#!/usr/bin/env python3
"""Regression tests for comparator challenge drift checking."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "comparator" / "check_challenge_drift.py"
PR_CI = REPO_ROOT / ".github" / "workflows" / "pr-ci.yml"
README = REPO_ROOT / "scripts" / "comparator" / "README.md"

CHALLENGES_SCRIPT = REPO_ROOT / "scripts" / "comparator" / "challenges.py"
EXTRACTOR = REPO_ROOT / "scripts" / "comparator" / "extract_closure.lean"

_spec = importlib.util.spec_from_file_location("check_challenge_drift", SCRIPT)
assert _spec is not None and _spec.loader is not None
check_challenge_drift = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_challenge_drift)

_cspec = importlib.util.spec_from_file_location("challenges", CHALLENGES_SCRIPT)
assert _cspec is not None and _cspec.loader is not None
challenges = importlib.util.module_from_spec(_cspec)
_cspec.loader.exec_module(challenges)


class ComparatorChallengeDriftTests(unittest.TestCase):
    def test_clean_closure_rows_keeps_only_four_column_tsv_rows(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            raw = root / "closure.tsv"
            clean = root / "closure.clean.tsv"
            raw.write_text(
                "\n".join(
                    [
                        "noise from an unexpected diagnostic",
                        "Decl\tMIPStarRE/Foo.lean\t1\t2",
                        "too\tmany\tcolumns\tfor\tthis\trow",
                        "Generated\tMIPStarRE/Bar.lean\tNORANGE\tNORANGE",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )

            check_challenge_drift.clean_closure_rows(raw, clean)

            self.assertEqual(
                clean.read_text(encoding="utf-8"),
                "Decl\tMIPStarRE/Foo.lean\t1\t2\n"
                "Generated\tMIPStarRE/Bar.lean\tNORANGE\tNORANGE\n",
            )

    def test_pr_ci_runs_drift_guard_after_lean_build_for_comparator_changes(self) -> None:
        workflow = PR_CI.read_text(encoding="utf-8")
        self.assertIn("comparator: ${{ steps.filter.outputs.comparator }}", workflow)
        self.assertIn("- 'scripts/comparator/**'", workflow)
        self.assertIn("needs.changes.outputs.comparator == 'true'", workflow)
        build = workflow.index("lake build MIPStarRE.LDT.Test.AxiomAudit")
        guard = workflow.index("python3 scripts/comparator/check_challenge_drift.py --root .")
        self.assertLess(build, guard)

    def test_readme_documents_update_command_and_footer_source(self) -> None:
        readme = README.read_text(encoding="utf-8")
        self.assertIn("python3 scripts/comparator/check_challenge_drift.py --root . --update", readme)
        self.assertIn("challenge_footer.lean", readme)
        self.assertIn("MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean", readme)
        self.assertIn("challenge_qpbt_footer.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/Soundness.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/QubitForm.lean", readme)

    def test_every_challenge_is_configured_completely(self) -> None:
        self.assertEqual(sorted(challenges.CHALLENGES), ["ldt", "qpbt"])
        for name, challenge in challenges.CHALLENGES.items():
            with self.subTest(challenge=name):
                self.assertEqual(challenge.name, name)
                self.assertTrue(challenge.targets)
                for path in (challenge.header, challenge.footer):
                    self.assertTrue(
                        (REPO_ROOT / path).is_file(), f"{name}: missing {path}"
                    )
                expected = REPO_ROOT / challenge.expected
                if challenge.split:
                    # one generated module per contributing library module
                    self.assertTrue(
                        expected.is_dir(),
                        f"{name}: missing directory {challenge.expected}",
                    )
                    self.assertTrue(
                        (expected / "Challenge.lean").is_file(),
                        f"{name}: {challenge.expected} has no root module",
                    )
                    self.assertTrue(
                        any(expected.rglob("Challenge/**/*.lean")),
                        f"{name}: {challenge.expected} has no mirror modules",
                    )
                else:
                    self.assertTrue(
                        expected.is_file(), f"{name}: missing {challenge.expected}"
                    )
                self.assertEqual(
                    challenge.target_env, " ".join(challenge.targets)
                )

    def test_qpbt_targets_are_the_headline_theorems(self) -> None:
        qpbt = challenges.CHALLENGES["qpbt"]
        self.assertEqual(
            qpbt.targets,
            (
                "MIPStarRE.QPBT.pauli_soundness",
                "MIPStarRE.QPBT.pauli_soundness_qubit",
            ),
        )
        footer = (REPO_ROOT / qpbt.footer).read_text(encoding="utf-8")
        for target in qpbt.targets:
            self.assertIn(target.rsplit(".", 1)[1], footer)

    def test_qpbt_challenge_is_split_and_mathlib_only(self) -> None:
        qpbt = challenges.CHALLENGES["qpbt"]
        self.assertTrue(
            qpbt.split,
            "the QPBT challenge must mirror the library module partition: a "
            "single module cannot reproduce Lean's per-module auxiliary names",
        )
        expected = REPO_ROOT / qpbt.expected
        parts = sorted(expected.rglob("Challenge/**/*.lean"))
        self.assertTrue(parts)
        allowed_prefixes = ("import Mathlib", "import Challenge")
        for part in [expected / "Challenge.lean", *parts]:
            with self.subTest(module=part.name):
                imports = []
                for line in part.read_text(encoding="utf-8").splitlines():
                    # imports are only legal in the leading block of a module
                    if line.startswith("import "):
                        imports.append(line)
                    elif line.strip():
                        break
                self.assertTrue(imports, f"{part} has no imports")
                for line in imports:
                    self.assertTrue(
                        line.startswith(allowed_prefixes),
                        f"{part}: challenge modules may only import Mathlib and "
                        f"other challenge modules, found {line!r}",
                    )

    def test_extractor_reads_targets_from_the_environment(self) -> None:
        extractor = EXTRACTOR.read_text(encoding="utf-8")
        self.assertIn("COMPARATOR_TARGETS", extractor)
        for challenge in challenges.CHALLENGES.values():
            module_prefix = challenge.targets[0].rsplit(".", 1)[0]
            with self.subTest(challenge=challenge.name):
                self.assertIn(module_prefix.split(".")[1], extractor)

    def test_pr_ci_runs_one_drift_step_per_challenge(self) -> None:
        workflow = PR_CI.read_text(encoding="utf-8")
        for name in challenges.CHALLENGES:
            self.assertIn(
                "python3 scripts/comparator/check_challenge_drift.py "
                f"--root . --challenge {name}",
                workflow,
            )


if __name__ == "__main__":
    unittest.main()
