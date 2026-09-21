#!/usr/bin/env python3
"""Regression tests for comparator challenge drift checking."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPARATOR = REPO_ROOT / "scripts" / "comparator"
SCRIPT = COMPARATOR / "check_challenge_drift.py"
PR_CI = REPO_ROOT / ".github" / "workflows" / "pr-ci.yml"
CI_SH = REPO_ROOT / "local" / "bin" / "ci.sh"
README = COMPARATOR / "README.md"
EXTRACTOR = COMPARATOR / "extract_closure.lean"

# the drift checker imports its sibling `challenge_config`, which a script run
# finds on `sys.path[0]` and a file-location import does not
if str(COMPARATOR) not in sys.path:
    sys.path.insert(0, str(COMPARATOR))

import challenge_config  # noqa: E402

_spec = importlib.util.spec_from_file_location("check_challenge_drift", SCRIPT)
assert _spec is not None and _spec.loader is not None
check_challenge_drift = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_challenge_drift)


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
        self.assertIn("--challenge", readme)
        self.assertIn("challenges/qpbt.json", readme)
        self.assertIn(
            "refuses a challenge whose configured header or footer file is not",
            readme,
        )
        self.assertIn("challenge_qpbt_footer.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/Soundness.lean", readme)
        self.assertIn("MIPStarRE/QPBT/Test/QubitForm.lean", readme)

    def test_machine_wide_guard_selects_every_configured_challenge(self) -> None:
        # `local/bin/ci.sh` passes no --challenge, so every configuration under
        # challenges/ is checked; a new challenge is picked up by adding its
        # file alone.
        configured = {path.stem for path in (COMPARATOR / "challenges").glob("*.json")}
        self.assertEqual(sorted(configured), ["ldt", "qpbt"])

        self.assertIn(
            "python3 scripts/comparator/check_challenge_drift.py --root .\n",
            CI_SH.read_text(encoding="utf-8"),
        )

    def test_pr_ci_names_only_configured_challenges(self) -> None:
        workflow = PR_CI.read_text(encoding="utf-8")
        for name in ("ldt", "qpbt"):
            self.assertIn(
                "python3 scripts/comparator/check_challenge_drift.py "
                f"--root . --challenge {name}",
                workflow,
            )

    def test_every_challenge_is_configured_completely(self) -> None:
        challenges = {
            challenge.name: challenge
            for challenge in challenge_config.load_challenges()
        }
        self.assertEqual(sorted(challenges), ["ldt", "qpbt"])
        for name, challenge in challenges.items():
            with self.subTest(challenge=name):
                self.assertTrue(challenge.targets)
                self.assertTrue(challenge.imports)
                for path in (challenge.header, challenge.footer, challenge.expected):
                    self.assertIsNotNone(path, f"{name}: unconfigured challenge part")
                    assert path is not None
                    self.assertTrue(
                        (REPO_ROOT / path).is_file(), f"{name}: missing {path}"
                    )

    def test_qpbt_targets_are_the_headline_theorems(self) -> None:
        qpbt = challenge_config.load_challenges(["qpbt"])[0]
        self.assertEqual(
            qpbt.targets,
            (
                "MIPStarRE.QPBT.pauli_soundness",
                "MIPStarRE.QPBT.pauli_soundness_qubit",
            ),
        )
        self.assertEqual(
            qpbt.expected, "scripts/comparator/expected/ChallengeQPBT.lean.expected"
        )
        assert qpbt.footer is not None
        footer = (REPO_ROOT / qpbt.footer).read_text(encoding="utf-8")
        for target in qpbt.targets:
            self.assertIn(target.rsplit(".", 1)[1], footer)

    def test_extractor_reads_targets_from_the_environment(self) -> None:
        extractor = EXTRACTOR.read_text(encoding="utf-8")
        self.assertIn(challenge_config.TARGETS_ENV, extractor)


if __name__ == "__main__":
    unittest.main()
