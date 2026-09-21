#!/usr/bin/env python3
"""Check that a checked-in comparator challenge is freshly regenerated."""

from __future__ import annotations

import argparse
import difflib
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from challenges import CHALLENGES, Challenge  # noqa: E402

EXTRACTOR = Path("scripts/comparator/extract_closure.lean")
ASSEMBLER = Path("scripts/comparator/assemble_challenge.py")


def run(
    cmd: Sequence[str],
    *,
    cwd: Path,
    stdout: Path | None = None,
    env: dict[str, str] | None = None,
) -> str:
    if stdout is None:
        completed = subprocess.run(
            cmd,
            cwd=cwd,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
        return completed.stdout

    with stdout.open("w", encoding="utf-8") as handle:
        subprocess.run(cmd, cwd=cwd, check=True, text=True, stdout=handle, env=env)
    return ""


def clean_closure_rows(raw_tsv: Path, clean_tsv: Path) -> None:
    rows = []
    for line in raw_tsv.read_text(encoding="utf-8").splitlines():
        if len(line.split("\t")) == 4:
            rows.append(line)
    clean_tsv.write_text("\n".join(rows) + ("\n" if rows else ""), encoding="utf-8")


def assemble_candidate(root: Path, workdir: Path, challenge: Challenge) -> Path:
    raw_tsv = workdir / "closure.tsv"
    clean_tsv = workdir / "closure.clean.tsv"
    body = workdir / "draft.lean"
    candidate = workdir / "Challenge.lean"

    env = dict(os.environ)
    env["COMPARATOR_TARGETS"] = challenge.target_env

    run(["lake", "env", "lean", str(EXTRACTOR)], cwd=root, stdout=raw_tsv, env=env)
    clean_closure_rows(raw_tsv, clean_tsv)
    body_text = run(
        [
            sys.executable,
            str(ASSEMBLER),
            str(clean_tsv),
            "--root",
            str(root),
            "--challenge",
            challenge.name,
        ],
        cwd=root,
    )
    body.write_text(body_text, encoding="utf-8")

    candidate.write_bytes(
        (root / challenge.header).read_bytes()
        + body.read_bytes()
        + (root / challenge.footer).read_bytes()
    )
    return candidate


def unified_diff(expected: Path, candidate: Path) -> str:
    expected_text = expected.read_text(encoding="utf-8", errors="replace").splitlines(True)
    candidate_text = candidate.read_text(encoding="utf-8", errors="replace").splitlines(True)
    return "".join(
        difflib.unified_diff(
            expected_text,
            candidate_text,
            fromfile=str(expected),
            tofile="regenerated challenge",
        )
    )


def compare_or_update(
    root: Path, challenge: Challenge, expected: Path, *, update: bool
) -> int:
    expected = root / expected
    with tempfile.TemporaryDirectory(prefix="comparator-challenge-") as td:
        candidate = assemble_candidate(root, Path(td), challenge)
        candidate_bytes = candidate.read_bytes()

        if update:
            expected.parent.mkdir(parents=True, exist_ok=True)
            expected.write_bytes(candidate_bytes)
            print(f"updated {expected.relative_to(root)}")
            return 0

        if not expected.exists():
            print(
                f"::error::{expected.relative_to(root)} does not exist; "
                "run `python3 scripts/comparator/check_challenge_drift.py --root . "
                f"--challenge {challenge.name} --update`",
                file=sys.stderr,
            )
            return 1

        if expected.read_bytes() == candidate_bytes:
            print(f"comparator challenge is current: {expected.relative_to(root)}")
            return 0

        print(
            "::error::Comparator challenge regeneration drift detected. "
            "Run `python3 scripts/comparator/check_challenge_drift.py --root . "
            f"--challenge {challenge.name} --update` and review the resulting diff.",
            file=sys.stderr,
        )
        print(unified_diff(expected, candidate), file=sys.stderr)
        return 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--challenge",
        choices=[*sorted(CHALLENGES), "all"],
        default="all",
        help="challenge to check (default: all)",
    )
    parser.add_argument(
        "--expected",
        type=Path,
        default=None,
        help="override the checked-in generated copy (needs a single --challenge)",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the checked-in generated challenge copy",
    )
    args = parser.parse_args(argv)

    names = sorted(CHALLENGES) if args.challenge == "all" else [args.challenge]
    if args.expected is not None and len(names) != 1:
        parser.error("--expected requires a single --challenge")

    root = args.root.resolve()
    status = 0
    for name in names:
        challenge = CHALLENGES[name]
        expected = args.expected if args.expected is not None else challenge.expected
        status |= compare_or_update(root, challenge, expected, update=args.update)
    return status


if __name__ == "__main__":
    sys.exit(main())
