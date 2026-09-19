#!/usr/bin/env python3
"""Check that each checked-in comparator challenge is freshly regenerated.

Every configuration under ``challenges/`` describes one challenge.  A challenge
whose expected file exists is regenerated in a temporary directory and byte
compared; a challenge whose expected file does not exist yet is skipped with a
message, unless its configuration sets ``require_expected``.
"""

from __future__ import annotations

import argparse
import difflib
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Sequence

from challenge_config import (
    ChallengeConfig,
    ChallengeConfigError,
    load_challenges,
)

# These belong to the scripts, not to the tree under `--root`: the checked tree
# may be a different worktree than the one this script was invoked from.
SCRIPT_DIR = Path(__file__).resolve().parent
EXTRACTOR = SCRIPT_DIR / "extract_closure.lean"
ASSEMBLER = SCRIPT_DIR / "assemble_challenge.py"

# A Lean module header cannot be computed at elaboration time, so the extractor
# is rendered per challenge with its own import block substituted.
IMPORT_BLOCK = re.compile(r"\A(?:[ \t]*\n)*(?:import[ \t]+\S+[^\n]*\n)+")


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


def render_extractor(challenge: ChallengeConfig, template: str) -> str:
    """The extractor source with this challenge's import block substituted."""
    body, substitutions = IMPORT_BLOCK.subn(
        lambda _: challenge.import_block(), template, count=1
    )
    if substitutions != 1:
        raise ChallengeConfigError(
            f"{EXTRACTOR} does not start with an import block; cannot render "
            f"challenge {challenge.name!r}"
        )
    return body


def challenge_part(root: Path, relative: str | None) -> bytes:
    """A header or footer file's bytes; empty when unconfigured or absent.

    A challenge under development is generated before its footer exists;
    `missing_challenge_inputs` reports what was left out.  Only `--write`
    generates such a challenge: `check_challenge` refuses to `--update` it, so
    a checked-in expected copy is never written with a part left out.
    """
    if relative is None:
        return b""
    path = root / relative
    return path.read_bytes() if path.exists() else b""


def assemble_candidate(root: Path, workdir: Path, challenge: ChallengeConfig) -> Path:
    raw_tsv = workdir / "closure.tsv"
    clean_tsv = workdir / "closure.clean.tsv"
    body = workdir / "draft.lean"
    candidate = workdir / "Challenge.lean"

    extractor = workdir / "extract_closure.lean"
    extractor.write_text(
        render_extractor(challenge, EXTRACTOR.read_text(encoding="utf-8")),
        encoding="utf-8",
    )

    env = dict(os.environ)
    env.update(challenge.extractor_env())
    run(["lake", "env", "lean", str(extractor)], cwd=root, stdout=raw_tsv, env=env)
    clean_closure_rows(raw_tsv, clean_tsv)
    body_text = run(
        [
            sys.executable,
            str(ASSEMBLER),
            str(clean_tsv),
            "--root",
            str(root),
            "--challenge",
            str(challenge.path),
        ],
        cwd=root,
    )
    body.write_text(body_text, encoding="utf-8")

    candidate.write_bytes(
        challenge_part(root, challenge.header)
        + body.read_bytes()
        + challenge_part(root, challenge.footer)
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
            tofile="regenerated Challenge.lean",
        )
    )


def missing_challenge_inputs(root: Path, challenge: ChallengeConfig) -> list[str]:
    """Header/footer files the configuration names but the tree does not have."""
    return [
        part
        for part in (challenge.header, challenge.footer)
        if part is not None and not (root / part).exists()
    ]


def check_challenge(
    root: Path, challenge: ChallengeConfig, *, update: bool, write: Path | None
) -> int:
    expected = root / challenge.expected

    if not (update or write) and not expected.exists():
        if challenge.require_expected:
            print(
                f"::error::challenge {challenge.name!r}: {challenge.expected} does "
                "not exist; run `python3 scripts/comparator/check_challenge_drift.py "
                f"--root . --challenge {challenge.name} --update`",
                file=sys.stderr,
            )
            return 1
        print(
            f"challenge {challenge.name!r}: no expected file yet "
            f"({challenge.expected}); skipping the drift check"
        )
        return 0

    absent = missing_challenge_inputs(root, challenge)
    if absent and update and write is None:
        # Writing the checked-in copy without a configured part would record a
        # challenge missing those statements; a `require_expected: false`
        # challenge would then stop being skipped and every later drift run
        # would report that hollow copy as current.
        print(
            f"::error::challenge {challenge.name!r}: refusing to update "
            f"{challenge.expected} without {', '.join(absent)} (not in this "
            "tree); the checked-in copy would omit that part of the "
            f"challenge.  Use `--challenge {challenge.name} --write PATH` "
            "while the challenge is still being developed.",
            file=sys.stderr,
        )
        return 1
    if absent:
        print(
            f"challenge {challenge.name!r}: assembling without "
            f"{', '.join(absent)} (not in this tree)",
            file=sys.stderr,
        )

    with tempfile.TemporaryDirectory(prefix=f"comparator-{challenge.name}-") as td:
        candidate = assemble_candidate(root, Path(td), challenge)
        candidate_bytes = candidate.read_bytes()

        if write is not None:
            write.parent.mkdir(parents=True, exist_ok=True)
            write.write_bytes(candidate_bytes)
            print(f"challenge {challenge.name!r}: wrote {write}")
            return 0

        if update:
            expected.parent.mkdir(parents=True, exist_ok=True)
            expected.write_bytes(candidate_bytes)
            print(f"challenge {challenge.name!r}: updated {challenge.expected}")
            return 0

        if expected.read_bytes() == candidate_bytes:
            print(f"challenge {challenge.name!r} is current: {challenge.expected}")
            return 0

        print(
            f"::error::Comparator challenge {challenge.name!r} regeneration drift "
            "detected.  Run `python3 scripts/comparator/check_challenge_drift.py "
            f"--root . --challenge {challenge.name} --update` and review the "
            "resulting diff.",
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
        action="append",
        metavar="NAME",
        help=(
            "challenge name under challenges/, or a path to a configuration "
            "file; repeatable (default: every configured challenge)"
        ),
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="rewrite the checked-in generated challenge copy",
    )
    parser.add_argument(
        "--write",
        type=Path,
        metavar="PATH",
        help="write the regenerated challenge to PATH instead of comparing; "
        "requires exactly one --challenge and leaves the expected copy alone",
    )
    args = parser.parse_args(argv)

    try:
        challenges = load_challenges(args.challenge)
    except ChallengeConfigError as exc:
        print(f"::error::{exc}", file=sys.stderr)
        return 1

    if args.write is not None and len(challenges) != 1:
        print(
            "::error::--write needs exactly one --challenge",
            file=sys.stderr,
        )
        return 1
    if not challenges:
        print("::error::no challenge configuration found", file=sys.stderr)
        return 1

    root = args.root.resolve()
    status = 0
    for challenge in challenges:
        status |= check_challenge(
            root, challenge, update=args.update, write=args.write
        )
    return status


if __name__ == "__main__":
    sys.exit(main())
