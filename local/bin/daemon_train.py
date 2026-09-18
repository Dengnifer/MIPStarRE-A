#!/usr/bin/env python3
"""Route one pinned, reviewed daemon batch to the existing train publisher.

The daemon supplies its complete candidate scan on stdin and a runtime JSON
batch. This adapter does not attest to review or CI: pr_train's member gates
recheck the current GitHub records and remain authoritative.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

import pr_merge
import pr_train
from pr_merge import GateFailure, git, git_ok
from wf_util import LayerError


SHA = re.compile(r"[0-9a-f]{40}\Z")
CANDIDATE = re.compile(
    r"(?P<pr>[1-9][0-9]*):[1-9][0-9]*:(?P<branch>[^:\s]+):[^:\s]*:"
    r"(?P<mode>clean|adj):(?P<head>[0-9a-f]{40})\Z"
)


def pinned_batch(path: Path) -> list[tuple[int, str]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or set(data) != {"members"} or not isinstance(data["members"], list):
        raise GateFailure("batch must be a JSON object with a members array")
    members = []
    for row in data["members"]:
        if (not isinstance(row, dict) or set(row) != {"number", "head"}
                or type(row["number"]) is not int or row["number"] <= 0
                or not isinstance(row["head"], str) or not SHA.fullmatch(row["head"])):
            raise GateFailure("batch member must pin a positive PR number and a full head SHA")
        members.append((row["number"], row["head"]))
    if len(members) < 2 or len({number for number, _ in members}) != len(members):
        raise GateFailure("batch requires at least two distinct PRs")
    return members


def select(repo: Path, batch: list[tuple[int, str]], scan: str) -> list[tuple[int, str]]:
    candidates = {}
    for line in scan.splitlines():
        match = CANDIDATE.fullmatch(line)
        if not match:
            raise GateFailure("malformed candidate scan; batch withheld")
        number = int(match["pr"])
        if number in candidates:
            raise GateFailure(f"duplicate candidate PR #{number}")
        candidates[number] = match
    for number, head in batch:
        row = candidates.get(number)
        if row is None or row["mode"] != "clean" or row["head"] != head:
            raise GateFailure(f"PR #{number} is not scanned clean at its pinned head")
        # Fresh candidates stay on the daemon's ordinary single-PR path.
        if pr_merge.head_is_fresh(repo, "github/main", head):
            raise GateFailure(f"PR #{number} is fresh; use the ordinary path")
        code, holder = pr_train.claim_call(repo, "check", str(number))
        if code == 3:
            raise GateFailure(f"PR #{number} has an active claim: {holder}")
        if code != 0:
            raise LayerError(f"claim check for PR #{number} failed ({code}): {holder}")
    return batch


def unpublished_history_is_telemetry(repo: Path, remote: str, local: str) -> bool:
    """Check each unpublished commit, including changes hidden by later reversals."""
    for sha in git(repo, "rev-list", "--reverse", f"{remote}..{local}").splitlines():
        commit, *parents = git(repo, "rev-list", "--parents", "-n", "1", sha).split()
        if commit != sha or not parents:
            return False
        if any(not pr_merge._base_advance_is_tolerated(repo, parent, sha) for parent in parents):
            return False
    return True


def prepare_primary(repo: Path) -> None:
    """Retain daemon telemetry and any unpublished telemetry-only main commits."""
    common = Path(git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir"))
    if common != repo / ".git" or git(repo, "symbolic-ref", "--short", "HEAD") != "main":
        raise GateFailure("train preparation requires the primary checkout on main")
    if git(repo, "status", "--porcelain", "--", ".", ":!results/telemetry"):
        raise GateFailure("primary has changes outside telemetry; no train preparation")
    if git(repo, "status", "--porcelain", "--", "results/telemetry"):
        git(repo, "add", "--", "results/telemetry")
        git(repo, "commit", "-m", "chore(telemetry): records before reviewed train",
            "--", "results/telemetry")
    git(repo, "fetch", "--no-tags", "github", "main")
    remote, local = git(repo, "rev-parse", "github/main"), git(repo, "rev-parse", "main")
    if remote != local:
        if (not git_ok(repo, "merge-base", "--is-ancestor", remote, local)
                or not unpublished_history_is_telemetry(repo, remote, local)):
            raise GateFailure("local main is not a telemetry-only descendant of published main")
        result = subprocess.run([str(repo / "local/bin/github-sync.sh"), "main"], cwd=repo)
        if result.returncode:
            raise LayerError(f"telemetry sync failed ({result.returncode}); train not started")
    # The sync may create and publish a record snapshot. Re-read the tip and
    # enforce the train's exact primary/remote cleanliness precondition.
    git(repo, "fetch", "--no-tags", "github", "main")
    pr_train.primary_at(repo, git(repo, "rev-parse", "github/main"))


def run(repo: Path, batch_file: Path, scan: str) -> int:
    members = select(repo, pinned_batch(batch_file), scan)
    prepare_primary(repo)
    pins = [arg for number, head in members for arg in ("--pinned-head", str(number), head)]
    result = subprocess.run([sys.executable, str(repo / "local/bin/pr_train.py"),
                             "--repo-root", str(repo), *pins,
                             *(str(number) for number, _ in members)], cwd=repo)
    if result.returncode:
        print(f"daemon train refused or incomplete (exit {result.returncode}); "
              "inspect train publication evidence before any retry", file=sys.stderr)
        return 1
    print("daemon train completed; check the published manifest for actual accepted members")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--batch-file", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        return run(args.repo_root.resolve(), args.batch_file, sys.stdin.read())
    except (LayerError, OSError, ValueError, KeyError) as exc:
        print(f"daemon train REFUSED: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
