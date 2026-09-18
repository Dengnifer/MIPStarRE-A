#!/usr/bin/env python3
"""Integrate independently reviewed PR heads, check the result, and publish it.

Operator-only after deployment. Development and tests must use fixture repos.
Member evidence remains attached to its original SHA; combined CI is additional
evidence and never manufactures an independent review of the integration head.
"""

from __future__ import annotations

import argparse
from contextlib import ExitStack, contextmanager
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import gh_common
import pr_merge
import telemetry
from pr_merge import GateFailure, git, git_ok
from wf_util import LayerError, atomic_write, cache_root, file_lock, utcnow


CLAIM_PARTY, CLAIM_KIND = "main", "train"
SHA = re.compile(r"[0-9a-f]{40}\Z")


def claim_script(repo: Path) -> Path:
    """The shared atomic claim list every writer in this project uses."""
    local = repo / "local/bin/claim.sh"
    return local if local.exists() else Path.home() / ".cache/mipstarre-dev/owner-bin/qpbt-claim.sh"


def claim_call(repo: Path, *args: str) -> tuple[int, str]:
    result = subprocess.run(["bash", str(claim_script(repo)), *args], cwd=repo,
                            text=True, capture_output=True)
    return result.returncode, (result.stdout + result.stderr).strip()


@contextmanager
def member_claims(repo: Path, numbers: list[int]):
    """Hold the shared claim on every member for the whole gating and transport.

    A claim adds no predicate to the remote transaction. It keeps this project's
    own writers off the member PRs while the train verifies and publishes, which
    is what makes the residual advertisement-to-commit window of the authorized
    publication contract safe in practice (see `issues-prs.md`). A member held by
    another writer refuses the train before it starts, naming the holder.
    """
    held, receipt = [], {"note": "train ended before publication"}
    try:
        for number in sorted(numbers):
            code, output = claim_call(repo, "claim", CLAIM_PARTY, CLAIM_KIND, str(number),
                                      "reviewed merge train")
            if code == 3:
                raise GateFailure(f"PR #{number} is claimed by another writer: {output}")
            if code:
                raise LayerError(f"claim of PR #{number} failed ({code}): {output}")
            held.append(number)
        yield receipt
    finally:
        for number in held:
            code, output = claim_call(repo, "release", CLAIM_PARTY, CLAIM_KIND, str(number),
                                      receipt["note"])
            if code:
                print(f"claim release of PR #{number} failed ({code}): {output}", file=sys.stderr)


def command(repo: Path, *args: str, env: dict | None = None) -> None:
    result = subprocess.run(args, cwd=repo, check=False, env=env)
    if result.returncode:
        raise LayerError(f"step {args[0]} failed ({result.returncode})")


def primary_at(repo: Path, base: str) -> None:
    common = Path(git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir"))
    if common != repo / ".git":
        raise GateFailure("train requires the primary checkout")
    if git(repo, "symbolic-ref", "--short", "HEAD") != "main":
        raise GateFailure("primary checkout must be on main")
    if git(repo, "status", "--porcelain") or git(repo, "rev-parse", "HEAD") != base:
        raise GateFailure("primary checkout is dirty or main changed")
    if git(repo, "ls-remote", "github", "refs/heads/main").split() != [base, "refs/heads/main"]:
        raise GateFailure("remote main changed")


def members_at(repo: Path, numbers: list[int], base: str, adjudicated: set[int],
               titles: dict[int, str] | None = None,
               expected_heads: dict[int, str] | None = None) -> list[dict]:
    members, failures = [], []
    for number in numbers:
        try:
            row = pr_merge.run_gate(repo, number, adjudicated=number in adjudicated,
                                    integration_base=base)
            if expected_heads is not None and row["head_sha"] != expected_heads[number]:
                raise GateFailure(f"requested pin {expected_heads[number]} changed to "
                                  f"{row['head_sha']}")
            members.append({"number": number, "head": row["head_sha"],
                            "branch": row["branch"], "adjudicated": number in adjudicated})
            if titles is not None:
                titles[number] = str(row["pr"].get("title") or row["branch"])
        except LayerError as exc:
            failures.append(f"PR #{number}: {exc}")
    if failures:
        raise GateFailure("train preconditions failed:\n" + "\n".join(failures))
    return members


def integrate(repo: Path, worktree: Path, members: list[dict],
              titles: dict[int, str]) -> tuple[list[dict], list[int]]:
    accepted, dropped = [], []
    for member in members:
        head, number = member["head"], member["number"]
        before = git(worktree, "rev-parse", "HEAD")
        if git_ok(worktree, "merge-base", "--is-ancestor", head, before):
            raise GateFailure(f"PR #{number} is already contained in the train")
        result = subprocess.run(
            ["git", "merge", "--no-ff", "--no-commit", head], cwd=worktree,
            text=True, capture_output=True)
        if result.returncode:
            if not git(worktree, "diff", "--name-only", "--diff-filter=U"):
                raise LayerError(f"PR #{number}: merge failed: {result.stderr}")
            git(worktree, "merge", "--abort")
            if git(worktree, "rev-parse", "HEAD") != before or git(worktree, "status", "--porcelain"):
                raise GateFailure(f"PR #{number}: conflict abort did not restore the accepted train")
            dropped.append(number)
            print(f"dropped PR #{number}: merge conflict", flush=True)
            continue
        command(worktree, sys.executable, str(repo / "local/bin/merge_loss_guard.py"),
                "--repo", str(worktree))
        git(worktree, "commit", "-m", f"Merge PR #{number} into reviewed train")
        # The merge commit's tree includes any resolution; its first parent is the
        # immediately preceding accepted train state, even after a dropped member.
        delta = pr_merge.lean_line_delta(worktree, before, git(worktree, "rev-parse", "HEAD"))
        title = pr_merge.merge_commit_title(number, titles[number], delta)
        if title is not None:
            git(worktree, "commit", "--amend", "-m", title)
        parents = git(worktree, "rev-list", "--parents", "-n", "1", "HEAD").split()[1:]
        if parents != [before, head]:
            raise GateFailure(f"PR #{number}: unexpected merge topology")
        accepted.append(member)
    return accepted, dropped


def ci_path(head: str) -> Path:
    return cache_root() / "ci-manifests" / f"prtrain-{head}-{head}.partial.json"


def check_combined_ci(data: dict) -> None:
    manifest = json.loads(ci_path(data["head"]).read_text(encoding="utf-8"))
    expected = {step: "success" for step in pr_merge.CI_STEPS}
    outcomes = {row["step"]: row["outcome"] for row in manifest["steps"]}
    if (manifest["head_sha"] != data["head"] or manifest["merge_base"] != data["base"]
            or manifest["worktree"] != data["worktree"] or manifest["conclusion"] != "success"
            or outcomes != expected or len(manifest["steps"]) != len(expected)):
        raise GateFailure(f"combined CI did not pass every step: {outcomes}")


def verify_manifest(path: Path, expected_main: str, expected_head: str,
                    expected_ref: str) -> list[dict]:
    """Recheck after checked-push's expensive preflight, before transport opens.

    Returns the verified members so the caller can lease their refs inside the
    publishing transport. A lease is compared against the remote's ref
    advertisement, so it catches a member that moved before the transport
    started; a member that still matches sends no update command and the remote
    therefore holds no predicate for it while it commits. Under the contract
    authorized on 2026-09-18 that residual window is covered by the member
    claims and detected afterwards by `moved_members` (see `issues-prs.md`).
    """
    data = json.loads(path.read_text(encoding="utf-8"))
    repo, worktree = Path(data["repo"]), Path(data["worktree"])
    if (expected_main != data["base"] or expected_head != data["head"]
            or expected_ref != "refs/heads/main"):
        raise GateFailure("publication tuple differs from the tested train")
    if len(data["members"]) < 2:
        raise GateFailure("fewer than two train members")
    expected_heads = None
    if "requested_heads" in data:
        requested = data["requested_heads"]
        if not isinstance(requested, dict) or any(
                not isinstance(number, str) or not number.isdecimal()
                or not isinstance(head, str) or not SHA.fullmatch(head)
                for number, head in requested.items()):
            raise GateFailure("invalid requested head pins in train manifest")
        expected_heads = {int(number): head for number, head in requested.items()}
        if (len(expected_heads) != len(requested)
                or set(expected_heads) != {m["number"] for m in data["members"]} | set(data["dropped"])):
            raise GateFailure("requested head pins do not match train members and drops")
    primary_at(repo, data["base"])
    current = members_at(repo, [m["number"] for m in data["members"]], data["base"],
                         {m["number"] for m in data["members"] if m["adjudicated"]},
                         expected_heads=expected_heads)
    if current != data["members"]:
        raise GateFailure("a train member head or branch changed")
    if expected_heads is not None and data["dropped"]:
        members_at(repo, data["dropped"], data["base"], set(), expected_heads=expected_heads)
    if git(worktree, "rev-parse", "HEAD") != data["head"] or git(worktree, "status", "--porcelain"):
        raise GateFailure("tested train changed")
    for member in current:
        if not git_ok(worktree, "merge-base", "--is-ancestor", member["head"], data["head"]):
            raise GateFailure(f"PR #{member['number']} is missing from the train")
    check_combined_ci(data)
    refs = {f"refs/heads/{m['branch']}": m["head"] for m in current}
    refs["refs/heads/main"] = data["base"]
    advertised = {ref: sha for sha, ref in
                  (line.split() for line in git(repo, "ls-remote", "github", *refs).splitlines())}
    if advertised != refs:
        raise GateFailure("remote main or member refs changed")
    primary_at(repo, data["base"])
    return current


def moved_members(repo: Path, members: list[dict]) -> list[dict]:
    """Re-read every member ref from the remote once the transport committed.

    This cannot prevent a member from advancing inside the residual window; it
    detects it afterwards. A member that moved is a CONTRACT VIOLATION: main
    still carries only verified content, but this train did not merge that PR,
    so nothing here may mark it merged.
    """
    refs = {f"refs/heads/{member['branch']}": member for member in members}
    observed = {ref: sha for sha, ref in
                (line.split() for line in git(repo, "ls-remote", "github", *refs).splitlines())}
    violations = []
    for ref, member in refs.items():
        if observed.get(ref) == member["head"]:
            continue
        code, holders = claim_call(repo, "check", str(member["number"]))
        violations.append({"number": member["number"], "ref": ref, "verified": member["head"],
                           "observed": observed.get(ref, "absent"),
                           "claims": holders if code == 3 else "none"})
    return violations


def run_ci(repo: Path, data: dict) -> None:
    worktree = Path(data["worktree"])
    env = dict(os.environ, MIPSTARRE_TELEMETRY_DIR=str(worktree.parent / "telemetry"))
    # Bootstrap with trusted primary scripts; --no-build prevents a second full build.
    command(repo, str(repo / "local/bin/worktree-setup.sh"), str(worktree), "--no-build", env=env)
    try:
        command(repo, str(repo / "local/bin/ci.sh"), "--integration-head", data["head"],
                "--worktree", str(worktree), "--base", data["base"], env=env)
    except LayerError:
        if ci_path(data["head"]).exists():
            check_combined_ci(data)
        raise
    check_combined_ci(data)


def publication_outcome(repo: Path, head: str) -> str:
    """Reconcile an ambiguous push without retrying it or assuming a failed read is absence."""
    try:
        rows = git(repo, "ls-remote", "github", "refs/heads/main").split()
        if len(rows) != 2 or rows[1] != "refs/heads/main":
            return "unknown"
        remote = rows[0]
        if remote == head:
            return "published"
        git(repo, "fetch", "--no-tags", "github", remote)
        result = subprocess.run(["git", "merge-base", "--is-ancestor", head, remote], cwd=repo)
        if result.returncode == 0:
            return "published"
        if result.returncode == 1 and git(repo, "rev-parse", "--is-shallow-repository") == "false":
            return "refused"
    except (LayerError, OSError, ValueError) as exc:
        print(f"publication reconciliation failed: {exc}", file=sys.stderr)
    return "unknown"


def record(repo: Path, data: dict, outcome: str) -> None:
    """Retain publication state and transfer build telemetry only after gating ends."""
    violations = data.get("violations", [])
    atomic_write(Path(data["worktree"]).parent / "publication.json",
                 json.dumps({"head": data["head"], "outcome": outcome, "ts": utcnow(),
                             "violations": violations}) + "\n")
    # The train lock only serialises trains; both files are written through the
    # canonical telemetry writers, whose own locking is what other sessions obey.
    with file_lock("train-telemetry"):
        directory = repo / "results/telemetry"
        directory.mkdir(parents=True, exist_ok=True)
        spools = [cache_root() / "ci-manifests" / f"train-{data['head']}.builds.jsonl",
                  Path(data["worktree"]).parent / "telemetry/builds.jsonl"]
        for spool in spools:
            if not spool.exists():
                continue
            try:
                rows = [json.loads(line) for line
                        in spool.read_text(encoding="utf-8").splitlines() if line.strip()]
            except ValueError as exc:
                # Keep the spool for the operator rather than losing the evidence.
                print(f"build telemetry spool {spool} is not JSONL: {exc}", file=sys.stderr)
                continue
            for row in rows:
                telemetry.append_jsonl(directory / "builds.jsonl", row)
            spool.unlink()
        members = ", ".join(f"#{m['number']}@{m['head']}" for m in data["members"])
        moved = ", ".join(f"#{row['number']} {row['verified']} -> {row['observed']}"
                          for row in violations)
        telemetry.append_event_bullet(
            directory / "events.md",
            f"{utcnow()} - Reviewed train {data['head']}: publication {outcome}; "
            f"members {members}; conflicting PRs dropped: {data['dropped']}"
            + (f"; CONTRACT VIOLATION, member refs moved during publication: {moved}."
               if moved else "."),
            datetime.now().astimezone().strftime("%Y-%m-%d"))


def run_train(repo: Path, numbers: list[int], adjudicated: set[int],
              expected_heads: dict[int, str] | None = None) -> int:
    if len(numbers) < 2 or len(set(numbers)) != len(numbers) or any(n <= 0 for n in numbers):
        raise GateFailure("provide at least two distinct positive PR numbers")
    if not adjudicated.issubset(numbers):
        raise GateFailure("--adjudicated must name a train member")
    if expected_heads is not None and (set(expected_heads) != set(numbers) or any(
            not isinstance(head, str) or not SHA.fullmatch(head)
            for head in expected_heads.values())):
        raise GateFailure("pinned heads must name every train member with a full SHA")
    if os.environ.get("MIPSTARRE_SKIP_HOOKS") == "1":
        raise GateFailure("a train cannot bypass hooks")
    with ExitStack() as stack:
        stack.enter_context(file_lock("pr-train"))
        for number in sorted(numbers):
            stack.enter_context(file_lock(f"pr-{number}"))
        # Claim every member on the shared list before the first gate reads it,
        # and keep the claims until the transport and its re-verification end.
        receipt = stack.enter_context(member_claims(repo, numbers))
        git(repo, "fetch", "github", "main")
        base = git(repo, "rev-parse", "github/main")
        primary_at(repo, base)
        titles: dict[int, str] = {}
        members = members_at(repo, numbers, base, adjudicated, titles, expected_heads)
        runtime = cache_root() / "trains"
        runtime.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="train-", dir=runtime))
        worktree = directory / "worktree"
        branch = "train-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
        git(repo, "worktree", "add", "-b", branch, str(worktree), base)
        print(f"train worktree: {worktree}", flush=True)
        data, outcome = None, "refused"
        try:
            members, dropped = integrate(repo, worktree, members, titles)
            if len(members) < 2:
                raise GateFailure(f"fewer than two members remain; conflicts: {dropped}")
            data = {"repo": str(repo), "worktree": str(worktree), "base": base,
                    "head": git(worktree, "rev-parse", "HEAD"), "members": members,
                    "dropped": dropped}
            if expected_heads is not None:
                data["requested_heads"] = {str(n): expected_heads[n] for n in numbers}
            path = directory / "manifest.json"
            atomic_write(path, json.dumps(data, indent=2) + "\n")
            run_ci(repo, data)
            verify_manifest(path, base, data["head"], "refs/heads/main")
            outcome = "unknown"
            try:
                command(repo, str(repo / "local/bin/checked-push.sh"), "--repo-root", str(repo),
                        "--train-manifest", str(path), "github", f"refs/heads/{branch}:refs/heads/main")
            except (LayerError, OSError):
                outcome = publication_outcome(repo, data["head"])
                raise
            outcome = "published"
            print(f"published train {data['head']}", flush=True)
            violations = moved_members(repo, members)
            data["violations"] = violations
            for row in violations:
                print(f"CONTRACT VIOLATION: PR #{row['number']} {row['ref']} was verified at "
                      f"{row['verified']} and is now {row['observed']}; claim list: "
                      f"{row['claims']}", flush=True)
            moved = {row["number"] for row in violations}
            # Preserve existing developer branches/worktrees, including conflicting members.
            git(repo, "fetch", "github", "main")
            if not pr_merge.fast_forward_base(repo, "main"):
                raise LayerError("train published; local main requires operator reconciliation")
            pr_merge.update_origin_alias(repo, "main")
            errors = []
            for member in members:
                if member["number"] in moved:
                    continue  # this train did not merge that PR; never say it did
                try:
                    gh_common.ensure_pr_comment(
                        member["number"], f"mipstarre-train head={data['head']}",
                        f"Merged in reviewed train `{data['head']}`; member head `{member['head']}`.")
                except LayerError as exc:
                    errors.append(str(exc))
            git(repo, "worktree", "remove", "--force", str(worktree))
            if os.environ.get("MIPSTARRE_LAKE_ROOT"):
                command(repo, str(repo / "local/bin/lake-root.sh"), "cleanup", str(repo), branch)
            git(repo, "branch", "-d", branch)
            failures = []
            if violations:
                failures.append("CONTRACT VIOLATION: member refs moved during publication: "
                                + ", ".join(f"#{row['number']} {row['verified']} -> "
                                            f"{row['observed']}" for row in violations))
            if errors:
                failures.append("comment publication incomplete: " + "; ".join(errors))
            if failures:
                raise LayerError("train published; " + "; ".join(failures))
            return 0
        except (LayerError, OSError, ValueError) as exc:
            print(f"train publication {outcome}; evidence: {directory}", file=sys.stderr)
            raise LayerError(str(exc)) from exc
        finally:
            if data is not None:
                receipt["note"] = (f"train {data['head']} {outcome}"
                                   + ("; CONTRACT VIOLATION" if data.get("violations") else ""))
                record(repo, data, outcome)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prs", type=int, nargs="*")
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--adjudicated", type=int, action="append", default=[])
    parser.add_argument("--pinned-head", nargs=2, action="append", metavar=("PR", "SHA"))
    parser.add_argument("--verify-manifest", type=Path)
    parser.add_argument("--expected-main", default="")
    parser.add_argument("--expected-head", default="")
    parser.add_argument("--expected-ref", default="")
    parser.add_argument("--members-out", type=Path)
    args = parser.parse_args()
    try:
        if args.verify_manifest:
            members = verify_manifest(args.verify_manifest, args.expected_main,
                                      args.expected_head, args.expected_ref)
            if args.members_out:
                # A file, not stdout: the gate reports share stdout with this run.
                atomic_write(args.members_out, "".join(
                    f"refs/heads/{member['branch']} {member['head']}\n" for member in members))
            return 0
        expected_heads = None
        if args.pinned_head:
            expected_heads = {}
            for number, head in args.pinned_head:
                if not number.isdecimal() or int(number) <= 0 or int(number) in expected_heads:
                    raise GateFailure("duplicate or invalid pinned PR number")
                expected_heads[int(number)] = head
        return run_train(args.repo_root.resolve(), args.prs, set(args.adjudicated), expected_heads)
    except (LayerError, OSError, ValueError, KeyError) as exc:
        print(f"pr_train.py: ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
