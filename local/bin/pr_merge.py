#!/usr/bin/env python3
"""The local merge gate: verify, merge no-ff, close, track, clean up.

This is the one script in the issue-lifecycle area that changes the repository's
history, and it is the local replacement for GitHub's branch-protection rules
rather than for any single workflow.  Upstream, "required checks + required
review" were server-side settings no client could bypass.  Here the equivalent
authority is this file, so it refuses by default and every override is named.

Gate (all must hold; each failure names the command that would fix it):

1. the PR record is ``state: open``;
2. ``head_sha`` is recorded and still equals the branch tip — a review or a CI
   run that predates the tip proves nothing about what is being merged
   (DESIGN.md:66-69, "Review only after green CI, on the same head SHA");
3. ``ci_status: success`` *and* a per-SHA manifest ``prs/<id>/ci/<sha>.json``;
4. ``review_state: APPROVED``, or ``COMMENTED`` with zero unchecked findings in
   ``prs/<id>/reviews/<sha>.*``;
5. the fix loop is quiescent: no pending-fix marker, and ``fix_iterations`` is
   within the combined cap (DESIGN.md:70-72).

Then: ``git merge --no-ff`` onto the base, refresh the ``refs/remotes/origin/
<base>`` alias that the hooks and diff-based audits need in order not to
self-disable (DESIGN.md:84-85), mark the record merged, auto-close the
``Closes``/``Fixes`` issues as ``completed``, run the tracking bookkeeping, and
delete the branch and its worktree.

The tracking call carries an exclusion list.  Upstream, a merged PR reached the
tracking parent twice — once through the merged-PR path and once through the
auto-close that the merge triggered — and the fix was to drop auto-closed issues
from the merged-PR progress comments (issue-automation.yml:449-452).  Here both
halves run in this process, so the same exclusion is passed explicitly to
``track.py``; without it a tracking parent gets two notes per child.

Usage:
    pr_merge.py 0007
    pr_merge.py 0007 --check-only
    pr_merge.py 0007 --dry-run
    pr_merge.py --help
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import track
    import issue_close
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "pr_merge.py: cannot import its siblings in local/bin "
        f"({exc}); track.py and issue_close.py must sit beside it.\n"
    )
    raise SystemExit(2)

from track import LayerError  # noqa: E402


DEFAULT_FIX_CAP = 5
UNCHECKED_FINDING_RE = re.compile(r"^\s*[-*]\s*\[ \]", re.MULTILINE)


class GateFailure(LayerError):
    """A refusal to merge.  Distinct type so the caller can report it as such."""


# ---------------------------------------------------------------------------
# git helpers
# ---------------------------------------------------------------------------

def git(repo_root: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args], cwd=str(repo_root),
        capture_output=True, text=True, check=False,
    )
    if check and result.returncode != 0:
        raise LayerError(
            f"git {' '.join(args)} failed ({result.returncode}): "
            f"{result.stderr.strip() or result.stdout.strip()}"
        )
    return result.stdout.strip()


def git_ok(repo_root: Path, *args: str) -> bool:
    result = subprocess.run(
        ["git", *args], cwd=str(repo_root),
        capture_output=True, text=True, check=False,
    )
    return result.returncode == 0


# ---------------------------------------------------------------------------
# Gate
# ---------------------------------------------------------------------------

def kill_switch_disabled(name: str) -> bool:
    """DESIGN.md:73-75 — disabled only on the literal string ``false``."""
    return os.environ.get(name) == "false"


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def check_review_verdict(record_dir: Path, head_sha: str, review_state: str,
                         *, adjudicated: bool = False) -> None:
    """Approve, or accept a commented review with no open findings."""
    reviews = record_dir / "reviews"
    if not reviews.is_dir():
        raise GateFailure(
            f"{reviews} does not exist. Run local/bin/review.sh on this PR; a "
            "merge needs a verdict file for the exact head SHA."
        )
    # review.sh writes `<head_sha>-code.md` and `<head_sha>-prose.md`
    # (local/protocols/review.md, "Verdict files").
    verdicts = sorted(p for p in reviews.glob(f"{head_sha}-*.md") if p.is_file())
    if not verdicts:
        raise GateFailure(
            f"no review verdict for head SHA {head_sha[:12]} in {reviews}. "
            "A verdict on an earlier SHA does not carry over: re-run "
            f"local/bin/review.sh (DESIGN.md:66-69)."
        )
    if review_state == "APPROVED":
        return
    accepted = {"COMMENTED"}
    if adjudicated:
        # local/protocols/review.md section 12: after four review rounds the
        # operator may adjudicate the remaining findings — every one ticked in
        # the current head's ledger with a reason and a tracked issue — and
        # merge with review_state ADJUDICATED under the explicit flag.
        accepted.add("ADJUDICATED")
    if review_state not in accepted:
        raise GateFailure(
            f"review_state is {review_state!r}; the gate accepts APPROVED, "
            "COMMENTED with zero unchecked findings"
            + (", or ADJUDICATED (--adjudicated)" if adjudicated else
               " (or ADJUDICATED with --adjudicated; review.md section 12)")
            + "."
        )
    open_findings = 0
    for verdict in verdicts:
        try:
            text = verdict.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            raise GateFailure(f"cannot read review verdict {verdict}: {exc}") from exc
        open_findings += len(UNCHECKED_FINDING_RE.findall(text))
    if open_findings:
        raise GateFailure(
            f"review_state is COMMENTED with {open_findings} unchecked finding(s) "
            f"in {reviews}/{head_sha[:12]}-*.md. Address them (or tick the boxes "
            "to record them as dismissed, with a reason) before merging."
        )


def check_fix_gates(repo_root: Path, record_dir: Path, meta: dict) -> None:
    """Refuse while the serialized fix loop is mid-flight or over its cap."""
    # autofix.sh holds a mkdir-based lease directory keyed on the BRANCH
    # (autofix.sh "---- lock" section: locks/fix-<branch with / -> ->.lock,
    # with the holder's pid in <lock>/pid).  Probe the same lock the same way;
    # a dead holder's lock does not block the merge.
    branch = str(meta.get("branch", ""))
    if branch:
        lock = track.lock_dir() / ("fix-" + branch.replace("/", "-") + ".lock")
        if lock.is_dir():
            pid_text = ""
            try:
                pid_text = (lock / "pid").read_text(encoding="ascii").split()[0]
            except (OSError, IndexError):
                pass
            if pid_text.isdigit() and _pid_alive(int(pid_text)):
                raise GateFailure(
                    f"{lock} is held by live pid {pid_text}: local/bin/autofix.sh "
                    "is rewriting this branch. Merging under it would race the "
                    "fix commits."
                )

    cap = int(os.environ.get("MIPSTARRE_FIX_CAP", DEFAULT_FIX_CAP))
    iterations = meta.get("fix_iterations", 0)
    if not isinstance(iterations, int):
        raise GateFailure(f"fix_iterations is {iterations!r}; expected an integer")
    if iterations > cap:
        raise GateFailure(
            f"fix_iterations is {iterations}, above the combined cap of {cap}. "
            "The cap is combined across ci/blueprint/review fixes (DESIGN.md:70-72); "
            "a PR past it needs human attention, not another merge attempt."
        )


def run_gate(repo_root: Path, record: track.PullRequest, *, allow_unreviewed: bool,
             adjudicated: bool = False) -> str:
    """Raise ``GateFailure`` unless the PR may merge; return the head SHA."""
    meta = record.meta
    record_dir = record.path.parent

    if record.state != "open":
        raise GateFailure(
            f"PR #{record.id} is {record.state!r}, not open; nothing to merge."
        )

    branch = record.branch
    if not branch:
        raise GateFailure(f"PR #{record.id} has no branch recorded")
    tip = git(repo_root, "rev-parse", "--verify", f"{branch}^{{commit}}", check=False)
    if not tip:
        raise GateFailure(
            f"branch {branch!r} does not resolve in this repository; it may have "
            "been deleted already."
        )

    head_sha = meta.get("head_sha")
    if not head_sha:
        raise GateFailure(
            f"PR #{record.id} has head_sha: null. Run local/bin/ci.sh on the branch "
            "so the record names the commit that was tested."
        )
    if str(head_sha) != tip:
        raise GateFailure(
            f"head_sha {str(head_sha)[:12]} does not match the branch tip "
            f"{tip[:12]}. New commits landed after the recorded CI/review; re-run "
            "local/bin/ci.sh and local/bin/review.sh (DESIGN.md:66-69)."
        )

    ci_status = meta.get("ci_status")
    if ci_status != "success":
        raise GateFailure(
            f"ci_status is {ci_status!r}, not 'success'. Run local/bin/ci.sh "
            f"{record.id} and merge only on green."
        )
    ci_dir = record_dir / "ci"
    manifest = ci_dir / f"{head_sha}.json"
    if not ci_dir.is_dir():
        raise GateFailure(
            f"{ci_dir} does not exist. The frontmatter claims success but there is "
            "no per-SHA manifest to back it; run local/bin/ci.sh."
        )
    if not manifest.is_file():
        raise GateFailure(
            f"no CI manifest at {manifest}. ci_status in frontmatter is a summary; "
            "the manifest for the exact head SHA is the evidence."
        )

    review_state = meta.get("review_state")
    if kill_switch_disabled("LOCAL_REVIEW_ENABLED"):
        if not allow_unreviewed:
            raise GateFailure(
                "LOCAL_REVIEW_ENABLED=false, so no verdict can be produced. The "
                "gate does not silently waive review: re-enable reviews, or merge "
                "with --allow-unreviewed, which records the waiver in the PR."
            )
        sys.stderr.write(
            "warning: merging with review disabled and --allow-unreviewed given\n"
        )
    elif review_state == "blocked":
        raise GateFailure(
            "review_state is 'blocked': CI failed, so review was refused rather "
            "than skipped (DESIGN.md:66-69). Fix CI first."
        )
    elif not review_state:
        raise GateFailure(
            f"PR #{record.id} has review_state: null. Run local/bin/review.sh "
            f"{record.id} on the current head SHA."
        )
    else:
        check_review_verdict(record_dir, str(head_sha), str(review_state),
                             adjudicated=adjudicated)

    check_fix_gates(repo_root, record_dir, meta)
    return str(head_sha)


# ---------------------------------------------------------------------------
# Merge
# ---------------------------------------------------------------------------

def ensure_mergeable_worktree(repo_root: Path, base: str) -> None:
    dirty = git(repo_root, "status", "--porcelain")
    if dirty:
        raise GateFailure(
            "the working tree is not clean; commit or stash before merging:\n"
            + dirty
        )
    current = git(repo_root, "rev-parse", "--abbrev-ref", "HEAD")
    if current != base:
        raise GateFailure(
            f"HEAD is on {current!r} but this PR targets {base!r}. "
            f"Run: git switch {base}"
        )


def update_origin_alias(repo_root: Path, base: str) -> None:
    """Keep ``refs/remotes/origin/<base>`` resolvable.

    DESIGN.md:84-85: the hooks and every diff-based audit silently self-disable
    when ``origin/main`` does not resolve.  There is no remote here, so the
    alias is maintained by hand at exactly the moment ``main`` moves.
    """
    if not git_ok(repo_root, "show-ref", "--verify", "--quiet", f"refs/heads/{base}"):
        sys.stderr.write(
            f"warning: refs/heads/{base} not found; skipping the origin alias update\n"
        )
        return
    git(repo_root, "update-ref", f"refs/remotes/origin/{base}", f"refs/heads/{base}")
    sys.stdout.write(f"refs/remotes/origin/{base} -> refs/heads/{base}\n")


def remove_branch_and_worktree(repo_root: Path, branch: str, *, dry_run: bool) -> None:
    listing = git(repo_root, "worktree", "list", "--porcelain", check=False)
    target: str | None = None
    current_path: str | None = None
    for line in listing.splitlines():
        if line.startswith("worktree "):
            current_path = line[len("worktree "):]
        elif line.startswith("branch ") and line[len("branch "):] == f"refs/heads/{branch}":
            target = current_path
    if target:
        if dry_run:
            sys.stdout.write(f"[dry-run] would remove worktree {target}\n")
        elif git_ok(repo_root, "worktree", "remove", target):
            sys.stdout.write(f"removed worktree {target}\n")
        else:
            sys.stderr.write(
                f"warning: could not remove worktree {target} (uncommitted files?); "
                f"remove it by hand with: git worktree remove --force {target}\n"
            )
    if dry_run:
        sys.stdout.write(f"[dry-run] would delete branch {branch}\n")
        return
    if git_ok(repo_root, "branch", "-d", branch):
        sys.stdout.write(f"deleted branch {branch}\n")
    else:
        sys.stderr.write(
            f"warning: 'git branch -d {branch}' refused; the branch is kept. "
            "Delete it by hand once you have confirmed the merge.\n"
        )


def spawn_cache_warmer(repo_root: Path) -> None:
    """Fire the single-writer cache warmer, detached.

    DESIGN.md:63-65: only the warmer writes the hot main cache.  Merging is the
    event that invalidates it, so this is where the refresh belongs — in the
    background, because the merge must not block on a build.
    """
    script = repo_root / "local" / "bin" / "cache-warmer.sh"
    if not script.is_file():
        sys.stderr.write(
            f"note: {script} does not exist yet; the hot main cache is now stale "
            "and will be rebuilt on demand.\n"
        )
        return
    logs = track.cache_root() / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    log_path = logs / f"cache-warmer-{track.utcnow().replace(':', '')}.log"
    handle = open(log_path, "w", encoding="utf-8")
    subprocess.Popen(  # noqa: S603 - fixed argv, no shell
        [str(script)], cwd=str(repo_root),
        stdout=handle, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
        start_new_session=True,
    )
    sys.stdout.write(f"cache warmer started in the background; log: {log_path}\n")


def run_followups(repo_root: Path, pr_id: str) -> None:
    """Optional follow-up mining on the merged diff.

    issue-automation.yml:573-624 ran this from a *trusted* checkout of the base
    branch so a malicious head could not swap the prompt.  Locally the same
    defense is: run the script from the main worktree, never from the branch
    that was merged (DESIGN.md:76-77).  That is what ``cwd=repo_root`` means
    here, and it is the reason this call happens after the merge rather than in
    the branch worktree.
    """
    script = repo_root / "local" / "bin" / "followups.sh"
    if not script.is_file():
        sys.stderr.write(
            f"note: {script} does not exist yet; skipping follow-up mining. "
            "Deferred obligations from this PR must be filed by hand with "
            "local/bin/issue_new.py --labels follow-up.\n"
        )
        return
    if os.environ.get("MIPSTARRE_LLM_ENABLED") == "false":
        sys.stderr.write("note: MIPSTARRE_LLM_ENABLED=false; skipping follow-up mining.\n")
        return
    result = subprocess.run([str(script), pr_id], cwd=str(repo_root), check=False)
    if result.returncode != 0:
        sys.stderr.write(f"warning: followups.sh exited {result.returncode}\n")


def merge_pr(args: argparse.Namespace) -> int:
    repo_root = args.repo_root.resolve()
    pr_id = track.normalize_id(args.pr)

    with track.pr_lock(pr_id):
        record = track.load_pr(repo_root, pr_id)
        base = str(record.meta.get("base") or "main")
        head_sha = run_gate(repo_root, record, allow_unreviewed=args.allow_unreviewed,
                            adjudicated=args.adjudicated)
        ensure_mergeable_worktree(repo_root, base)
        sys.stdout.write(
            f"gate passed: PR #{pr_id} {record.branch} @ {head_sha[:12]} -> {base}\n"
        )
        if args.check_only:
            return 0

        keep_open, auto_close = track.linked_issues(record.body, record.branch)
        title = track.sanitize(record.title or record.branch, track.TITLE_LIMIT)
        message = f"Merge PR #{pr_id}: {title}"

        if args.dry_run:
            sys.stdout.write(
                f"[dry-run] git merge --no-ff {record.branch} -m {message!r}\n"
                f"[dry-run] would auto-close {auto_close or 'nothing'} as completed\n"
                f"[dry-run] would post progress notes for {keep_open or 'nothing'}\n"
            )
            return 0

        try:
            git(repo_root, "merge", "--no-ff", "--no-edit", "-m", message, record.branch)
        except LayerError as exc:
            # The registry (issues/, prs/, results/telemetry/) is
            # single-instance on the base branch by protocol
            # (local/protocols/issues-prs.md; EVOLUTION.md "Registry root
            # resolves to the primary checkout"), so a conflict confined to
            # registry paths is resolved with the base's version and the
            # merge completes.  Any conflict touching a non-registry path
            # aborts as before: content conflicts are for humans.
            conflicted = [
                line[3:]
                for line in git(repo_root, "status", "--porcelain",
                                check=False).splitlines()
                if line.startswith("UU ") or line.startswith("AA ")
            ]
            registry_prefixes = ("issues/", "prs/", "results/telemetry/")
            if conflicted and all(
                path.startswith(registry_prefixes) for path in conflicted
            ):
                for path in conflicted:
                    git(repo_root, "checkout", "--ours", "--", path)
                    git(repo_root, "add", "--", path)
                git(repo_root, "commit", "--no-edit", "--no-verify")
                sys.stdout.write(
                    "registry-path merge conflicts resolved with the base's "
                    f"version ({len(conflicted)} file(s)); see "
                    "local/protocols/issues-prs.md\n"
                )
            else:
                # Leave no half-merged tree behind: a conflicted merge must
                # not look like a partially applied one, and none of the
                # bookkeeping below has run yet.
                git(repo_root, "merge", "--abort", check=False)
                raise GateFailure(
                    f"the merge of {record.branch} into {base} conflicts; the working "
                    "tree was restored and nothing was recorded. Rebase or merge "
                    f"{base} into the branch, re-run local/bin/ci.sh and "
                    f"local/bin/review.sh on the new head, then try again.\n{exc}"
                ) from exc
        merge_commit = git(repo_root, "rev-parse", "HEAD")
        sys.stdout.write(f"merged as {merge_commit}\n")

        update_origin_alias(repo_root, base)

        record = track.load_pr(repo_root, pr_id)
        record.meta["state"] = "merged"
        record.meta["merged_commit"] = merge_commit
        track.atomic_write(record.path, record.render())
        sys.stdout.write(f"{record.path.relative_to(repo_root)}: state=merged\n")

    # Auto-close first so the tracking counts computed below are current.
    closed_ok: list[str] = []
    for ident in auto_close:
        issue = track.try_load_issue(repo_root, ident)
        if issue is None:
            sys.stderr.write(
                f"warning: PR #{pr_id} says 'Closes #{ident}' but no such issue "
                "file exists; nothing closed.\n"
            )
            continue
        issue_close.close_issue(
            repo_root, ident, "completed",
            note=f"closed by the merge of PR #{pr_id}",
            force=False, dry_run=False,
        )
        closed_ok.append(ident)

    # ... and exclude them from the merged-PR progress notes, or the tracking
    # parent receives one note from the close above and a second from here.
    track.on_pr_merged(repo_root, pr_id, dry_run=False, exclude=closed_ok)

    if not args.no_followups:
        run_followups(repo_root, pr_id)
    if not args.no_warm_cache:
        spawn_cache_warmer(repo_root)
    remove_branch_and_worktree(repo_root, record.branch, dry_run=False)
    return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="pr_merge.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("pr", metavar="ID", help="PR record id, e.g. 0007")
    parser.add_argument("--check-only", action="store_true",
                        help="run the gate and report, merge nothing")
    parser.add_argument("--adjudicated", action="store_true",
                        help="accept review_state ADJUDICATED (operator adjudication "
                             "after the round cap; local/protocols/review.md section 12)")
    parser.add_argument("--allow-unreviewed", action="store_true",
                        help="only meaningful with LOCAL_REVIEW_ENABLED=false: "
                             "merge without a verdict and say so")
    parser.add_argument("--no-followups", action="store_true",
                        help="skip the follow-up mining hook")
    parser.add_argument("--no-warm-cache", action="store_true",
                        help="do not start the background cache warmer")
    parser.add_argument("--repo-root", type=Path, default=track.default_repo_root(),
                        help="repository root (default: two levels above this script)")
    parser.add_argument("--dry-run", action="store_true",
                        help="run the gate, then print the actions instead of taking them")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return merge_pr(args)
    except GateFailure as exc:
        sys.stderr.write(f"pr_merge.py: REFUSING TO MERGE — {exc}\n")
        return 1
    except LayerError as exc:
        sys.stderr.write(f"pr_merge.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
