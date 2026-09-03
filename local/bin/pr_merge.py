#!/usr/bin/env python3
"""The merge gate: prove the exact head SHA is green and reviewed, then merge it.

The one script in the issue-lifecycle area that changes ``main``: the local
replacement for GitHub's branch-protection rules, which upstream were server-side
settings no client could bypass.  A single-account repository has none — the owner can
always press Merge — so the authority is this file.  It refuses by default, every
override is named, and ``gh_common.merge_pr`` merges through the REST ``sha`` guard,
which makes GitHub reject the call if the head moved meanwhile.

Every piece of evidence lives on GitHub, bound to the head SHA (issues-prs.md; the old
``prs/`` registry is archived under ``results/telemetry/registry-archive/``):

1. the PR is open, unmerged, not a draft;
2. the primary worktree is clean and on the base, and the local branch tip is that
   SHA — the merge must be of the bytes that were built here;
3. the eight ``local-ci/<step>`` contexts (ci.sh:70) and ``local-ci/summary`` are
   ``success`` on it.  A missing context blocks: GitHub's combined state reads
   "success" for a commit carrying no statuses at all;
4. a ``<!-- mipstarre-review pr=N head=SHA -->`` COMMENT review sits on that exact
   commit id, its ``VERDICT:`` line is APPROVED (or COMMENTED with zero unchecked
   findings), and ``local-review/summary`` is ``success`` (DESIGN.md:66-69) — one
   account cannot self-APPROVE, so an adverse verdict travels in that status;
5. no ``CHANGES_REQUESTED`` review sits on that SHA, from anyone;
6. the fix loop is quiescent: no live autofix.sh lock.  The ``[codex-auto-fix]`` /
   ``[codex-review-fix]`` commit count since the merge base is printed for the
   record only — the iteration cap is autofix.sh's loop-termination bound and
   carries no merge authority (issues-prs.md 3; EVOLUTION.md 2026-09-02);
7. every issue this PR closes has no open sub-issue left.

``--adjudicated`` waives gate 4's adverse verdict — nothing else — when an
``ADJUDICATION`` comment names this exact head (review.md 12).  GitHub merges and
closes the linked issues itself, so no local bookkeeping can double-count.  The
best-effort tail then fast-forwards local ``main``, refreshes the
``refs/remotes/origin/main`` alias the hooks and diff-based audits need in order not
to self-disable (DESIGN.md:83-85), warms the cache and drops the branch.

Usage: pr_merge.py N [--check-only | --dry-run] [--adjudicated] [--no-warm-cache]
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))  # gh_common/wf_util sit here
import gh_common  # noqa: E402
from wf_util import (TITLE_LIMIT, LayerError, cache_root, default_repo_root,  # noqa: E402
                     file_lock, lock_dir, sanitize, utcnow)

#: ci.sh:70 ``STEP_NAMES`` verbatim, plus the roll-up ci.sh posts last.
CI_STEPS = ("build", "blueprint-render", "paper-gaps", "blueprint-sync",
            "file-length", "proof-debt", "proof-evasion", "statement-origin")
CI_CONTEXTS = tuple(f"local-ci/{step}" for step in CI_STEPS) + ("local-ci/summary",)
REVIEW_CONTEXT = "local-review/summary"

#: Findings are task-list items; an unticked box is an open finding.  Kept compatible
#: with review.sh's tally and autofix.sh's ledger read.
UNCHECKED_FINDING_RE = re.compile(r"^\s*[-*]\s*\[ \]", re.MULTILINE)
UNCHECKED_ID_RE = re.compile(r"^\s*[-*]\s*\[ \]\s*(F\d+)\b", re.MULTILINE)
VERDICT_RE = re.compile(r"^VERDICT:\s*([A-Z_]+)", re.MULTILINE)
HEAD_FIELD_RE = re.compile(r"^head=([0-9a-f]{40})$", re.MULTILINE)
DISPOSITION_RE = re.compile(
    r"^\s*[-*]\s*\[[xX]\]\s*(F\d+)\b.*?\s+[—–]\s+"
    r"(?:fixed in [0-9a-f]{7,40}|moot:\s*\S.*|deferred to issue #(\d+):\s*\S.*)$",
    re.MULTILINE)

#: autofix.sh:62-63 ``PREFIX_AUTO``/``PREFIX_REVIEW`` — the ping-pong guard's subject
#: prefixes; gate 6 reports how many such commits the PR carries.
FIX_COMMIT_PREFIXES = ("[codex-auto-fix]", "[codex-review-fix]")

#: GitHub's nine auto-closing keywords, exactly (close/closes/closed, fix/fixes/fixed,
#: resolve/resolves/resolved) — the gate must see every issue GitHub will close on
#: merge.  ``Addresses`` keeps an issue open and imposes no dependency
#: (CONTRIBUTING.md:61-62).  Keep in sync with pr_open.py CLOSES_RE.
CLOSES_RE = re.compile(r"\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?):?\s+#(\d+)", re.IGNORECASE)


class GateFailure(LayerError):
    """A refusal to merge.  Distinct type so the caller can report it as such."""


# --------------------------------------------------------------- small helpers

def git(repo_root: Path, *args: str, check: bool = True) -> str:
    result = subprocess.run(["git", *args], cwd=str(repo_root),
                            capture_output=True, text=True, check=False)
    if check and result.returncode != 0:
        raise LayerError(f"git {' '.join(args)} failed ({result.returncode}): "
                         f"{result.stderr.strip() or result.stdout.strip()}")
    return result.stdout.strip()


def git_ok(repo_root: Path, *args: str) -> bool:
    return subprocess.run(["git", *args], cwd=str(repo_root), capture_output=True,
                          text=True, check=False).returncode == 0


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def passed(line: str) -> None:
    """One line of the gate report, printed as the gate clears (--check-only reads)."""
    sys.stdout.write(line + "\n")


# --------------------------------------------------------------------- gates

def ensure_mergeable_worktree(repo_root: Path, branch: str, base: str, head_sha: str) -> None:
    """Gate 2 — clean primary worktree on the base, local branch at the head.

    GitHub performs the merge, so none of this is needed for the merge itself; all of it
    is needed for the tail, which fast-forwards ``base`` in this very worktree and
    deletes the branch.  Refusing here keeps the failure before the irreversible step.
    """
    dirty = git(repo_root, "status", "--porcelain")
    if dirty:
        raise GateFailure("gate 2 (worktree): the primary tree is not clean, required clean "
                          "so the post-merge fast-forward cannot lose work:\n" + dirty)
    current = git(repo_root, "rev-parse", "--abbrev-ref", "HEAD")
    if current != base:
        raise GateFailure(f"gate 2 (worktree): HEAD is on {current!r}, required {base!r} "
                          f"(the PR base). Run: git switch {base}")
    tip = git(repo_root, "rev-parse", "--verify", f"{branch}^{{commit}}", check=False)
    if not tip:
        raise GateFailure(f"gate 2 (local branch): {branch!r} does not resolve here, required "
                          f"it at {head_sha[:12]}: git fetch github {branch}:{branch}")
    if tip != head_sha:
        raise GateFailure(f"gate 2 (local branch): {branch} tip is {tip[:12]}, required "
                          f"{head_sha[:12]} (the PR head). Push or fetch — the evidence binds "
                          "to the SHA, not to the branch name.")
    passed(f"gate 2 worktree clean on {base}, local tip == head")


def check_ci(statuses: dict, head_sha: str) -> None:
    """Gate 3 — every CI context is ``success`` on the exact head SHA."""
    problems: list[str] = []
    for context in CI_CONTEXTS:
        row = statuses.get(context)
        if row is None:
            problems.append(f"{context}: MISSING")
        elif row.get("state") != "success":
            problems.append(f"{context}: {row.get('state')} "
                            f"({sanitize(str(row.get('description') or ''), 120)})")
    if problems:
        raise GateFailure(f"gate 3 (CI): required success on {head_sha[:12]} for all "
                          f"{len(CI_CONTEXTS)} contexts; observed:\n  " + "\n  ".join(problems)
                          + "\nRun local/bin/ci.sh on this head. A missing context is a block, "
                          "never a pass: GitHub's combined state is 'success' for a commit "
                          "with no statuses at all.")
    passed(f"gate 3 all {len(CI_CONTEXTS)} local-ci contexts success")


def check_review(number: int, head_sha: str, reviews: list[dict], statuses: dict,
                 *, adjudicated: bool) -> set[int]:
    """Gate 4 — one verdict review on this commit id, clean or adjudicated."""
    marker = f"<!-- mipstarre-review pr={number} head={head_sha} -->"
    matching = [r for r in reviews
                if r.get("commit_id") == head_sha and marker in (r.get("body") or "")]
    if not matching:
        raise GateFailure(f"gate 4 (review): no review carrying {marker} on commit "
                          f"{head_sha[:12]}, required exactly one. A verdict on an earlier SHA "
                          "does not carry over (DESIGN.md:66-69): re-run review.sh.")
    # One verdict review per head is the contract; if a retry ever leaves two, the newest
    # is operative (the API returns reviews in creation order).
    body = matching[-1].get("body") or ""
    found = VERDICT_RE.search(body)
    verdict = found.group(1) if found else ""
    unchecked = len(UNCHECKED_FINDING_RE.findall(body))
    summary_state = (statuses.get(REVIEW_CONTEXT) or {}).get("state")
    # Green needs BOTH a clean verdict and a clean ledger: an APPROVED trailer
    # over unresolved findings is inconsistent reviewer output (round 2, F4).
    clean = verdict in ("APPROVED", "COMMENTED") and unchecked == 0
    if clean and summary_state == "success":
        passed(f"gate 4 verdict {verdict} on {head_sha[:12]}, {REVIEW_CONTEXT} success")
        return set()
    observed = (f"VERDICT {verdict or 'absent'} with {unchecked} unchecked finding(s), "
                f"{REVIEW_CONTEXT} {summary_state or 'MISSING'}")
    if not adjudicated:
        raise GateFailure(f"gate 4 (review): required VERDICT APPROVED, or COMMENTED with zero "
                          f"unchecked findings, and {REVIEW_CONTEXT} success; observed "
                          f"{observed}. Address the findings (or tick them off with a reason and "
                          "a tracked issue) and re-run review.sh, or merge --adjudicated.")
    # review.md section 12: past the round cap the operator may adjudicate what is left.
    round_marker = re.compile(rf"mipstarre-review pr={number} head=([0-9a-f]{{40}})")
    reviewed_heads = {m.group(1) for row in reviews
                      if (m := round_marker.search(row.get("body") or ""))}
    if len(reviewed_heads) < 4:
        raise GateFailure("gate 4 (review): adjudication is available only from review round "
                          f"5; found {len(reviewed_heads)} completed round(s).")
    finding_ids = UNCHECKED_ID_RE.findall(body)
    if len(finding_ids) != unchecked or len(set(finding_ids)) != unchecked:
        raise GateFailure("gate 4 (review): every unresolved finding must have one unique F<n> "
                          "identifier before it can be adjudicated.")
    accepted = None
    for row in gh_common.api(f"issues/{number}/comments", paginate=True):
        text = (row.get("body") or "").lstrip()
        heads = HEAD_FIELD_RE.findall(text)
        dispositions = DISPOSITION_RE.findall(text)
        disposition_ids = [match[0] for match in dispositions]
        if (text.startswith("ADJUDICATION") and heads == [head_sha]
                and sorted(disposition_ids) == sorted(finding_ids)
                and len(set(disposition_ids)) == len(disposition_ids)):
            accepted = (row, dispositions)
            break
    if accepted is None:
        raise GateFailure(f"gate 4 (review): --adjudicated given but no ADJUDICATION comment "
                          f"on PR #{number} has exactly head={head_sha} and one checked, valid "
                          f"disposition for each of {unchecked} unresolved finding(s).")
    row, dispositions = accepted
    for _, issue_number in dispositions:
        if not issue_number:
            continue
        issue = gh_common.api(f"issues/{issue_number}")
        if issue.get("pull_request") or issue.get("state") != "open":
            raise GateFailure(f"gate 4 (review): deferred issue #{issue_number} does not exist "
                              "as an open tracked issue.")
    where = str(row.get("html_url") or row.get("id"))
    sys.stderr.write(f"warning: merging PR #{number} on operator adjudication ({where}); the "
                     f"review evidence is adverse — {observed}\n")
    passed(f"gate 4 adjudicated at {head_sha[:12]} ({where})")
    return {int(issue_number) for _, issue_number in dispositions if issue_number}


def check_fix_gates(repo_root: Path, branch: str, base: str, head_sha: str) -> str:
    """Gate 6 — refuse while the serialized fix loop is mid-flight.
    Returns the merge base (gate 7 scans the same commit range); the fix-prefixed
    commit count is reported, never enforced (EVOLUTION.md 2026-09-02)."""
    # autofix.sh holds a mkdir-based lease keyed on the BRANCH (autofix.sh:580,
    # locks/fix-<branch with / -> ->.lock, holder pid in <lock>/pid).  Probe the same lock
    # the same way; a dead holder's lock does not block the merge.
    lock = lock_dir() / ("fix-" + branch.replace("/", "-") + ".lock")
    if lock.is_dir():
        pid_text = ""
        try:
            pid_text = (lock / "pid").read_text(encoding="ascii").split()[0]
        except (OSError, IndexError):
            pass
        if pid_text.isdigit() and _pid_alive(int(pid_text)):
            raise GateFailure(f"gate 6 (fix loop): {lock} is held by live pid {pid_text}, required "
                              "idle. autofix.sh is rewriting this branch and merging under it "
                              "would race the fix commits.")
    base_ref = None
    for candidate in (f"github/{base}", f"refs/remotes/origin/{base}", base):
        if git_ok(repo_root, "rev-parse", "--verify", "--quiet", f"{candidate}^{{commit}}"):
            base_ref = candidate
            break
    if base_ref is None:
        raise GateFailure(f"gate 7 (dependencies): no local ref resolves for base {base!r}, so "
                          f"the merge-base commit range cannot be scanned. Run: git fetch "
                          f"github {base}")
    merge_base = git(repo_root, "merge-base", base_ref, head_sha)
    # `git rev-list --format` prints a "commit <sha>" header before each formatted line.
    lines = git(repo_root, "rev-list", "--format=%s", f"{merge_base}..{head_sha}").splitlines()
    iterations = sum(1 for line in lines if not line.startswith("commit ")
                     and line.startswith(FIX_COMMIT_PREFIXES))
    passed(f"gate 6 fix loop idle; {iterations} fix-prefixed commit(s) since "
           f"{merge_base[:12]} (autofix.sh bounds its own loop)")
    return merge_base


def check_dependencies(repo_root: Path, number: int, body: str,
                       merge_base: str, head_sha: str,
                       deferred_issues: set[int]) -> None:
    """Gate 7 — nothing this PR closes may still have open children.

    GitHub honors closing keywords in the PR body AND in commit messages that
    land on the default branch, so both surfaces are scanned.  (Qualified
    ``owner/repo#N`` references are out of scope: single-repo project.)
    """
    surfaces = [body or ""]
    surfaces.append(git(repo_root, "log", "--format=%B", f"{merge_base}..{head_sha}",
                        check=False))
    closes = list(dict.fromkeys(n for text in surfaces
                                for n in CLOSES_RE.findall(text)))
    if conflicts := deferred_issues.intersection(int(ident) for ident in closes):
        raise GateFailure(f"gate 7 (dependencies): PR #{number} also closes deferred issue(s) "
                          f"{sorted(conflicts)}, which must remain open.")
    for ident in closes:
        children = gh_common.open_sub_issues(int(ident))
        if children:
            raise GateFailure(f"gate 7 (dependencies): PR #{number} closes #{ident}, which still "
                              f"has open sub-issue(s) {', '.join('#%d' % c for c in children)}, "
                              "required none. Finish or re-parent them first.")
    passed("gate 7 " + (", ".join(f"#{i} has no open sub-issue" for i in closes)
                        or "no 'Closes #N' footer; nothing to depend on"))


def run_gate(repo_root: Path, number: int, *, adjudicated: bool) -> dict:
    """Raise ``GateFailure`` unless the PR may merge; return the merge facts."""
    pr = gh_common.pr_view(number)
    state = pr.get("state")
    if state != "open" or pr.get("merged"):
        raise GateFailure(f"gate 1 (open PR): PR #{number} is state={state!r} "
                          f"merged={bool(pr.get('merged'))}, required open and unmerged.")
    if pr.get("draft") is not False:
        raise GateFailure(f"gate 1 (open PR): PR #{number} reports draft={pr.get('draft')!r}, "
                          "required exactly false. (A missing field means the API response "
                          "changed shape — fail closed, don't guess.)")
    head = pr.get("head") or {}
    head_sha = str(head.get("sha") or "")
    branch = str(head.get("ref") or "")
    base = str((pr.get("base") or {}).get("ref") or "")
    if not head_sha or not branch or not base:
        raise GateFailure(f"gate 1 (open PR): PR #{number} reports head sha={head_sha!r} "
                          f"ref={branch!r} base={base!r}; all three are required.")
    passed(f"gate 1 open, not a draft: {branch} @ {head_sha[:12]} -> {base}")
    ensure_mergeable_worktree(repo_root, branch, base, head_sha)
    # Gate 2b — the head must CONTAIN the current base tip: CI and review bind
    # to the head alone, so a branch behind the base would merge a base/head
    # combination nothing ever tested (round 3, F2).  Fetch first so "current"
    # means GitHub's tip, not a stale local remote-tracking ref.
    if not git_ok(repo_root, "fetch", "github", base):
        raise GateFailure(f"gate 2b (fresh base): 'git fetch github {base}' failed; cannot "
                          "verify the branch is up to date with the base.")
    if not git_ok(repo_root, "merge-base", "--is-ancestor", f"github/{base}", head_sha):
        base_tip = git(repo_root, "rev-parse", "--short", f"github/{base}", check=False)
        raise GateFailure(f"gate 2b (fresh base): {base} is at {base_tip} and the PR head "
                          f"{head_sha[:12]} does not contain it. Merge or rebase the base "
                          "into the branch, re-run CI and review on the new head, then merge.")
    passed(f"gate 2b head contains the current {base} tip")
    statuses = gh_common.latest_statuses(head_sha)  # one read; gates 3 and 4 share it
    reviews = gh_common.pr_reviews(number)
    check_ci(statuses, head_sha)
    deferred_issues = check_review(number, head_sha, reviews, statuses, adjudicated=adjudicated)
    # Gate 5 — a CHANGES_REQUESTED review on this head is final, and never adjudicable.
    blockers = [r for r in reviews if r.get("state") == "CHANGES_REQUESTED"
                and r.get("commit_id") == head_sha]
    if blockers:
        who = ", ".join(sorted({sanitize(str((r.get("user") or {}).get("login") or "?"), 40)
                                for r in blockers}))
        raise GateFailure(f"gate 5 (changes requested): {len(blockers)} CHANGES_REQUESTED "
                          f"review(s) by {who} on {head_sha[:12]}, required none. Adjudication "
                          "never overrides this: dismiss it on GitHub, or fix and re-review.")
    passed("gate 5 no CHANGES_REQUESTED review on this head")
    merge_base = check_fix_gates(repo_root, branch, base, head_sha)
    check_dependencies(repo_root, number, str(pr.get("body") or ""), merge_base, head_sha,
                       deferred_issues)
    return {"pr": pr, "head_sha": head_sha, "branch": branch, "base": base}


# ------------------------------------- post-merge tail: best effort, non-fatal

def fast_forward_base(repo_root: Path, base: str) -> bool:
    """Move local ``base`` onto the merge GitHub just made, if it is strictly behind: a
    local commit GitHub has not seen is somebody's unpushed work, not this tail's call.
    Returns True only when local ``base`` verifiably sits on the fetched remote."""
    remote = f"github/{base}"
    if not git_ok(repo_root, "rev-parse", "--verify", "--quiet", f"{remote}^{{commit}}"):
        sys.stderr.write(f"warning: {remote} does not resolve after the fetch; local {base} "
                         "left where it was\n")
        return False
    if not git_ok(repo_root, "merge-base", "--is-ancestor", base, remote):
        sys.stderr.write(f"warning: local {base} is not an ancestor of {remote}, so it is not "
                         "moved — diverged history is a human's call, and the merge is already "
                         "recorded on GitHub\n")
        return False
    if git_ok(repo_root, "merge", "--ff-only", remote):
        sys.stdout.write(f"{base} fast-forwarded to "
                         f"{git(repo_root, 'rev-parse', '--short', base, check=False)}\n")
        return True
    sys.stderr.write(f"warning: could not fast-forward {base}; by hand: git merge "
                     f"--ff-only {remote}\n")
    return False


def update_origin_alias(repo_root: Path, base: str) -> None:
    """Keep ``refs/remotes/origin/<base>`` resolvable: the hooks and every diff-based
    audit silently self-disable without it (DESIGN.md:83-85), and the one remote here is
    named ``github``, so the alias is maintained by hand exactly when ``main`` moves."""
    if not git_ok(repo_root, "show-ref", "--verify", "--quiet", f"refs/heads/{base}"):
        sys.stderr.write(f"warning: refs/heads/{base} not found; skipping the origin alias\n")
        return
    git(repo_root, "update-ref", f"refs/remotes/origin/{base}", f"refs/heads/{base}")
    sys.stdout.write(f"refs/remotes/origin/{base} -> refs/heads/{base}\n")


def spawn_cache_warmer(repo_root: Path) -> None:
    """Fire the single-writer cache warmer, detached: only the warmer writes the hot main
    cache (DESIGN.md:63-65), merging is the event that invalidates it, and the merge
    itself must not block on the rebuild."""
    script = repo_root / "local" / "bin" / "cache-warmer.sh"
    if not script.is_file():
        sys.stderr.write(f"note: {script} does not exist yet; the hot main cache is now stale "
                         "and will be rebuilt on demand.\n")
        return
    logs = cache_root() / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    log_path = logs / f"cache-warmer-{utcnow().replace(':', '')}.log"
    handle = open(log_path, "w", encoding="utf-8")
    subprocess.Popen(  # noqa: S603 - fixed argv, no shell
        [str(script)], cwd=str(repo_root), stdout=handle,
        stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL, start_new_session=True)
    sys.stdout.write(f"cache warmer started in the background; log: {log_path}\n")


def remove_branch_and_worktree(repo_root: Path, branch: str) -> None:
    """Drop the branch worktree, then the branch itself, under the old safeguards."""
    listing = git(repo_root, "worktree", "list", "--porcelain", check=False)
    target: str | None = None
    current_path: str | None = None
    for line in listing.splitlines():
        if line.startswith("worktree "):
            current_path = line[len("worktree "):]
        elif line.startswith("branch ") and line[len("branch "):] == f"refs/heads/{branch}":
            target = current_path
    if target:
        if git_ok(repo_root, "worktree", "remove", target):
            sys.stdout.write(f"removed worktree {target}\n")
        else:
            sys.stderr.write(f"warning: could not remove worktree {target} (uncommitted "
                             f"files?); by hand: git worktree remove --force {target}\n")
    # `git branch -d` is the safeguard: it refuses unless the branch is merged into HEAD,
    # which it only is once the fast-forward above succeeded.
    if git_ok(repo_root, "branch", "-d", branch):
        sys.stdout.write(f"deleted branch {branch}\n")
    else:
        sys.stderr.write(f"warning: 'git branch -d {branch}' refused; the branch is kept. "
                         "Delete it once you have confirmed the merge.\n")


def post_merge(repo_root: Path, base: str, branch: str, *, warm_cache: bool) -> None:
    """Housekeeping after a proven merge; every failure is a warning, not an exit.

    Order matters: the origin alias, the cache warmer and the branch cleanup all
    assume local ``base`` sits on the merge.  When the fast-forward is refused
    (diverged local history), running them anyway would bind the alias and the
    warm cache to the WRONG main and silently skew every diff-based audit — so
    everything downstream of the fast-forward is gated on it.
    """
    if not git_ok(repo_root, "fetch", "github", base):
        sys.stderr.write(f"warning: 'git fetch github {base}' failed; local {base}, the "
                         "origin alias and the branch cleanup are left to you.\n")
        return
    if not fast_forward_base(repo_root, base):
        sys.stderr.write(f"warning: local {base} was not fast-forwarded; skipping the origin "
                         "alias refresh, the cache warmer and the branch cleanup — resolve "
                         f"local {base} first, then rerun them by hand.\n")
        return
    update_origin_alias(repo_root, base)
    if warm_cache:
        spawn_cache_warmer(repo_root)
    remove_branch_and_worktree(repo_root, branch)


# --------------------------------------------------------------- entry point

def run_merge(args: argparse.Namespace) -> int:
    repo_root = args.repo_root.resolve()
    number = int(args.pr)
    # The exact-SHA REST guard is the real protection against a concurrent merge; this
    # lock only keeps two local sessions from gating in lockstep.
    with file_lock(f"pr-{number}"):
        gate = run_gate(repo_root, number, adjudicated=args.adjudicated)
        head_sha, branch, base = gate["head_sha"], gate["branch"], gate["base"]
        title = sanitize(str(gate["pr"].get("title") or branch), TITLE_LIMIT)
        passed(f"gate passed: PR #{number} {title} @ {head_sha[:12]} -> {base}")
        if args.check_only:
            return 0
        if args.dry_run:
            sys.stdout.write(f"[dry-run] would merge PR #{number} at {head_sha} (REST PUT with "
                             "the exact-sha guard); GitHub would close the linked issues\n"
                             f"[dry-run] would fetch github, fast-forward {base}, refresh "
                             f"refs/remotes/origin/{base}, warm the cache, then remove the "
                             f"worktree and branch {branch}\n")
            return 0
        sys.stdout.write(f"merged as {gh_common.merge_pr(number, head_sha)}; GitHub closed "
                         "the linked issues\n")
    try:
        post_merge(repo_root, base, branch, warm_cache=not args.no_warm_cache)
    except LayerError as exc:
        sys.stderr.write(f"warning: post-merge housekeeping incomplete: {exc}\n")
    return 0


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(prog="pr_merge.py", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("pr", metavar="N", type=int, help="GitHub PR number, e.g. 7")
    parser.add_argument("--check-only", action="store_true",
                        help="run the gate and report, merge nothing")
    parser.add_argument("--adjudicated", action="store_true",
                        help="accept an adverse verdict backed by an ADJUDICATION comment "
                             "on this exact head (review.md section 12)")
    parser.add_argument("--no-warm-cache", action="store_true",
                        help="do not start the background cache warmer")
    parser.add_argument("--repo-root", type=Path, default=default_repo_root(),
                        help="repository root (default: two levels above this script)")
    parser.add_argument("--dry-run", action="store_true",
                        help="run the gate, then print the actions instead of taking them")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return run_merge(args)
    except GateFailure as exc:
        sys.stderr.write(f"pr_merge.py: REFUSING TO MERGE — {exc}\n")
        return 1
    except LayerError as exc:
        sys.stderr.write(f"pr_merge.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
