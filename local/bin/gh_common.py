#!/usr/bin/env python3
"""The one GitHub layer for ``local/bin`` — a thin, fail-closed wrapper over ``gh``.

GitHub is the single source of truth for issues, PRs, CI evidence (commit
statuses on the exact head SHA), review verdicts (COMMENT reviews bound to a
commit id), and merges (REST merge guarded by an exact-SHA match).  This module
is the only place workflow scripts talk to GitHub, as a Python import or via
its CLI (``gh_common.py <subcommand> ...``) from shell.

Design rules (local/protocols/issues-prs.md):

* At most one write mutation per invocation of a helper; ambiguity after a
  failed write is resolved by re-reading state and adopting, never by
  repeating the mutation.  Writes that are idempotent by content (statuses,
  close-PATCH) may be retried blindly.
* Everything uses ``gh api`` (raw REST), so no feature of a modern ``gh`` CLI
  is required — the exact-SHA merge guard is the REST ``sha`` parameter, not a
  CLI flag.
* Fail closed: a network failure after retries raises; no local fallback
  record is ever written.

Environment: ``MIPSTARRE_GH`` (gh binary; default ``gh`` on PATH, then
``~/.local/bin/gh``), ``MIPSTARRE_GITHUB_REPO`` (``owner/repo``; default
parsed from the ``github`` remote of the primary checkout).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from wf_util import LayerError, atomic_write, check_bracket_free, default_repo_root, utcnow

#: One page of the REST pagination loop; also the adoption search window.
PAGE = 100

#: GitHub caps comment/review bodies at 65536 characters; leave headroom for
#: the marker line and the truncation notice.
COMMENT_BODY_LIMIT = 60000

_TRANSIENT_RE = re.compile(
    r"(?i)(timed? ?out|connection|temporar|unavailable|network|reset by peer|"
    r"tls|eof|http (?:429|5\d\d)|rate limit|bad gateway|service unavailable)"
)

_REMOTE_RE = re.compile(r"github\.com[:/]([^/]+/[^/\s]+?)(?:\.git)?$")


def gh_bin() -> str:
    override = os.environ.get("MIPSTARRE_GH")
    if override:
        return override
    found = shutil.which("gh")
    if found:
        return found
    fallback = Path.home() / ".local" / "bin" / "gh"
    if fallback.exists():
        return str(fallback)
    raise LayerError("gh CLI not found (set MIPSTARRE_GH or install gh)")


def repo_slug(repo_root: Path | None = None) -> str:
    override = os.environ.get("MIPSTARRE_GITHUB_REPO")
    if override:
        return override
    root = repo_root or default_repo_root()
    proc = subprocess.run(
        ["git", "-C", str(root), "remote", "get-url", "github"],
        capture_output=True, text=True,
    )
    if proc.returncode == 0:
        match = _REMOTE_RE.search(proc.stdout.strip())
        if match:
            return match.group(1)
    raise LayerError(
        "cannot resolve the GitHub repo: set MIPSTARRE_GITHUB_REPO=owner/repo "
        "or add a 'github' remote to the primary checkout"
    )


def run_gh(args: list[str], *, input_text: str | None = None,
           mutation: bool = False, idempotent: bool = False,
           retries: int = 3) -> str:
    """Run ``gh`` and return stdout; raise ``LayerError`` on final failure.

    A non-idempotent mutation is attempted exactly once — the caller owns
    ambiguity recovery by re-reading state.  Reads and idempotent mutations
    retry on transient failures with linear backoff.
    """
    attempts = 1 if (mutation and not idempotent) else max(1, retries)
    env = dict(os.environ, GH_PROMPT_DISABLED="1", GH_NO_UPDATE_NOTIFIER="1",
               NO_COLOR="1", GH_PAGER="cat")
    last_err = ""
    for attempt in range(1, attempts + 1):
        proc = subprocess.run(
            [gh_bin(), *args], input=input_text,
            capture_output=True, text=True, env=env,
        )
        if proc.returncode == 0:
            return proc.stdout
        last_err = (proc.stderr or proc.stdout or "").strip()
        if attempt < attempts and _TRANSIENT_RE.search(last_err):
            time.sleep(5 * attempt)
            continue
        break
    raise LayerError(f"gh {' '.join(args[:3])}... failed: {last_err[:2000]}")


def api(path: str, *, method: str | None = None, payload: dict | None = None,
        paginate: bool = False, mutation: bool = False,
        idempotent: bool = False, absolute: bool = False):
    """Call the REST API under ``repos/<slug>/`` (or an absolute *path*).

    Pagination is manual (``?per_page=100&page=N``) so nothing here depends on
    a modern ``gh``.  Returns parsed JSON (``None`` for an empty response).
    """
    full = path if absolute else f"repos/{repo_slug()}/{path}"

    def one(page_path: str):
        args = ["api", page_path]
        if method:
            args += ["-X", method]
        input_text = None
        if payload is not None:
            args += ["--input", "-"]
            input_text = json.dumps(payload)
        out = run_gh(args, input_text=input_text, mutation=mutation,
                     idempotent=idempotent)
        return json.loads(out) if out.strip() else None

    if not paginate:
        return one(full)

    sep = "&" if "?" in full else "?"
    rows: list = []
    page = 1
    while True:
        batch = one(f"{full}{sep}per_page={PAGE}&page={page}")
        if not batch:
            break
        rows.extend(batch)
        if len(batch) < PAGE:
            break
        page += 1
    return rows


# ---------------------------------------------------------------------------
# Commit statuses — CI and review evidence, bound to the exact head SHA
# ---------------------------------------------------------------------------

def post_status(sha: str, context: str, state: str, description: str = "",
                target_url: str | None = None) -> None:
    """Post one commit status.  Idempotent by content: latest-per-context wins."""
    if state not in ("pending", "success", "failure", "error"):
        raise LayerError(f"invalid status state {state!r}")
    payload = {"state": state, "context": context,
               "description": description[:140]}
    if target_url:
        payload["target_url"] = target_url
    api(f"statuses/{sha}", method="POST", payload=payload,
        mutation=True, idempotent=True)


def latest_statuses(sha: str) -> dict[str, dict]:
    """Latest status per context on *sha* (rows arrive newest-first)."""
    rows = api(f"commits/{sha}/statuses", paginate=True)
    latest: dict[str, dict] = {}
    for row in rows:
        context = row.get("context") or ""
        if context and context not in latest:
            latest[context] = {"state": row.get("state"),
                               "description": row.get("description") or "",
                               "created_at": row.get("created_at") or ""}
    return latest


# ---------------------------------------------------------------------------
# Pull requests
# ---------------------------------------------------------------------------

def pr_view(number: int) -> dict:
    return api(f"pulls/{number}")


def pr_for_branch(branch: str) -> dict | None:
    """The unique open PR whose head is *branch*, or None."""
    owner = repo_slug().split("/")[0]
    rows = api(f"pulls?state=open&head={owner}:{branch}", paginate=True)
    if len(rows) > 1:
        raise LayerError(f"multiple open PRs for head {branch!r}")
    return rows[0] if rows else None


def ensure_pr_comment(number: int, marker: str, body: str) -> int:
    """Create or update the single PR comment carrying *marker*.

    The marker (an HTML comment) is the idempotency key: an existing comment
    is PATCHed in place; after an ambiguous POST failure the list is re-read
    and an adopted comment is not re-posted.
    """
    full = _marked_body(marker, body)
    existing = _find_comment(number, marker)
    if existing is not None:
        api(f"issues/comments/{existing}", method="PATCH",
            payload={"body": full}, mutation=True, idempotent=True)
        return existing
    try:
        created = api(f"issues/{number}/comments", method="POST",
                      payload={"body": full}, mutation=True)
        return int(created["id"])
    except LayerError:
        adopted = _find_comment(number, marker)
        if adopted is not None:
            return adopted
        raise


def _find_comment(number: int, marker: str) -> int | None:
    for row in api(f"issues/{number}/comments", paginate=True):
        if marker in (row.get("body") or ""):
            return int(row["id"])
    return None


def _marked_body(marker: str, body: str) -> str:
    if len(body) > COMMENT_BODY_LIMIT:
        body = body[:COMMENT_BODY_LIMIT] + "\n\n*(truncated; the full text is in runtime storage / telemetry)*"
    return f"{marker}\n{body}"


def post_review(number: int, commit_id: str, marker: str, body: str) -> str:
    """Post one COMMENT review bound to *commit_id*; marker-idempotent.

    Single-account repos cannot self-APPROVE, so every local verdict is a
    COMMENT review; adverseness travels in the ``local-review/summary`` status,
    not in a review state.  Returns ``"exists"`` or the new review id.
    """
    for row in api(f"pulls/{number}/reviews", paginate=True):
        if row.get("commit_id") == commit_id and marker in (row.get("body") or ""):
            return "exists"
    payload = {"commit_id": commit_id, "event": "COMMENT",
               "body": _marked_body(marker, body)}
    try:
        created = api(f"pulls/{number}/reviews", method="POST",
                      payload=payload, mutation=True)
        return str(created.get("id"))
    except LayerError:
        for row in api(f"pulls/{number}/reviews", paginate=True):
            if row.get("commit_id") == commit_id and marker in (row.get("body") or ""):
                return "adopted"
        raise


def pr_reviews(number: int) -> list[dict]:
    return api(f"pulls/{number}/reviews", paginate=True)


def merge_pr(number: int, sha: str) -> str:
    """Merge PR *number* iff its head is exactly *sha*; verify topology.

    The REST ``sha`` parameter makes GitHub reject the merge when the head
    moved — the atomic exact-head guard, independent of the gh CLI version.
    Returns the merge commit SHA after verifying it has exactly two parents
    with the frozen head second.
    """
    put_error = ""
    try:
        api(f"pulls/{number}/merge", method="PUT",
            payload={"sha": sha, "merge_method": "merge"}, mutation=True)
    except LayerError as exc:
        put_error = str(exc)  # fall through: the read-back below is the authority
    pr = pr_view(number)
    if not pr.get("merged"):
        state = pr.get("state")
        head = (pr.get("head") or {}).get("sha")
        detail = f"; merge call said: {put_error[:400]}" if put_error else ""
        raise LayerError(
            f"PR #{number} did not merge (state={state}, head={head}, "
            f"expected {sha}){detail}")
    merge_commit = pr.get("merge_commit_sha") or ""
    commit = api(f"commits/{merge_commit}")
    parents = [p.get("sha") for p in commit.get("parents") or []]
    if len(parents) != 2 or parents[1] != sha:
        raise LayerError(
            f"PR #{number} merge commit {merge_commit} has parents {parents}; "
            f"expected two with head {sha} second — someone else merged?")
    return merge_commit


# ---------------------------------------------------------------------------
# Issues
# ---------------------------------------------------------------------------

def list_labels() -> list[str]:
    return [row["name"] for row in api("labels", paginate=True)]


def issue_view(number: int) -> dict:
    return api(f"issues/{number}")


def issue_create(title: str, body: str, labels: tuple[str, ...] = (),
                 parent: int | None = None, key: str | None = None) -> int:
    """Create an issue; validate labels; optionally link as a sub-issue.

    With *key*, a ``<!-- mipstarre-issue-key: ... -->`` marker is embedded and
    an ambiguous create failure adopts the existing issue instead of
    duplicating it.
    """
    check_bracket_free(title, "issue title")
    if labels:
        known = set(list_labels())
        missing = sorted(set(labels) - known)
        if missing:
            raise LayerError(
                f"labels not in the repository: {missing} — create them on "
                f"GitHub first (gh label create) or drop them")
    marker = f"<!-- mipstarre-issue-key: {key} -->" if key else None
    full_body = f"{marker}\n{body}" if marker else body
    # Adoption never returns early: the parent link below must run even when the
    # issue already exists (a prior run may have died between create and link).
    number = _find_issue_by_marker(marker) if marker else None
    if number is None:
        payload: dict = {"title": title, "body": full_body}
        if labels:
            payload["labels"] = list(labels)
        try:
            created = api("issues", method="POST", payload=payload, mutation=True)
            number = int(created["number"])
        except LayerError:
            if marker:
                number = _find_issue_by_marker(marker)
            if number is None:
                raise
    if parent is not None:
        add_sub_issue(parent, number)
    return number


def _find_issue_by_marker(marker: str) -> int | None:
    rows = api(f"issues?state=all&per_page={PAGE}&sort=created&direction=desc")
    for row in rows or []:
        if "pull_request" in row:
            continue
        if marker in (row.get("body") or ""):
            return int(row["number"])
    return None


def add_sub_issue(parent: int, child: int) -> None:
    child_id = issue_view(child)["id"]
    try:
        api(f"issues/{parent}/sub_issues", method="POST",
            payload={"sub_issue_id": child_id}, mutation=True)
    except LayerError as exc:
        # Re-linking an existing child is a 422; adopt it.
        for row in api(f"issues/{parent}/sub_issues", paginate=True):
            if int(row.get("number", -1)) == child:
                return
        raise exc


def open_sub_issues(number: int) -> list[int]:
    rows = api(f"issues/{number}/sub_issues", paginate=True)
    return [int(r["number"]) for r in rows if r.get("state") == "open"]


def issue_close(number: int, reason: str = "completed",
                comment: str | None = None) -> None:
    if reason not in ("completed", "not-planned"):
        raise LayerError(f"invalid close reason {reason!r}")
    if comment:
        ensure_pr_comment(number, f"<!-- mipstarre-close-note-{number} -->", comment)
    api(f"issues/{number}", method="PATCH",
        payload={"state": "closed",
                 "state_reason": "not_planned" if reason == "not-planned" else reason},
        mutation=True, idempotent=True)


# ---------------------------------------------------------------------------
# Read-only snapshot (audit/recovery telemetry — never lifecycle input)
# ---------------------------------------------------------------------------

def snapshot(out_dir: Path) -> None:
    issues = [r for r in api("issues?state=open", paginate=True)
              if "pull_request" not in r]
    pulls = api("pulls?state=open", paginate=True)
    meta = {"generated": utcnow(), "repo": repo_slug(),
            "open_issues": len(issues), "open_pulls": len(pulls)}
    out = Path(out_dir)
    atomic_write(out / "open-issues.json", json.dumps(issues, indent=1) + "\n")
    atomic_write(out / "open-pulls.json", json.dumps(pulls, indent=1) + "\n")
    atomic_write(out / "metadata.json", json.dumps(meta, indent=1) + "\n")


# ---------------------------------------------------------------------------
# CLI — the shell scripts' entry point
# ---------------------------------------------------------------------------

def _emit(value) -> None:
    if value is None:
        return
    if isinstance(value, (dict, list)):
        json.dump(value, sys.stdout, indent=1)
        sys.stdout.write("\n")
    else:
        sys.stdout.write(f"{value}\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("pr-view"); p.add_argument("number", type=int)
    p = sub.add_parser("pr-for-branch"); p.add_argument("branch")
    p = sub.add_parser("post-status")
    p.add_argument("sha"); p.add_argument("context"); p.add_argument("state")
    p.add_argument("--desc", default=""); p.add_argument("--target-url")
    p = sub.add_parser("latest-statuses"); p.add_argument("sha")
    p = sub.add_parser("ensure-pr-comment")
    p.add_argument("number", type=int); p.add_argument("marker")
    p.add_argument("--body-file", required=True)
    p = sub.add_parser("post-review")
    p.add_argument("number", type=int); p.add_argument("commit_id")
    p.add_argument("marker"); p.add_argument("--body-file", required=True)
    p = sub.add_parser("pr-reviews"); p.add_argument("number", type=int)
    p = sub.add_parser("merge-pr")
    p.add_argument("number", type=int); p.add_argument("sha")
    p = sub.add_parser("issue-view"); p.add_argument("number", type=int)
    p = sub.add_parser("issue-create")
    p.add_argument("--title", required=True)
    p.add_argument("--body-file", required=True)
    p.add_argument("--label", action="append", default=[])
    p.add_argument("--parent", type=int)
    p.add_argument("--key")
    p = sub.add_parser("issue-close")
    p.add_argument("number", type=int)
    p.add_argument("--reason", default="completed")
    p.add_argument("--comment")
    p = sub.add_parser("open-sub-issues"); p.add_argument("number", type=int)
    p = sub.add_parser("list-labels")
    p = sub.add_parser("snapshot"); p.add_argument("--out-dir", required=True)
    p = sub.add_parser("repo-slug")

    args = parser.parse_args(argv)
    try:
        if args.cmd == "pr-view":
            _emit(pr_view(args.number))
        elif args.cmd == "pr-for-branch":
            _emit(pr_for_branch(args.branch))
        elif args.cmd == "post-status":
            post_status(args.sha, args.context, args.state,
                        description=args.desc, target_url=args.target_url)
        elif args.cmd == "latest-statuses":
            _emit(latest_statuses(args.sha))
        elif args.cmd == "ensure-pr-comment":
            _emit(ensure_pr_comment(args.number, args.marker,
                                    Path(args.body_file).read_text(encoding="utf-8")))
        elif args.cmd == "post-review":
            _emit(post_review(args.number, args.commit_id, args.marker,
                              Path(args.body_file).read_text(encoding="utf-8")))
        elif args.cmd == "pr-reviews":
            _emit(pr_reviews(args.number))
        elif args.cmd == "merge-pr":
            _emit(merge_pr(args.number, args.sha))
        elif args.cmd == "issue-view":
            _emit(issue_view(args.number))
        elif args.cmd == "issue-create":
            _emit(issue_create(args.title,
                               Path(args.body_file).read_text(encoding="utf-8"),
                               labels=tuple(args.label), parent=args.parent,
                               key=args.key))
        elif args.cmd == "issue-close":
            issue_close(args.number, reason=args.reason, comment=args.comment)
        elif args.cmd == "open-sub-issues":
            _emit(open_sub_issues(args.number))
        elif args.cmd == "list-labels":
            _emit(list_labels())
        elif args.cmd == "snapshot":
            snapshot(Path(args.out_dir))
        elif args.cmd == "repo-slug":
            _emit(repo_slug())
    except LayerError as exc:
        sys.stderr.write(f"error: {exc}\n")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
