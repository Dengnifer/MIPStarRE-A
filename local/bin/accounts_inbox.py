#!/usr/bin/env python3
"""The owner's GitHub control channel for the live accounts file.

The shell is not always at hand.  A comment on the owner inbox issue in the
fixed form::

    ACCOUNTS: second ceiling=20
    ACCOUNTS: third enabled=false

is applied to ``watchdog/accounts.json`` by the janitor at its next sweep and
answered with one reply saying exactly what took effect::

    applied: second ceiling 30 -> 20
    rejected: ACCOUNTS: fourth ceiling=10 — no account named 'fourth'; the file
    has primary, second, third

Three rules make this safe enough to be a control channel rather than a
conversation:

* **The author must be the repository owner.**  The login is taken from
  ``MIPSTARRE_OWNER_LOGIN``, then from the ``Repository owner login:`` line in
  ``local/README.md``, then from the owner half of the repository slug.  A
  directive from anyone else is never applied; it is answered with a
  ``rejected:`` line naming the author, so an attempt is visible rather than
  silent.
* **One reply per comment, and applying is once.**  Each answered comment gets a
  reply carrying ``<!-- mipstarre-accounts comment=<id> -->``; a comment that
  already has one is skipped entirely, so a sweep every minute does not re-apply
  a ceiling the owner has since changed at the shell.
* **The channel carries ceilings, reserved slots, the enabled flag and a note —
  nothing else.**  An endpoint or a codex home is a path on the owner's host and
  is set with ``owner-tools/accounts.sh``, where a typo cannot travel through a
  public comment.  ``accounts_file.py`` owns the parsing and the validation, so
  this channel and the CLI cannot disagree about what a valid entry is.

Comment bodies are untrusted text (``local/protocols/issues-prs.md`` §4): only
lines matching ``ACCOUNTS:`` are read at all, every value is validated before
anything is written, and nothing is ever interpolated into a shell.

Usage::

    accounts_inbox.py [--issue N] [--dry-run] [--limit N]

Exit codes: 0 (including "nothing to do"), 2 a GitHub or run-mode failure.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import gh_common
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(f"accounts_inbox.py: cannot import gh_common.py ({exc}).\n")
    raise SystemExit(2)

import accounts_file  # noqa: E402
import run_mode  # noqa: E402
from wf_util import LayerError, sanitize  # noqa: E402

MARKER = "mipstarre-accounts"

#: The line ``local/README.md`` carries, and the only thing read from it.
OWNER_LINE_RE = re.compile(
    r"Repository owner login:\s*\**\s*`?([A-Za-z0-9][A-Za-z0-9-]{0,38})`?")

#: How many of the newest comments are looked at at all.  A COUNT bound only;
#: the temporal bound below is the one the staleness rule needs.
DEFAULT_LIMIT = 40

#: Comments older than this are not answered.  A directive the janitor never saw
#: — the daemon was down for a day — is stale capacity advice, and applying it
#: hours later would be worse than ignoring it.  The count cap alone did not
#: implement that rule: the owner inbox issue is permissions-only and low
#: traffic, so far fewer than `DEFAULT_LIMIT` comments exist and every
#: `ACCOUNTS:` comment ever written stayed in scope forever.  With the pipeline
#: deliberately paused, the janitor's first sweep after a resume would have
#: applied the whole backlog at once — including `enabled=false`, which is cap 0
#: and no probe — silently overriding the brief just applied.  Several janitor
#: sweeps wide (daemon.conf `janitor_interval_s` defaults to 900 s), so a
#: directive written while the daemon was briefly down still lands.  The owner
#: sees no reply and can repeat it; ``--max-age-min 0`` turns the bound off.
DEFAULT_MAX_AGE_MIN = 120


def owner_login(repo_root: Path | None = None) -> tuple[str, str]:
    """``(login, where it came from)``.  Never guesses an empty string."""
    override = (os.environ.get("MIPSTARRE_OWNER_LOGIN") or "").strip()
    if override:
        return override, "MIPSTARRE_OWNER_LOGIN"
    readme = (repo_root or run_mode.repo_root()) / "local" / "README.md"
    try:
        match = OWNER_LINE_RE.search(readme.read_text(encoding="utf-8"))
    except OSError:
        match = None
    if match:
        return match.group(1), f"{readme} (Repository owner login:)"
    slug = gh_common.repo_slug()
    return slug.split("/")[0], f"the owner half of the repository slug {slug}"


def comment_age_min(row: dict, now: datetime | None = None) -> float | None:
    """Age of a comment in minutes from its ``created_at``; ``None`` when absent.

    ``None`` — no timestamp, or one that does not parse — is treated as NOT
    stale by `sweep`.  The REST API always supplies ``created_at``, so a missing
    one means an unusual payload rather than an old comment, and refusing to
    answer it would silently drop a directive the owner did write.
    """
    raw = row.get("created_at")
    if not isinstance(raw, str) or not raw.strip():
        return None
    try:
        moment = datetime.fromisoformat(raw.strip().replace("Z", "+00:00"))
    except ValueError:
        return None
    if moment.tzinfo is None:
        moment = moment.replace(tzinfo=timezone.utc)
    return ((now or datetime.now(timezone.utc)) - moment).total_seconds() / 60.0


def reply_marker(comment_id: int) -> str:
    return f"<!-- {MARKER} comment={comment_id} -->"


def already_answered(comments: list[dict], comment_id: int) -> bool:
    marker = reply_marker(comment_id)
    return any(marker in (row.get("body") or "") for row in comments)


#: The local half of "applying is once".  The reply marker lives on GitHub and is
#: written AFTER the accounts file; if that POST fails (rate limit, network, a
#: `LayerError`) the edit is on disk with nothing recording it, and the next
#: sweep re-applies the same directive — reverting any `accounts.sh set` the
#: owner made in between.  This file is written BEFORE the edit, so the failure
#: mode is "applied once, unanswered" (the owner repeats it) instead of "applied
#: again and again".
LEDGER_REL = Path("watchdog") / "capacity" / "inbox-applied.json"
LEDGER_KEEP = 500


def ledger_path(root: Path | None = None) -> Path:
    return (root or accounts_file.cache_root()) / LEDGER_REL


def applied_ids(root: Path | None = None) -> list[int]:
    try:
        document = json.loads(ledger_path(root).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return []
    return [int(value) for value in document.get("applied", [])
            if isinstance(value, int)] if isinstance(document, dict) else []


def record_applied(comment_id: int, root: Path | None = None) -> None:
    """Note the id before the file is written; never fatal, never a duplicate."""
    path = ledger_path(root)
    ids = applied_ids(root)
    if comment_id in ids:
        return
    ids = (ids + [comment_id])[-LEDGER_KEEP:]
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"schema": f"{MARKER}-ledger/1", "applied": ids},
                                   indent=1) + "\n", encoding="utf-8")
    except OSError as exc:
        sys.stderr.write(f"accounts_inbox.py: warning: cannot record {comment_id} "
                         f"in {path}: {exc}; a failed reply could re-apply it\n")


def render_reply(comment_id: int, author: str, results: list[str]) -> str:
    """The owner-facing answer: what was applied, or why it was not."""
    lines = [f"Accounts directive from @{sanitize(author, 40)} "
             f"(comment {comment_id}):", ""]
    lines += [f"- {line}" for line in results]
    lines += ["",
              "<sub>local/bin/accounts_inbox.py, applied to "
              f"{accounts_file.accounts_path()} by local/bin/janitor.sh. "
              "Form: `ACCOUNTS: &lt;name&gt; ceiling=&lt;n&gt; [reserved=&lt;n&gt;] "
              "[enabled=true|false]`, one per line. The live file is the source of "
              "truth for admission; the capacity controller re-reads it every "
              "tick.</sub>"]
    return "\n".join(lines) + "\n"


def sweep(issue: int, *, dry_run: bool = False, limit: int = DEFAULT_LIMIT,
          max_age_min: int = DEFAULT_MAX_AGE_MIN,
          now: datetime | None = None) -> list[str]:
    """Answer every unanswered, recent ``ACCOUNTS:`` comment; the report lines.

    Two bounds, both necessary: `limit` caps how far back the scan goes, and
    `max_age_min` caps how old a directive may be and still be acted on.  A
    stale one is reported in the janitor's line and NOT replied to, so the
    owner's "no reply means it was not applied" rule still holds and a repeat
    comment is answered normally.
    """
    login, source = owner_login()
    comments = gh_common.api(f"issues/{issue}/comments", paginate=True) or []
    applied = set(applied_ids())
    report: list[str] = []
    for row in comments[-limit:]:
        body = row.get("body") or ""
        if MARKER in body:  # one of our own replies
            continue
        directives = accounts_file.parse_directives(body)
        if not directives:
            continue
        comment_id = int(row.get("id") or 0)
        if not comment_id or already_answered(comments, comment_id):
            continue
        if comment_id in applied:
            report.append(f"accounts-inbox: #{issue} comment {comment_id} was already "
                          "applied but its reply did not post; not applying it again")
            continue
        age = comment_age_min(row, now)
        if max_age_min > 0 and age is not None and age > max_age_min:
            report.append(
                f"accounts-inbox: #{issue} comment {comment_id} is {age:.0f} min old "
                f"(bound {max_age_min} min); NOT applied and not answered — capacity "
                "advice this old is worse than none. Repeat it to apply it.")
            continue
        author = str((row.get("user") or {}).get("login") or "")
        if author != login:
            # Reported, never replied to.  A public reply echoing a stranger's
            # text back let anyone with comment access make the bot comment once
            # per comment they wrote.  The author check is the load-bearing part
            # and is unchanged; the attempt is still visible, in the janitor's
            # own report, where the owner reads it.
            report += [
                f"accounts-inbox: #{issue} comment {comment_id} by "
                f"@{sanitize(author, 40) or 'an unknown account'}: ignored — this "
                f"channel applies only the repository owner's comments ({login}, "
                f"from {source}); {record['raw']}"
                for record in directives]
            continue
        if dry_run:
            report.append(f"accounts-inbox: comment {comment_id} by @{author}: "
                          f"{len(directives)} directive(s) would be applied (dry run)")
            continue
        record_applied(comment_id)
        results = accounts_file.apply_directives(
            body, actor=f"github:{author}", origin=f"#{issue} comment {comment_id}")
        gh_common.ensure_pr_comment(issue, reply_marker(comment_id),
                                    render_reply(comment_id, author, results))
        for line in results:
            report.append(f"accounts-inbox: #{issue} comment {comment_id} "
                          f"by @{author}: {line}")
    if not report:
        report.append("accounts-inbox: no new ACCOUNTS: directive")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="accounts_inbox.py", description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--issue", type=int,
                        help="owner inbox issue (default: run_mode.py get owner_inbox_issue)")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                        help=f"newest comments to consider (default {DEFAULT_LIMIT})")
    parser.add_argument("--max-age-min", type=int, default=DEFAULT_MAX_AGE_MIN,
                        help="ignore directives older than this many minutes "
                             f"(default {DEFAULT_MAX_AGE_MIN}; 0 disables the bound)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print what would be applied and replied; write nothing")
    parser.add_argument("--json", action="store_true", help="report as JSON")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    try:
        issue = args.issue
        if issue is None:
            # Not strict about the accounts file: this channel is the owner's
            # REMOTE repair path for that very file, and it must not be dead
            # exactly when a mistyped field needs repairing from a phone.
            issue = int(run_mode.value_for(
                run_mode.load_mode(strict_accounts=False), "owner_inbox_issue"))
        report = sweep(issue, dry_run=args.dry_run, limit=max(1, args.limit),
                       max_age_min=max(0, args.max_age_min))
    except (LayerError, accounts_file.AccountsError, ValueError, OSError) as exc:
        sys.stderr.write(f"accounts_inbox.py: {exc}\n")
        return 2
    if args.json:
        json.dump(report, sys.stdout, indent=1, ensure_ascii=False)
        sys.stdout.write("\n")
    else:
        sys.stdout.write("\n".join(report) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
