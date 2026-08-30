#!/usr/bin/env python3
"""Tracking bookkeeping for the local issue tree — a deterministic port.

Replaces the ``track`` job of ``.github/workflows/issue-automation.yml``
(:335-572), which the parent repository had already demoted from an LLM agent to
a script: "track/followups replace the tracking-issue-sync.yml agent: the
bookkeeping half is mechanical and now runs as a script"
(issue-automation.yml:18-21).  This file finishes that demotion — the half that
was mechanical on GitHub is mechanical here too, with no network and no model.

Three GitHub facilities disappear and are replaced by file-tree equivalents:

* native sub-issues (one parent per issue, GraphQL ``subIssues``) become the
  ``parent`` / ``children`` frontmatter fields, validated by
  ``local/bin/validate_tree.py``;
* issue comments become marker-deduplicated bullets under a ``## Activity``
  heading in the issue file;
* webhook delivery becomes explicit invocation from ``issue_close.py``,
  ``pr_open.py`` and ``pr_merge.py``.

The last substitution is why ``comment_once`` matters more here than on GitHub.
The parent added it as a replay defense — "Post at most once: skip when any
existing comment contains the marker (guards against redelivered events and
re-runs)" (issue-automation.yml:403-404).  Locally, re-running a command is the
normal way to use it, so without the marker check the tree would fill with
duplicates within a day.

This module doubles as the data layer for the rest of ``local/bin``: the YAML
subset reader/writer, the atomic-rename mutation helper, the per-entity advisory
locks, and the issue/PR record types all live here and are imported by the
sibling scripts.  Nothing outside ``local/bin`` may import it.

Usage:
    track.py --issue-closed 0042
    track.py --issue-reopened 0042
    track.py --pr-opened 0007
    track.py --pr-merged 0007 [--exclude-issue 0042 ...]
    track.py --check            # parse the whole tree and report nothing else
"""

from __future__ import annotations

import argparse
import errno
import fcntl
import os
import re
import sys
import tempfile
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Iterator, Sequence


# ---------------------------------------------------------------------------
# Locations
# ---------------------------------------------------------------------------

#: Runtime state (locks, caches) never lives in the repository — DESIGN.md:37.
CACHE_ROOT = Path(os.environ.get("MIPSTARRE_CACHE_ROOT", "~/.cache/mipstarre-dev"))

ISSUE_ID_RE = re.compile(r"^\d{4,}$")
ISSUE_FILE_RE = re.compile(r"^(\d{4,})-([a-z0-9][a-z0-9-]*)\.md$")

#: Characters banned from titles.  docs/CONTRIBUTING.md:122-124 names exactly
#: this pair: bracketed prefixes leak into bot-generated branch names and ``]``
#: breaks part of the PR automation stack.  A title may still contain ``:``
#: ("Tracking: ..." is the documented idiom, and the classifier keys on it).
FORBIDDEN_TITLE_CHARS = "[]"

#: Characters banned from branch names: the pair above plus the git refname
#: metacharacters, which ``git check-ref-format`` rejects for the same
#: structural reason — a name that travels through shell, path and regex
#: contexts must survive all three.
FORBIDDEN_REF_CHARS = "[]~^:?*\\ \t"


def default_repo_root() -> Path:
    """Repository root, assuming this file stays at ``local/bin/track.py``."""
    return Path(__file__).resolve().parents[2]


def cache_root() -> Path:
    return CACHE_ROOT.expanduser()


def lock_dir() -> Path:
    return cache_root() / "locks"


def utcnow() -> str:
    """Timestamp format used by every frontmatter ``created``/``updated``."""
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class LayerError(RuntimeError):
    """Operator-facing failure: printed without a traceback by ``main``."""


# ---------------------------------------------------------------------------
# Untrusted-text sanitization
# ---------------------------------------------------------------------------

_CONTROL_RE = re.compile(r"[\u0000-\u0008\u000B\u000C\u000E-\u001F\u007F]")

#: Truncation limits copied from the parent's sanitize step
#: (issue-automation.yml:124-128): title 200, body 5000.
TITLE_LIMIT = 200
BODY_LIMIT = 5000


def sanitize(text: str | None, limit: int | None = None) -> str:
    """Strip control characters, break ``` fences, optionally truncate.

    Verbatim port of the ``Sanitize issue content`` step at
    ``.github/workflows/issue-automation.yml:122-128``.  Issue and PR text is
    untrusted even when it originates locally: it is echoed into generated
    markdown and, once the LLM hooks below are wired, into agent prompts
    (DESIGN.md invariant 6).  Fence-breaking inserts zero-width spaces so a
    body cannot close a fenced block that frames it as data.
    """
    cleaned = _CONTROL_RE.sub("", text or "")
    cleaned = cleaned.replace("```", "\u200b`\u200b`\u200b`")
    if limit is not None:
        cleaned = cleaned[:limit]
    return cleaned


def check_bracket_free(value: str, what: str, chars: str = FORBIDDEN_TITLE_CHARS) -> None:
    """Raise when *value* carries a character that breaks name propagation.

    docs/CONTRIBUTING.md:122-124: "Avoid prefixes like ``[Chapter 9] ...``:
    bot-generated branch names inherit those characters, and ``]`` breaks part
    of the PR automation stack."  The local convention derives slugs and branch
    names from titles mechanically, so the rule is enforced at the point of
    creation rather than left to reviewer discipline.
    """
    bad = sorted({c for c in value if c in chars})
    if bad:
        rendered = " ".join(repr(c) for c in bad)
        raise LayerError(
            f"{what} contains reserved character(s) {rendered}: {value!r}\n"
            "Bracketed prefixes leak into branch names and break name-derived "
            "automation (docs/CONTRIBUTING.md:122-124). Rewrite the text, e.g. "
            "'Chapter 9 - finish the sandwich-chain corollaries'."
        )


def slugify(title: str, max_words: int = 8) -> str:
    """Lowercase, hyphenated, bracket-free slug derived from a title."""
    lowered = title.lower()
    words = [w for w in re.split(r"[^a-z0-9]+", lowered) if w]
    if not words:
        raise LayerError(f"title {title!r} yields an empty slug; use words a-z0-9")
    slug = "-".join(words[:max_words])[:60].strip("-")
    if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", slug):
        raise LayerError(f"derived slug {slug!r} is not bracket-free lowercase-kebab")
    return slug


# ---------------------------------------------------------------------------
# Advisory locking
# ---------------------------------------------------------------------------

_HELD: dict[str, int] = {}


@contextmanager
def file_lock(name: str, *, timeout_note: str | None = None) -> Iterator[None]:
    """Exclusive advisory lock under ``~/.cache/mipstarre-dev/locks/<name>``.

    GitHub serialized concurrent handlers with per-entity concurrency groups and
    ``cancel-in-progress: false`` (issue-automation.yml:29-31 explains why the
    groups are per-cause: "an opened-issue run and the label events that
    classification fires moments later must not cancel one another").  Locally
    the analogous hazard is two agent sessions mutating the same issue file;
    a per-entity ``flock`` plus the atomic writer below covers it.

    Re-entrant within one process so a caller may hold an issue lock while a
    helper re-acquires it.
    """
    if _HELD.get(name):
        _HELD[name] += 1
        try:
            yield
        finally:
            _HELD[name] -= 1
        return

    directory = lock_dir()
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}.lock"
    fd = os.open(str(path), os.O_CREAT | os.O_RDWR, 0o644)
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            if exc.errno not in (errno.EAGAIN, errno.EACCES):
                raise
            sys.stderr.write(f"waiting for lock {path} ...\n")
            fcntl.flock(fd, fcntl.LOCK_EX)
        os.ftruncate(fd, 0)
        os.write(fd, f"{os.getpid()}\n".encode())
        _HELD[name] = 1
        try:
            yield
        finally:
            _HELD.pop(name, None)
            fcntl.flock(fd, fcntl.LOCK_UN)
    finally:
        os.close(fd)


def issue_lock(issue_id: str):
    return file_lock(f"issue-{issue_id}")


def pr_lock(pr_id: str):
    return file_lock(f"pr-{pr_id}")


# ---------------------------------------------------------------------------
# Atomic writes
# ---------------------------------------------------------------------------

def atomic_write(path: Path, text: str) -> None:
    """Write *text* to *path* via tempfile + ``os.replace``.

    Every frontmatter mutation goes through here.  A half-written issue file is
    worse than a lost one: the tree is the only record of parent/child structure
    and there is no server to reconstruct it.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), prefix=f".{path.name}.", suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise
    dir_fd = os.open(str(path.parent), os.O_RDONLY)
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


# ---------------------------------------------------------------------------
# A deliberately small YAML subset
# ---------------------------------------------------------------------------
#
# Scope: scalars (string / int / bool / null), ``[a, b]`` flow sequences, block
# sequences of scalars or of mappings, two-space indentation, full-line ``#``
# comments.  Everything this layer writes stays inside that subset, and
# labels.yml is authored to match.  Anything richer should be rejected loudly
# rather than half-understood.

_KEY_RE = re.compile(r"^(?P<key>[A-Za-z0-9_][A-Za-z0-9_.\- ]*):(?:[ \t]+(?P<val>.*))?$")


def _parse_scalar(raw: str | None) -> object:
    if raw is None:
        return None
    text = raw.strip()
    if text == "" or text in {"null", "~"}:
        return None
    if text in {"true", "True"}:
        return True
    if text in {"false", "False"}:
        return False
    if text.startswith("[") and text.endswith("]"):
        return _parse_flow_list(text[1:-1])
    if len(text) >= 2 and text[0] == text[-1] and text[0] in "\"'":
        return _unquote(text)
    if re.fullmatch(r"-?\d+", text):
        return int(text)
    return text


def _unquote(text: str) -> str:
    quote = text[0]
    inner = text[1:-1]
    if quote == "'":
        return inner.replace("''", "'")
    out: list[str] = []
    escaped = False
    for ch in inner:
        if escaped:
            out.append({"n": "\n", "t": "\t"}.get(ch, ch))
            escaped = False
        elif ch == "\\":
            escaped = True
        else:
            out.append(ch)
    return "".join(out)


def _parse_flow_list(inner: str) -> list[object]:
    items: list[object] = []
    buf: list[str] = []
    quote: str | None = None
    escaped = False
    for ch in inner:
        if escaped:
            buf.append(ch)
            escaped = False
            continue
        if quote:
            buf.append(ch)
            if ch == "\\" and quote == '"':
                escaped = True
            elif ch == quote:
                quote = None
            continue
        if ch in "\"'":
            quote = ch
            buf.append(ch)
            continue
        if ch == ",":
            items.append("".join(buf))
            buf = []
            continue
        buf.append(ch)
    if "".join(buf).strip():
        items.append("".join(buf))
    return [_parse_scalar(item) for item in items if item.strip() != ""]


def _significant(lines: Sequence[str]) -> list[tuple[int, str, int]]:
    """(indent, text, source_line_number) for non-blank, non-comment lines."""
    out: list[tuple[int, str, int]] = []
    for number, line in enumerate(lines, start=1):
        if "\t" in line[: len(line) - len(line.lstrip())]:
            raise LayerError(f"line {number}: tab indentation is not supported")
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        out.append((len(line) - len(line.lstrip(" ")), stripped, number))
    return out


def _parse_block(rows: list[tuple[int, str, int]], index: int, indent: int) -> tuple[object, int]:
    if index >= len(rows):
        return None, index
    if rows[index][1].startswith("- "):
        return _parse_sequence(rows, index, indent)
    return _parse_mapping(rows, index, indent)


def _parse_mapping(rows, index: int, indent: int) -> tuple[dict, int]:
    result: dict[str, object] = {}
    while index < len(rows):
        level, text, number = rows[index]
        if level < indent:
            break
        if level > indent:
            raise LayerError(f"line {number}: unexpected indentation in mapping")
        match = _KEY_RE.match(text)
        if not match:
            raise LayerError(f"line {number}: not a supported mapping entry: {text!r}")
        key = match.group("key").strip()
        raw = match.group("val")
        index += 1
        if raw is None or raw.strip() == "":
            if index < len(rows) and rows[index][0] > indent:
                value, index = _parse_block(rows, index, rows[index][0])
            elif index < len(rows) and rows[index][0] == indent and rows[index][1].startswith("- "):
                value, index = _parse_sequence(rows, index, indent)
            else:
                value = None
        else:
            value = _parse_scalar(raw)
        result[key] = value
    return result, index


def _parse_sequence(rows, index: int, indent: int) -> tuple[list, int]:
    items: list[object] = []
    while index < len(rows):
        level, text, number = rows[index]
        if level < indent or not text.startswith("- "):
            break
        if level > indent:
            raise LayerError(f"line {number}: unexpected indentation in sequence")
        payload = text[2:].strip()
        index += 1
        if _KEY_RE.match(payload):
            child_indent = level + 2
            sub_rows: list[tuple[int, str, int]] = [(child_indent, payload, number)]
            while index < len(rows) and rows[index][0] >= child_indent and not (
                rows[index][0] == level and rows[index][1].startswith("- ")
            ):
                if rows[index][0] < child_indent:
                    break
                sub_rows.append((child_indent, rows[index][1], rows[index][2])
                                if rows[index][0] == child_indent else rows[index])
                index += 1
            mapping, _ = _parse_mapping(sub_rows, 0, child_indent)
            items.append(mapping)
        else:
            items.append(_parse_scalar(payload))
    return items, index


def parse_yaml_subset(text: str) -> dict:
    rows = _significant(text.splitlines())
    if not rows:
        return {}
    value, _ = _parse_mapping(rows, 0, rows[0][0])
    return value


def _emit_scalar(value: object) -> str:
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, (list, tuple)):
        return "[" + ", ".join(_emit_scalar(v) for v in value) + "]"
    escaped = str(value).replace("\\", "\\\\").replace('"', '\\"')
    escaped = escaped.replace("\n", "\\n").replace("\r", "")
    return f'"{escaped}"'


def dump_frontmatter(meta: dict, order: Sequence[str]) -> str:
    """Serialize *meta* in *order*; unknown keys follow, sorted, for visibility."""
    keys = list(order) + sorted(k for k in meta if k not in order)
    lines = ["---"]
    for key in keys:
        if key not in meta:
            continue
        lines.append(f"{key}: {_emit_scalar(meta[key])}")
    lines.append("---")
    return "\n".join(lines) + "\n"


def split_frontmatter(text: str) -> tuple[dict, str]:
    """Return ``(frontmatter, body)``; raises when the fence is missing."""
    if not text.startswith("---"):
        raise LayerError("file does not start with a '---' frontmatter fence")
    lines = text.splitlines()
    end = None
    for number in range(1, len(lines)):
        if lines[number].strip() == "---":
            end = number
            break
    if end is None:
        raise LayerError("unterminated frontmatter: no closing '---'")
    meta = parse_yaml_subset("\n".join(lines[1:end]))
    body = "\n".join(lines[end + 1:])
    return meta, body.lstrip("\n")


# ---------------------------------------------------------------------------
# Label taxonomy
# ---------------------------------------------------------------------------

class Taxonomy:
    """Parsed ``local/labels.yml``: the local replacement for ``gh label list``."""

    def __init__(self, names: list[str], entries: list[dict], banned: dict[str, str]):
        self.names = names
        self.entries = entries
        self.banned = banned

    def __contains__(self, name: object) -> bool:
        return name in self.names

    def aliases_by_label(self) -> dict[str, list[str]]:
        out: dict[str, list[str]] = {}
        for entry in self.entries:
            aliases = entry.get("aliases") or []
            if isinstance(aliases, list) and aliases:
                out[str(entry["name"])] = [str(a).lower() for a in aliases]
        return out

    def by_category(self, category: str) -> list[str]:
        return [str(e["name"]) for e in self.entries if e.get("category") == category]


def load_taxonomy(repo_root: Path) -> Taxonomy:
    path = repo_root / "local" / "labels.yml"
    if not path.is_file():
        raise LayerError(
            f"label taxonomy not found at {path}. It is the local source of truth "
            "for labels (replacing 'GitHub is the source of truth', "
            "docs/CONTRIBUTING.md:286-289) and is required before any issue may "
            "be created or validated."
        )
    data = parse_yaml_subset(path.read_text(encoding="utf-8"))
    entries = data.get("labels") or []
    if not isinstance(entries, list) or not entries:
        raise LayerError(f"{path}: 'labels:' must be a non-empty block sequence")
    names: list[str] = []
    for entry in entries:
        if not isinstance(entry, dict) or "name" not in entry:
            raise LayerError(f"{path}: every label entry needs a 'name' key")
        names.append(str(entry["name"]))
    banned = {}
    for entry in data.get("banned") or []:
        if isinstance(entry, dict) and "name" in entry:
            banned[str(entry["name"])] = str(entry.get("reason", "banned"))
    return Taxonomy(names, [e for e in entries if isinstance(e, dict)], banned)


# ---------------------------------------------------------------------------
# Issue records
# ---------------------------------------------------------------------------

#: Frontmatter field order, fixed by DESIGN.md:97-100.
ISSUE_FIELDS = (
    "id", "title", "state", "state_reason", "parent", "children",
    "labels", "pinned", "created", "updated", "agent_session",
)

#: Frontmatter field order, fixed by DESIGN.md:101-105.
PR_FIELDS = (
    "id", "branch", "issue", "base", "state", "head_sha", "ci_status",
    "review_state", "fix_iterations", "auto_fix", "labels", "created",
    "merged_commit",
)

ACTIVITY_HEADING = "## Activity"


class Record:
    """A markdown file with YAML frontmatter."""

    fields: Sequence[str] = ()

    def __init__(self, path: Path, meta: dict, body: str):
        self.path = path
        self.meta = meta
        self.body = body

    @property
    def id(self) -> str:
        return str(self.meta.get("id", ""))

    @property
    def title(self) -> str:
        return str(self.meta.get("title", ""))

    @property
    def state(self) -> str:
        return str(self.meta.get("state", ""))

    @property
    def labels(self) -> list[str]:
        value = self.meta.get("labels") or []
        return [str(v) for v in value] if isinstance(value, list) else []

    def render(self) -> str:
        body = self.body.rstrip("\n")
        return dump_frontmatter(self.meta, self.fields) + "\n" + body + "\n"

    def save(self) -> None:
        self.meta["updated"] = utcnow()
        atomic_write(self.path, self.render())


class Issue(Record):
    fields = ISSUE_FIELDS

    @property
    def parent(self) -> str | None:
        value = self.meta.get("parent")
        if value in (None, "", "null"):
            return None
        if isinstance(value, list):
            raise LayerError(
                f"issue {self.id}: 'parent' is a list. An issue has at most one "
                "parent (GitHub's native sub-issue invariant, preserved here)."
            )
        return str(value)

    @property
    def children(self) -> list[str]:
        value = self.meta.get("children") or []
        return [str(v) for v in value] if isinstance(value, list) else []

    @property
    def state_reason(self) -> str | None:
        value = self.meta.get("state_reason")
        return None if value in (None, "", "null") else str(value)

    @property
    def is_resolved(self) -> bool:
        """Closed *and* completed.

        The parent counted any ``state === 'CLOSED'`` sub-issue as progress
        (issue-automation.yml:378-400).  Locally a not-planned close must not
        advance the tracking count, so resolution requires the reason too; the
        ``[closed/total]`` figures below are counts of *resolved* children.
        """
        return self.state == "closed" and self.state_reason == "completed"


class PullRequest(Record):
    fields = PR_FIELDS

    @property
    def title(self) -> str:
        """First ``# `` heading of the body, else the record directory name.

        DESIGN.md:101-105 fixes the PR frontmatter fields, and ``title`` is not
        among them, so the title lives in the body as its H1 — where a reader
        sees it first and where the Motivation/Description/Testing skeleton
        required by docs/CONTRIBUTING.md:36-58 still follows unchanged.
        """
        for line in self.body.splitlines():
            if line.startswith("# "):
                return line[2:].strip()
        return self.path.parent.name

    @property
    def branch(self) -> str:
        return str(self.meta.get("branch", ""))

    @property
    def issue(self) -> str | None:
        value = self.meta.get("issue")
        return None if value in (None, "", "null") else str(value)


def issues_dir(repo_root: Path) -> Path:
    return repo_root / "issues"


def prs_dir(repo_root: Path) -> Path:
    return repo_root / "prs"


def normalize_id(value: str | int) -> str:
    text = str(value).strip().lstrip("#")
    if not text.isdigit():
        raise LayerError(f"{value!r} is not a numeric id")
    return f"{int(text):04d}"


def issue_path(repo_root: Path, issue_id: str) -> Path:
    directory = issues_dir(repo_root)
    if not directory.is_dir():
        raise LayerError(
            f"issue tree not found at {directory}. Create the first issue with "
            "local/bin/issue_new.py before running tracking commands."
        )
    matches = sorted(directory.glob(f"{normalize_id(issue_id)}-*.md"))
    if not matches:
        raise LayerError(f"no issue file for #{normalize_id(issue_id)} under {directory}")
    if len(matches) > 1:
        raise LayerError(
            f"#{normalize_id(issue_id)} has {len(matches)} files: "
            + ", ".join(p.name for p in matches)
        )
    return matches[0]


def load_issue(repo_root: Path, issue_id: str) -> Issue:
    path = issue_path(repo_root, issue_id)
    meta, body = split_frontmatter(path.read_text(encoding="utf-8"))
    return Issue(path, meta, body)


def try_load_issue(repo_root: Path, issue_id: str) -> Issue | None:
    try:
        return load_issue(repo_root, issue_id)
    except LayerError:
        return None


def iter_issues(repo_root: Path, *, include_standup: bool = False) -> Iterator[Issue]:
    """Yield issue records, ordered by id.

    ``issues/standup/`` is excluded by default.  Standup digests are written by
    automation from the activity feed; feeding them back in reproduces the
    self-reference that GitHub avoided with ``-label:standup`` search filters
    (housekeeping.yml:85-95).
    """
    directory = issues_dir(repo_root)
    if not directory.is_dir():
        return
    paths = sorted(directory.glob("*.md"))
    if include_standup and (directory / "standup").is_dir():
        paths += sorted((directory / "standup").glob("*.md"))
    for path in paths:
        try:
            meta, body = split_frontmatter(path.read_text(encoding="utf-8"))
        except LayerError as exc:
            raise LayerError(f"{path}: {exc}") from exc
        yield Issue(path, meta, body)


def pr_path(repo_root: Path, pr_id: str) -> Path:
    directory = prs_dir(repo_root)
    if not directory.is_dir():
        raise LayerError(
            f"PR registry not found at {directory}. Open a PR record with "
            "local/bin/pr_open.py first."
        )
    matches = sorted(directory.glob(f"{normalize_id(pr_id)}-*/pr.md"))
    if not matches:
        raise LayerError(f"no PR record for PR #{normalize_id(pr_id)} under {directory}")
    if len(matches) > 1:
        raise LayerError(f"PR #{normalize_id(pr_id)} has {len(matches)} records")
    return matches[0]


def load_pr(repo_root: Path, pr_id: str) -> PullRequest:
    path = pr_path(repo_root, pr_id)
    meta, body = split_frontmatter(path.read_text(encoding="utf-8"))
    return PullRequest(path, meta, body)


def iter_prs(repo_root: Path) -> Iterator[PullRequest]:
    directory = prs_dir(repo_root)
    if not directory.is_dir():
        return
    for path in sorted(directory.glob("*/pr.md")):
        meta, body = split_frontmatter(path.read_text(encoding="utf-8"))
        yield PullRequest(path, meta, body)


def next_sequence_id(seq_path: Path, existing: Iterable[str]) -> str:
    """Allocate the next 4-digit id, atomically.

    The counter file is authoritative but is reconciled against the ids already
    on disk on every allocation: a counter restored from an older commit must
    never hand out an id that is already taken.  Callers hold the sequence lock.
    """
    highest = 0
    for value in existing:
        try:
            highest = max(highest, int(value))
        except (TypeError, ValueError):
            continue
    current = 0
    if seq_path.is_file():
        raw = seq_path.read_text(encoding="utf-8").strip()
        if raw:
            if not raw.isdigit():
                raise LayerError(f"{seq_path}: expected a decimal counter, found {raw!r}")
            current = int(raw)
    allocated = max(current, highest) + 1
    atomic_write(seq_path, f"{allocated}\n")
    return f"{allocated:04d}"


# ---------------------------------------------------------------------------
# commentOnce
# ---------------------------------------------------------------------------

def append_activity_once(issue: Issue, marker: str, note: str, *, dry_run: bool = False) -> bool:
    """Append one ``## Activity`` bullet unless *marker* already appears.

    Direct port of ``commentOnce`` (issue-automation.yml:403-417).  The parent
    scanned every existing comment body for the marker substring; here the whole
    issue file plays that role.  Returns True when the note was written.

    ``## Activity`` is the terminal section of an issue file by convention, so
    the append is a plain end-of-file write and never has to reflow the body.
    """
    with issue_lock(issue.id):
        current = issue.path.read_text(encoding="utf-8")
        if marker in current:
            return False
        meta, body = split_frontmatter(current)
        fresh = Issue(issue.path, meta, body)
        text = fresh.body.rstrip("\n")
        if ACTIVITY_HEADING not in text:
            text += f"\n\n{ACTIVITY_HEADING}\n"
        if text.rstrip("\n").endswith(ACTIVITY_HEADING):
            text = text.rstrip("\n") + "\n"
        text += f"\n- {utcnow()} — {note}"
        fresh.body = text
        if dry_run:
            sys.stdout.write(f"[dry-run] {issue.path.name}: {note}\n")
            return True
        fresh.save()
        issue.meta = fresh.meta
        issue.body = fresh.body
        sys.stdout.write(f"{issue.path.name}: {note}\n")
        return True


# ---------------------------------------------------------------------------
# Tracking computations
# ---------------------------------------------------------------------------

def child_counts(repo_root: Path, parent: Issue) -> tuple[int, int]:
    """``(resolved, total)`` over the parent's declared children."""
    total = 0
    resolved = 0
    for child_id in parent.children:
        child = try_load_issue(repo_root, child_id)
        if child is None:
            sys.stderr.write(
                f"warning: #{parent.id} lists child #{child_id}, which has no file; "
                "run local/bin/validate_tree.py\n"
            )
            continue
        total += 1
        if child.is_resolved:
            resolved += 1
    return resolved, total


def note_if_all_resolved(parent: Issue, resolved: int, total: int, *, dry_run: bool = False) -> None:
    """Port of ``noteIfAllResolved`` (issue-automation.yml:419-425).

    The parent repository deliberately posts a note rather than applying a
    label: "The repository does not currently use a live ``all-resolved``
    label, so do not add one manually" (docs/CONTRIBUTING.md:217-219).  The
    marker is the bare phrase ``ready to close``, exactly as upstream, so a
    hand-written note containing it also suppresses the automated one.
    """
    if total > 0 and resolved == total:
        append_activity_once(
            parent,
            "ready to close",
            "All sub-issues in this tracking issue are complete; the mathematical "
            "scope described here is ready to close.",
            dry_run=dry_run,
        )


_LINK_RE = re.compile(r"\b(closes|fixes|addresses|partially addresses)\s+#(\d+)", re.IGNORECASE)
_BRANCH_ISSUE_RE = re.compile(r"issue-(\d+)")


def linked_issues(pr_body: str, branch: str) -> tuple[list[str], list[str]]:
    """``(keep_open, auto_close)`` — port of ``linkedIssues``.

    issue-automation.yml:453-478.  ``Addresses``/``Partially addresses`` keep an
    issue open; ``Closes``/``Fixes`` auto-close it on merge.  The branch name
    contributes a keep-open link through the ``issue-(\\d+)`` regex, which is
    why DESIGN.md:106-107 fixes the branch convention as
    ``issue-<id>-<slug>`` / ``codex/issue-<id>-<slug>``.

    The upstream comment at issue-automation.yml:450-452 records the reason the
    two sets are disjoint: "Closes/Fixes issues are excluded from progress
    comments: their auto-close fires the issues/closed path, which handles the
    tracking update."  Locally ``pr_merge.py`` performs the auto-close itself
    and then calls the closed path, so the same exclusion prevents a doubled
    note on the tracking parent.
    """
    keep_open: list[str] = []
    auto_close: list[str] = []
    for keyword, number in _LINK_RE.findall(pr_body or ""):
        ident = normalize_id(number)
        if keyword.lower() in {"closes", "fixes"}:
            if ident not in auto_close:
                auto_close.append(ident)
        elif ident not in keep_open:
            keep_open.append(ident)
    match = _BRANCH_ISSUE_RE.search(branch or "")
    if match:
        ident = normalize_id(match.group(1))
        if ident not in auto_close and ident not in keep_open:
            keep_open.append(ident)
    keep_open = [i for i in keep_open if i not in auto_close]
    return keep_open, auto_close


def skip_pr_opened_announcement(branch: str) -> bool:
    """``claude/`` and ``codex/`` branches: PR cleanup owns the announcement.

    issue-automation.yml:480-482 and pr-cleanup.yml:15-22.  ``claude/`` is kept
    alongside ``codex/`` because imported branches from the parent workflow
    still carry it.
    """
    return bool(re.match(r"^(claude|codex)/", branch or ""))


def pr_reference_pattern(pr_id: str) -> re.Pattern[str]:
    """Match textual references to a PR inside an issue title/body.

    Port of ``prReferencePattern`` (issue-automation.yml:428-436).  GitHub gave
    issues and PRs one shared ``#N`` namespace; here they are separate
    sequences, so a bare ``#7`` in an issue body means issue 7.  The local
    spelling of a PR reference is therefore ``PR #0007`` or the path
    ``prs/0007``, and the pattern accepts leading zeros in either form.
    """
    numeric = str(int(pr_id))
    return re.compile(
        rf"(?:^|[^0-9])(?:PR\s*#0*{numeric}|prs/0*{numeric})(?:$|[^0-9])",
        re.IGNORECASE,
    )


def tracking_issues_referencing_pr(repo_root: Path, pr_id: str) -> list[Issue]:
    """Open ``tracking``-labelled issues that mention this PR in prose."""
    pattern = pr_reference_pattern(pr_id)
    found = []
    for issue in iter_issues(repo_root):
        if issue.state != "open" or "tracking" not in issue.labels:
            continue
        if pattern.search(f"{issue.title}\n{issue.body}"):
            found.append(issue)
    return found


class _Targets:
    """Ordered map of tracking parents to the child issues that reached them."""

    def __init__(self) -> None:
        self._data: dict[str, tuple[Issue, list[str]]] = {}

    def add(self, parent: Issue, linked: str | None = None) -> None:
        entry = self._data.setdefault(parent.id, (parent, []))
        if linked is not None and linked not in entry[1]:
            entry[1].append(linked)

    def values(self):
        return list(self._data.values())


def _open_parent(repo_root: Path, issue: Issue) -> Issue | None:
    parent_id = issue.parent
    if parent_id is None:
        return None
    parent = try_load_issue(repo_root, parent_id)
    if parent is None:
        sys.stderr.write(
            f"warning: #{issue.id} names parent #{parent_id}, which has no file; "
            "run local/bin/validate_tree.py\n"
        )
        return None
    return parent


# ---------------------------------------------------------------------------
# Event handlers
# ---------------------------------------------------------------------------

def on_issue_state_change(repo_root: Path, issue_id: str, action: str, *, dry_run: bool) -> int:
    """Port of the ``context.eventName === 'issues'`` branch (:485-508)."""
    issue = load_issue(repo_root, issue_id)
    parent = _open_parent(repo_root, issue)
    if parent is None:
        sys.stdout.write(f"#{issue.id} has no tracking parent; nothing to do.\n")
        return 0
    resolved, total = child_counts(repo_root, parent)
    note_if_all_resolved(parent, resolved, total, dry_run=dry_run)
    if parent.state != "open":
        return 0
    title = sanitize(issue.title, TITLE_LIMIT)
    if action == "closed":
        marker = f"#{issue.id} (*{title}*) is now resolved"
        note = f"{marker}. [{resolved}/{total} sub-issues closed]"
    else:
        marker = f"#{issue.id} (*{title}*) has been reopened"
        note = (
            f"{marker}, so it is again an outstanding part of this tracking issue. "
            f"[{resolved}/{total} sub-issues closed]"
        )
    append_activity_once(parent, marker, note, dry_run=dry_run)
    return 0


def on_pr_opened(repo_root: Path, pr_id: str, *, dry_run: bool) -> int:
    """Port of the ``action === 'opened'`` branch (:520-543)."""
    pr = load_pr(repo_root, pr_id)
    keep_open, auto_close = linked_issues(pr.body, pr.branch)
    referencing = tracking_issues_referencing_pr(repo_root, pr.id)
    if not keep_open and not auto_close and not referencing:
        sys.stdout.write("No linked issues found; nothing to do.\n")
        return 0
    if skip_pr_opened_announcement(pr.branch):
        sys.stdout.write(
            "PR cleanup handles announcements for claude/ and codex/ branches.\n"
        )
        return 0
    targets = _Targets()
    for ident in keep_open + auto_close:
        issue = try_load_issue(repo_root, ident)
        if issue is None:
            sys.stderr.write(f"warning: PR #{pr.id} links #{ident}, which has no file\n")
            continue
        parent = _open_parent(repo_root, issue)
        if parent is not None and parent.state == "open":
            targets.add(parent, ident)
    for issue in referencing:
        targets.add(issue)
    title = sanitize(pr.title, TITLE_LIMIT)
    for parent, linked in targets.values():
        suffix = f" to address #{linked[0]}" if linked else ""
        marker = f"PR #{pr.id} (*{title}*) has been opened"
        append_activity_once(parent, marker, f"{marker}{suffix}.", dry_run=dry_run)
    return 0


def on_pr_merged(
    repo_root: Path,
    pr_id: str,
    *,
    dry_run: bool,
    exclude: Sequence[str] = (),
) -> int:
    """Port of the merged-PR branch (:545-570).

    *exclude* removes issues that ``pr_merge.py`` has already auto-closed: their
    closure fires ``--issue-closed``, which posts the resolution note on the
    parent.  Without the exclusion the parent receives two notes for one child —
    the double-fire the upstream comment at issue-automation.yml:450-452 was
    written to prevent.
    """
    pr = load_pr(repo_root, pr_id)
    keep_open, _auto_close = linked_issues(pr.body, pr.branch)
    excluded = {normalize_id(e) for e in exclude}
    keep_open = [i for i in keep_open if i not in excluded]
    referencing = tracking_issues_referencing_pr(repo_root, pr.id)
    title = sanitize(pr.title, TITLE_LIMIT)
    targets = _Targets()
    for ident in keep_open:
        issue = try_load_issue(repo_root, ident)
        if issue is None:
            sys.stderr.write(f"warning: PR #{pr.id} links #{ident}, which has no file\n")
            continue
        marker = f"PR #{pr.id} (*{title}*) addressing this issue has been merged"
        append_activity_once(
            issue,
            marker,
            f"{marker}. See {pr.path.parent.name}/pr.md for what was accomplished "
            "and what remains.",
            dry_run=dry_run,
        )
        parent = _open_parent(repo_root, issue)
        if parent is not None and parent.state == "open":
            targets.add(parent, ident)
    for issue in referencing:
        targets.add(issue)
    for parent, linked in targets.values():
        resolved, total = child_counts(repo_root, parent)
        note_if_all_resolved(parent, resolved, total, dry_run=dry_run)
        progress = f", making progress on #{linked[0]}" if linked else ""
        marker = f"PR #{pr.id} (*{title}*) has been merged"
        append_activity_once(
            parent,
            marker,
            f"{marker}{progress}. [{resolved}/{total} sub-issues closed]",
            dry_run=dry_run,
        )
    return 0


def check_tree(repo_root: Path) -> int:
    """Parse every record; a cheap syntax gate for callers and for CI."""
    issues = list(iter_issues(repo_root, include_standup=True))
    prs = list(iter_prs(repo_root))
    sys.stdout.write(f"parsed {len(issues)} issue file(s) and {len(prs)} PR record(s)\n")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="track.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--repo-root", type=Path, default=default_repo_root(),
                        help="repository root (default: two levels above this script)")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--issue-closed", metavar="ID",
                       help="an issue was closed as completed")
    group.add_argument("--issue-reopened", metavar="ID",
                       help="an issue was reopened")
    group.add_argument("--pr-opened", metavar="ID", help="a PR record was opened")
    group.add_argument("--pr-merged", metavar="ID", help="a PR record was merged")
    group.add_argument("--check", action="store_true",
                       help="parse the issue and PR trees, then exit")
    parser.add_argument("--exclude-issue", action="append", default=[], metavar="ID",
                        help="with --pr-merged: issue auto-closed by the merge; its "
                             "progress note comes from the closed path instead")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the notes that would be appended, write nothing")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo_root.resolve()
    try:
        if args.check:
            return check_tree(root)
        if args.issue_closed:
            return on_issue_state_change(
                root, normalize_id(args.issue_closed), "closed", dry_run=args.dry_run)
        if args.issue_reopened:
            return on_issue_state_change(
                root, normalize_id(args.issue_reopened), "reopened", dry_run=args.dry_run)
        if args.pr_opened:
            return on_pr_opened(root, normalize_id(args.pr_opened), dry_run=args.dry_run)
        return on_pr_merged(
            root,
            normalize_id(args.pr_merged),
            dry_run=args.dry_run,
            exclude=args.exclude_issue,
        )
    except LayerError as exc:
        sys.stderr.write(f"track.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
