#!/usr/bin/env python3
"""Shared non-registry helpers for ``local/bin``.

Extracted verbatim from ``track.py`` when the local issue/PR registry was
retired in favor of GitHub-native records (issue 0007; the registry itself is
archived read-only under ``results/telemetry/registry-archive/``).  Only the
pieces with no registry coupling live here: runtime locations, untrusted-text
sanitization, naming rules, the per-entity advisory lock, and the atomic
writer.  Nothing outside ``local/`` may import this module.
"""

from __future__ import annotations

import errno
import fcntl
import os
import re
import sys
import tempfile
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterator


# ---------------------------------------------------------------------------
# Locations
# ---------------------------------------------------------------------------

#: Runtime state (locks, caches) never lives in the repository — DESIGN.md:37.
CACHE_ROOT = Path(os.environ.get("MIPSTARRE_CACHE_ROOT", "~/.cache/mipstarre-dev"))

#: Characters banned from titles.  docs/CONTRIBUTING.md:122-124 names exactly
#: this pair: bracketed prefixes leak into bot-generated branch names and ``]``
#: breaks part of the PR automation stack.  A title may still contain ``:``
#: ("Tracking: ..." is the documented idiom).
FORBIDDEN_TITLE_CHARS = "[]"

#: Characters banned from branch names: the pair above plus the git refname
#: metacharacters, which ``git check-ref-format`` rejects for the same
#: structural reason — a name that travels through shell, path and regex
#: contexts must survive all three.
FORBIDDEN_REF_CHARS = "[]~^:?*\\ \t"


def default_repo_root() -> Path:
    """Repository root, assuming this file stays at ``local/bin/wf_util.py``."""
    return Path(__file__).resolve().parents[2]


def cache_root() -> Path:
    return CACHE_ROOT.expanduser()


def lock_dir() -> Path:
    return cache_root() / "locks"


def utcnow() -> str:
    """Timestamp format used across telemetry and generated records."""
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
    untrusted even when it originates locally — and doubly so now that bodies
    round-trip through GitHub, where anyone with repo read access can quote
    them.  Fence-breaking inserts zero-width spaces so a body cannot close a
    fenced block that frames it as data.
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
    of the PR automation stack."  Slugs and branch names derive from titles
    mechanically, so the rule is enforced at the point of creation.
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

    The hazard is two agent sessions mutating the same runtime state; a
    per-entity ``flock`` plus the atomic writer below covers it.  Re-entrant
    within one process so a caller may hold a lock while a helper re-acquires
    it.
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


# ---------------------------------------------------------------------------
# Atomic writes
# ---------------------------------------------------------------------------

def atomic_write(path: Path, text: str) -> None:
    """Write *text* to *path* via tempfile + ``os.replace``.

    Used for runtime artifacts and telemetry snapshots: a half-written file
    must never be observable.
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
