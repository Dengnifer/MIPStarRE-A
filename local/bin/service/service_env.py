#!/usr/bin/env python3
"""Locations and settings for the Python service tools (the bash side is service-lib.sh).

Order of authority, highest first: an explicit ``KIT_*`` environment variable (so a
test or an operator can drive a tool against a temporary tree), ``local/project.json``
through ``scripts/project_config.py``, then the built-in default.  Nothing here reads
a key, a token or anything outside the repository and the cache root.

Provenance: the absolute-path ``sys.path.insert`` preamble the origin's meta-side Python
tools carried; the repository path, the cache root and the repository slug are looked up
here instead of being pasted in.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

#: local/bin/service/service_env.py -> three levels up is the repository root.
REPO_ROOT = Path(__file__).resolve().parents[3]

_DEFAULTS = {
    "KIT_NAME": "PaperLib",
    "KIT_LEAN_ROOT": "PaperLib",
    "KIT_TRACK": "main",
    "KIT_CACHE_ROOT": "~/.cache/paperlib-dev",
    "KIT_TMUX": "paperlib",
}

_CONFIG_KEYS = {
    "KIT_NAME": "project.name",
    "KIT_LEAN_ROOT": "project.lean_root",
    "KIT_TRACK": "project.track",
    "KIT_GITHUB_SLUG": "project.github_slug",
    "KIT_COMPARATOR_SLUG": "project.comparator_slug",
    "KIT_CACHE_ROOT": "paths.cache_root",
    "KIT_TMUX": "session.tmux",
    "KIT_PROGRESS_ISSUE": "issues.progress",
    "KIT_OWNER_INBOX_ISSUE": "issues.owner_inbox",
    "KIT_MAIN_MODEL": "session.main.model",
    "KIT_MAIN_EFFORT": "session.main.effort",
    "KIT_WORKER_MODEL": "session.workers.model",
    "KIT_WORKER_EFFORT": "session.workers.effort",
    "KIT_LANES": "session.workers.lanes",
}

_config_cache: dict | None = None
_config_tried = False


def config(root: Path | None = None) -> dict:
    """``local/project.json`` as a dict, or ``{}`` when it cannot be read.

    A missing or unreadable configuration is not fatal: every caller has an
    environment fallback, and the tools must still run on a half-bootstrapped tree.
    """
    global _config_cache, _config_tried
    if root is None and _config_tried:
        return _config_cache or {}
    base = root or REPO_ROOT
    if root is None:
        _config_tried = True
    scripts = str(base / "scripts")
    try:
        if scripts not in sys.path:
            sys.path.insert(0, scripts)
        import project_config  # noqa: PLC0415 - deliberately late and optional

        data = project_config.load(base)
    except Exception:
        data = {}
    if root is None:
        _config_cache = data
    return data


def setting(name: str, default: str = "") -> str:
    """One ``KIT_*`` setting as a string: environment, then config, then default."""
    value = os.environ.get(name)
    if value is not None and value != "":
        return value
    key = _CONFIG_KEYS.get(name)
    if key:
        node = config()
        for part in key.split("."):
            if not isinstance(node, dict):
                node = None
                break
            node = node.get(part)
        if node not in (None, ""):
            return str(node)
    return _DEFAULTS.get(name, default)


def repo_root() -> Path:
    value = os.environ.get("KIT_REPO_ROOT")
    return Path(value).expanduser() if value else REPO_ROOT


def cache_root() -> Path:
    return Path(setting("KIT_CACHE_ROOT")).expanduser()


def state_dir() -> Path:
    value = os.environ.get("KIT_STATE_DIR")
    return Path(value).expanduser() if value else cache_root() / "watchdog"


def daemon_dir() -> Path:
    return state_dir() / "daemon"


def lane_dir() -> Path:
    return state_dir() / "lanes"


def claim_tool() -> Path:
    """The in-repo claim list — never a copy under the operator's owner-bin."""
    return repo_root() / "local" / "bin" / "claim.sh"


def slug() -> str:
    """``owner/repo``: configuration first, then the checkout's GitHub remote.

    Raises ``RuntimeError`` rather than returning a guess — a wrong slug would send
    writes to somebody else's repository.
    """
    value = setting("KIT_GITHUB_SLUG")
    if value and not value.startswith("OWNER/"):
        return value
    import re
    import subprocess

    for remote in ("github", "origin"):
        proc = subprocess.run(["git", "-C", str(repo_root()), "remote", "get-url", remote],
                              capture_output=True, text=True)
        if proc.returncode == 0:
            match = re.search(r"github\.com[:/]([^/]+/[^/\s]+?)(?:\.git)?$", proc.stdout.strip())
            if match:
                return match.group(1)
    raise RuntimeError(
        "cannot resolve the GitHub repository: set project.github_slug in "
        "local/project.json (or KIT_GITHUB_SLUG), or add a 'github' remote")


def use_local_bin() -> None:
    """Put ``local/bin`` on ``sys.path`` so gh_common / pr_merge import normally."""
    path = str(repo_root() / "local" / "bin")
    if path not in sys.path:
        sys.path.insert(0, path)


def ci_manifest(number: int, head: str) -> Path:
    """Where ``local/bin/ci.sh`` leaves the per-head manifest it wrote."""
    return cache_root() / "ci-manifests" / f"pr{number}-{head}.json"


if __name__ == "__main__":  # a tiny CLI so shell callers can read one setting
    if len(sys.argv) == 2:
        print(setting(sys.argv[1]))
    else:
        print("usage: service_env.py KIT_<NAME>", file=sys.stderr)
        raise SystemExit(2)
