#!/usr/bin/env python3
"""Read `local/project.json`, the one place that says which paper this repository
formalizes: Lean root, track table, GitHub slugs, cache paths, session defaults.

Every tool that used to hard-code the origin project's names reads this instead.
The file may be absent (a checkout that was never bootstrapped): the loader then
returns the placeholder defaults below, so tools keep working on a bare tree.
Stdlib only, python 3.10 (no tomllib, no third-party imports) -- hence JSON.

CLI:  python3 scripts/project_config.py get session.tmux
      python3 scripts/project_config.py shell      # export KIT_*=... lines
      python3 scripts/project_config.py validate
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import shlex
import sys
from pathlib import Path
from typing import Any

CONFIG_RELPATH = "local/project.json"
SCHEMA = 1

#: Placeholders that mean "the receiver has not filled this in yet".  Tools that
#: would do something irreversible with them (push to a remote, say) must refuse.
#:
#: The SLUG is spelled in pieces ON PURPOSE.  `scripts/bootstrap_project.py`
#: rewrites the literal strings everywhere in the tree, and a constant whose job
#: is to mean "no repository has been approved yet" has to go on meaning that
#: inside the instantiated project — otherwise the project's own tools would
#: read its real slug as a placeholder and refuse to publish.
#:
#: The LEAN ROOT is the opposite: it is the name of this repository's own
#: library, so the rename must reach it, exactly as it reaches the Lean files,
#: the lakefile and the test fixtures that name the same tree.  It is spelled as
#: a plain literal for that reason.
PLACEHOLDER_OWNER = "OWNER"
PLACEHOLDER_SLUG = PLACEHOLDER_OWNER + "/" + "REPO"
PLACEHOLDER_LEAN_ROOT = "PaperLib"

#: Placeholder configuration. `bootstrap_project.py` writes a real file over it;
#: until then every tool sees these values, which name no concrete project.
DEFAULTS: dict[str, Any] = {
    "schema": SCHEMA,
    "project": {
        # The slug constants, never their literals: see PLACEHOLDER_SLUG.
        "name": PLACEHOLDER_LEAN_ROOT,
        "lean_root": PLACEHOLDER_LEAN_ROOT,
        "track": "main",
        "title": "",
        "arxiv": [],
        "github_slug": PLACEHOLDER_SLUG,
        "comparator_slug": PLACEHOLDER_SLUG + "-comparator",
    },
    "paths": {
        "cache_root": "~/.cache/paperlib-dev",
        "full_build_lock": "~/.cache/lean-full-build.lock",
    },
    "issues": {"progress": None, "owner_inbox": None, "tracker_root": None},
    "session": {
        "tmux": "paperlib",
        "turn_max_minutes": 25,
        "main": {"model": "", "effort": "", "key": "default", "native_delegates": 1},
        "workers": {
            "model": "",
            "hard_model": "",
            "effort": "",
            "lanes": 0,
            "models_allowed": [],
        },
    },
    "keys": {"default": {"codex_home": "~/.codex", "limit": 2}},
    "paper_mirrors": [],
    "tracks": {},
}
#: One track entry carries exactly the fields of `Track` in
#: `scripts/completion_gate.py`.  Missing fields fall back to these empties, so a
#: half-filled track never crashes a tool; the completion gate reports what is
#: still empty instead.
TRACK_FIELDS: dict[str, Any] = {
    "name": "",
    "lean_root": "",
    "headline": [],
    "gap_register": "",
    "axiom_audit": "",
    "blueprint_chapters": [],
    "leanok_exemptions": "",
    "comparator_doc": "docs/comparator.md",
    "expected_challenge": "",
    "truthful_docs": [],
    "artifact_files": [],
    "artifact_script": "scripts/make_artifact.sh",
}

#: Values that are file-system paths and therefore get `~` expanded on load.
#: (`issues.*` are GitHub issue numbers, not paths.)
_PATH_KEYS = ("paths.cache_root", "paths.full_build_lock")


class ConfigError(Exception):
    """`local/project.json` is present but cannot be used."""


# --------------------------------------------------------------------------- #
# loading
# --------------------------------------------------------------------------- #


def repo_root(root: str | os.PathLike[str] | None = None) -> Path:
    """The repository root: the argument, or the directory holding `scripts/`."""

    if root is not None:
        return Path(root).expanduser()
    return Path(__file__).resolve().parent.parent


def config_path(root: str | os.PathLike[str] | None = None) -> Path:
    return repo_root(root) / CONFIG_RELPATH


def load(root: str | os.PathLike[str] | None = None, required: bool = False) -> dict:
    """Return the configuration for the repository at `root`.

    Keys absent from the file fall back to `DEFAULTS`.  A missing file is fine
    unless `required`; a malformed or schema-violating file always raises
    `ConfigError`.  The returned dict carries `_root` (the repository root as a
    string) so callers need not pass the root around twice.
    """

    path = config_path(root)
    if not path.exists():
        if required:
            raise ConfigError(
                f"no {CONFIG_RELPATH} in {repo_root(root)}. "
                "Run scripts/bootstrap_project.py to create one, or copy the "
                "placeholder from the kit."
            )
        cfg = copy.deepcopy(DEFAULTS)
    else:
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise ConfigError(f"{path}: not valid JSON ({exc})") from exc
        if not isinstance(raw, dict):
            raise ConfigError(f"{path}: top level must be an object, got {_kind(raw)}")
        cfg = _merge(copy.deepcopy(DEFAULTS), raw)
        _validate(cfg, path)

    for dotted in _PATH_KEYS:
        value = get(cfg, dotted)
        if isinstance(value, str) and value:
            _set(cfg, dotted, os.path.expanduser(value))
    for name, entry in cfg.get("keys", {}).items():
        home = entry.get("codex_home")
        if isinstance(home, str) and home:
            entry["codex_home"] = os.path.expanduser(home)

    cfg["_root"] = str(repo_root(root))
    return cfg


def get(cfg: dict, dotted: str, default: Any = None) -> Any:
    """`get(cfg, "session.main.model")` -- missing or null yields `default`."""

    node: Any = cfg
    for part in dotted.split("."):
        if not isinstance(node, dict) or part not in node:
            return default
        node = node[part]
    return default if node is None else node


def track(cfg: dict, name: str | None = None) -> dict | None:
    """One track entry with every `TRACK_FIELDS` key present, or None.

    `name` defaults to `project.track`.  Unknown track -> None (the caller
    decides whether that is an error).
    """

    wanted = name or get(cfg, "project.track", "")
    entry = get(cfg, "tracks", {}).get(wanted)
    if entry is None:
        return None
    merged = copy.deepcopy(TRACK_FIELDS)
    merged.update(copy.deepcopy(entry))
    merged.setdefault("name", wanted)
    if not merged.get("name"):
        merged["name"] = wanted
    return merged


def track_names(cfg: dict) -> list[str]:
    return sorted(get(cfg, "tracks", {}))


def state_dir(cfg: dict) -> str:
    """`$KIT_STATE_DIR` -- the out-of-repo session state directory."""

    return str(Path(get(cfg, "paths.cache_root", "")) / "watchdog")


def paper_mirror_dirs(cfg: dict) -> list[str]:
    """`references/<stem>-paper` for every configured mirror stem."""

    return [f"references/{stem}-paper" for stem in get(cfg, "paper_mirrors", [])]


def lean_scan_targets(root: str | os.PathLike[str], cfg: dict | None = None) -> list[str]:
    """The subtrees that carry this project's Lean code, relative to `root`.

    The Lean root of every registered track, or -- before any track exists --
    `<lean_root>/<track>` when that directory is there and `<lean_root>`
    otherwise.  "Which subtree carries the code" is a project decision, so it is
    read from the configuration and never guessed from a directory name.
    """

    base = Path(root).expanduser()
    cfg = cfg if cfg is not None else load(base)
    roots = [
        entry["lean_root"]
        for name in track_names(cfg)
        if (entry := track(cfg, name)) and entry.get("lean_root")
    ]
    if roots:
        return roots
    lean_root = get(cfg, "project.lean_root", "")
    tr = get(cfg, "project.track", "")
    if lean_root and tr and (base / lean_root / tr).is_dir():
        return [f"{lean_root}/{tr}"]
    return [lean_root] if lean_root else []


def models(cfg: dict) -> dict:
    """The three model names, with `""` meaning "let the codex CLI decide".

    `main` is the supervising session's model, `default` the model a dispatched
    worker runs, and `hard` the one reserved for work classified as hard
    (`session.workers.hard_model`; empty falls back to `default`).  No model name
    is baked into the kit: an untouched `local/project.json` returns three empty
    strings and every tool then omits its `-m` flag.
    """

    default = get(cfg, "session.workers.model", "") or ""
    return {
        "main": get(cfg, "session.main.model", "") or "",
        "default": default,
        "hard": (get(cfg, "session.workers.hard_model", "") or "") or default,
    }


def models_allowed(cfg: dict) -> list[str]:
    """The allowlist a dispatched worker's model must be in; empty = no limit."""

    return [m for m in get(cfg, "session.workers.models_allowed", []) if m]


def has_github_slug(cfg: dict) -> bool:
    """True once the receiver replaced the `OWNER/REPO` placeholder."""

    slug = get(cfg, "project.github_slug", "")
    return bool(slug) and not slug.startswith(PLACEHOLDER_OWNER + "/")


# --------------------------------------------------------------------------- #
# shell export form
# --------------------------------------------------------------------------- #


def exports(cfg: dict) -> "list[tuple[str, str]]":
    """The `KIT_*` name/value pairs, in a fixed order.  Null becomes ""."""

    def s(dotted: str) -> str:
        value = get(cfg, dotted, "")
        return "" if value is None else str(value)

    return [
        ("KIT_REPO_ROOT", cfg.get("_root", "")),
        ("KIT_NAME", s("project.name")),
        ("KIT_LEAN_ROOT", s("project.lean_root")),
        ("KIT_TRACK", s("project.track")),
        ("KIT_GITHUB_SLUG", s("project.github_slug")),
        ("KIT_COMPARATOR_SLUG", s("project.comparator_slug")),
        ("KIT_CACHE_ROOT", s("paths.cache_root")),
        ("KIT_STATE_DIR", state_dir(cfg)),
        ("KIT_TMUX", s("session.tmux")),
        ("KIT_TURN_MAX", s("session.turn_max_minutes")),
        ("KIT_PROGRESS_ISSUE", s("issues.progress")),
        ("KIT_OWNER_INBOX_ISSUE", s("issues.owner_inbox")),
        ("KIT_TRACKER_ROOT", s("issues.tracker_root")),
        ("KIT_MAIN_MODEL", s("session.main.model")),
        ("KIT_MAIN_EFFORT", s("session.main.effort")),
        ("KIT_MAIN_KEY", s("session.main.key")),
        ("KIT_MAIN_DELEGATES", s("session.main.native_delegates")),
        ("KIT_WORKER_MODEL", s("session.workers.model")),
        ("KIT_WORKER_EFFORT", s("session.workers.effort")),
        ("KIT_LANES", s("session.workers.lanes")),
    ]


def shell(cfg: dict) -> str:
    """The text `local/bin/session/config.sh` evals."""

    return "".join(f"export {name}={shlex.quote(value)}\n" for name, value in exports(cfg))


# --------------------------------------------------------------------------- #
# validation
# --------------------------------------------------------------------------- #


def _kind(value: Any) -> str:
    return {
        dict: "an object",
        list: "a list",
        str: "a string",
        bool: "a boolean",
        int: "a number",
        float: "a number",
        type(None): "null",
    }.get(type(value), type(value).__name__)


def _require(ok: bool, path: Path, where: str, message: str) -> None:
    if not ok:
        raise ConfigError(f"{path}: {where} {message}")


def _check_str(cfg: dict, path: Path, dotted: str, allow_empty: bool = True) -> None:
    value = get(cfg, dotted, "")
    _require(isinstance(value, str), path, dotted, f"must be a string, got {_kind(value)}")
    if not allow_empty:
        _require(bool(value), path, dotted, "must not be empty")


def _check_int(cfg: dict, path: Path, dotted: str, minimum: int) -> None:
    value = get(cfg, dotted, minimum)
    _require(
        isinstance(value, int) and not isinstance(value, bool),
        path,
        dotted,
        f"must be a whole number, got {_kind(value)}",
    )
    _require(value >= minimum, path, dotted, f"must be >= {minimum}, got {value}")


def _check_str_list(cfg: dict, path: Path, dotted: str) -> None:
    value = get(cfg, dotted, [])
    _require(isinstance(value, list), path, dotted, f"must be a list, got {_kind(value)}")
    for i, item in enumerate(value):
        _require(
            isinstance(item, str), path, f"{dotted}[{i}]", f"must be a string, got {_kind(item)}"
        )


def _validate(cfg: dict, path: Path) -> None:
    schema = cfg.get("schema")
    _require(
        isinstance(schema, int) and not isinstance(schema, bool),
        path,
        "schema",
        f"must be a whole number, got {_kind(schema)}",
    )
    _require(
        schema == SCHEMA,
        path,
        "schema",
        f"is {schema}; this kit understands {SCHEMA}. Update scripts/project_config.py "
        "or the file.",
    )

    for section in ("project", "paths", "issues", "session", "keys", "tracks"):
        _require(
            isinstance(cfg.get(section), dict),
            path,
            section,
            f"must be an object, got {_kind(cfg.get(section))}",
        )

    for dotted in ("project.name", "project.lean_root", "project.track"):
        _check_str(cfg, path, dotted, allow_empty=False)
    for dotted in ("project.title", "project.github_slug", "project.comparator_slug"):
        _check_str(cfg, path, dotted)
    _check_str_list(cfg, path, "project.arxiv")
    _check_str_list(cfg, path, "paper_mirrors")

    for dotted in ("paths.cache_root", "paths.full_build_lock"):
        _check_str(cfg, path, dotted, allow_empty=False)

    # All three are GitHub issue numbers: the progress issue, the owner's inbox
    # issue, and the root of the tracker tree the proof packets hang under.
    for dotted in ("issues.progress", "issues.owner_inbox", "issues.tracker_root"):
        value = get(cfg, dotted)
        _require(
            value is None or (isinstance(value, int) and not isinstance(value, bool)),
            path,
            dotted,
            f"must be an issue number or null, got {_kind(value)}",
        )

    _check_str(cfg, path, "session.tmux", allow_empty=False)
    _check_int(cfg, path, "session.turn_max_minutes", 1)
    for dotted in (
        "session.main.model",
        "session.main.effort",
        "session.main.key",
        "session.workers.model",
        "session.workers.hard_model",
        "session.workers.effort",
    ):
        _check_str(cfg, path, dotted)
    # The models a dispatched worker may run.  Empty list = no restriction; the
    # rotation shim enforces it (keyrot-install.sh renders it into the state
    # directory as `models-allowed`).
    _check_str_list(cfg, path, "session.workers.models_allowed")
    _check_int(cfg, path, "session.main.native_delegates", 0)
    _check_int(cfg, path, "session.workers.lanes", 0)

    keys = cfg["keys"]
    for name, entry in keys.items():
        _require(isinstance(entry, dict), path, f"keys.{name}", f"must be an object, got {_kind(entry)}")
        _check_str(cfg, path, f"keys.{name}.codex_home", allow_empty=False)
        _check_int(cfg, path, f"keys.{name}.limit", 0)
    main_key = get(cfg, "session.main.key", "")
    _require(
        not main_key or main_key in keys,
        path,
        "session.main.key",
        f"names {main_key!r}, which is not in keys ({', '.join(sorted(keys)) or 'none'})",
    )

    for name, entry in cfg["tracks"].items():
        where = f"tracks.{name}"
        _require(isinstance(entry, dict), path, where, f"must be an object, got {_kind(entry)}")
        unknown = sorted(set(entry) - set(TRACK_FIELDS))
        _require(
            not unknown,
            path,
            where,
            f"has unknown field(s) {', '.join(unknown)}; allowed: {', '.join(sorted(TRACK_FIELDS))}",
        )
        for field, sample in TRACK_FIELDS.items():
            if field not in entry:
                continue
            value = entry[field]
            if isinstance(sample, list):
                _require(
                    isinstance(value, list),
                    path,
                    f"{where}.{field}",
                    f"must be a list, got {_kind(value)}",
                )
            else:
                _require(
                    isinstance(value, str),
                    path,
                    f"{where}.{field}",
                    f"must be a string, got {_kind(value)}",
                )
        for i, pair in enumerate(entry.get("headline", [])):
            _require(
                isinstance(pair, list) and len(pair) == 2 and all(isinstance(p, str) for p in pair),
                path,
                f"{where}.headline[{i}]",
                'must be ["Full.Theorem.Name", "blueprint:label"]',
            )


#: Sections a project REPLACES rather than extends.  `tracks` and `keys` are
#: registries: a file that lists its own keys means "these are the keys", and
#: inheriting the placeholder `default` key would leave a phantom entry pointing
#: at `~/.codex` that the rotation shim and its guard would then believe in.
_REPLACED_SECTIONS = ("tracks", "keys")


def _merge(base: dict, overlay: dict) -> dict:
    for key, value in overlay.items():
        if isinstance(value, dict) and isinstance(base.get(key), dict) \
                and key not in _REPLACED_SECTIONS:
            base[key] = _merge(base[key], value)
        else:
            base[key] = value
    return base


def _set(cfg: dict, dotted: str, value: Any) -> None:
    parts = dotted.split(".")
    node = cfg
    for part in parts[:-1]:
        node = node.setdefault(part, {})
    node[parts[-1]] = value


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=None, help="repository root (default: this checkout)")
    sub = parser.add_subparsers(dest="command", required=True)
    p_get = sub.add_parser("get", help="print one value")
    p_get.add_argument("key", help="dotted key, e.g. session.tmux")
    p_get.add_argument("--default", default="", help="printed when the key is absent or null")
    sub.add_parser("shell", help="print export KIT_*=... lines")
    sub.add_parser("validate", help="check the file and print a one-line summary")
    args = parser.parse_args(argv)

    try:
        cfg = load(args.root, required=args.command == "validate")
    except ConfigError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if args.command == "get":
        value = get(cfg, args.key, args.default)
        if isinstance(value, (dict, list)):
            print(json.dumps(value, indent=2, sort_keys=True))
        else:
            print(value)
        return 0
    if args.command == "shell":
        sys.stdout.write(shell(cfg))
        return 0
    tracks = track_names(cfg)
    print(
        f"{config_path(args.root)}: ok "
        f"(project {get(cfg, 'project.name')}, lean root {get(cfg, 'project.lean_root')}, "
        f"tracks: {', '.join(tracks) if tracks else 'none registered'})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
