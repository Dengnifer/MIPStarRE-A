#!/usr/bin/env python3
"""Per-challenge configuration for the comparator challenge generator.

A *challenge* is one self-contained `Challenge.lean` file: the Lean modules the
extractor must import, the target theorems whose statement closure it extracts,
the header and footer wrapped around the assembled body, the checked-in
expected copy, and the elaboration-context tables (`extras`,
`module_preludes`) that the kernel closure cannot see.

Configurations live in `scripts/comparator/challenges/<name>.json` and are read
by `extract_closure.lean` (through the environment), `assemble_challenge.py`
and `check_challenge_drift.py`.  See README.md in this directory.

Schema (unknown top-level keys are rejected so typos fail loudly):

```jsonc
{
  "name": "ldt",                       // required, must equal the file stem
  "description": "…",                  // optional, free text
  "imports": ["MIPStarRE.…"],          // required, non-empty
  "targets": ["MIPStarRE.…"],          // required, non-empty; closure roots
  "header": "scripts/…/header.lean",   // optional, null to omit
  "footer": "scripts/…/footer.lean",   // optional, null to omit
  "expected": "scripts/…/Challenge.lean.expected",   // required
  "require_expected": true,            // optional, default true
  "split": false,                      // optional, default false
  "common_opens": ["open scoped …"],  // optional, split-module context
  "extras": {"Decl.Name": ["line"]},   // optional
  "module_preludes": {                 // optional
    // one scope covering the whole module …
    "MIPStarRE/…/Module.lean": {"namespace": ["A", "B"], "lines": ["open …"]},
    // … or several, each covering a line range of it
    "MIPStarRE/…/Other.lean": [
      {"namespace": ["A"], "lines": ["variable …"], "first": 52, "last": 94},
      {"namespace": ["A"], "lines": ["variable …"], "first": 96, "last": 223,
       "noncomputable": true}
    ]
  }
}
```

A module needs one scope per source section whose elaboration context differs:
the self-dual normal basis file, for instance, has a group-algebra section and
a trace-dual section binding the same identifier to different things.  A scope
opened with `noncomputable section` in the source is marked `noncomputable`,
because the definitions inside such a section carry no `noncomputable` keyword
of their own and do not re-elaborate outside one.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# Configuration lives next to the scripts that read it, not under the tree
# being checked: `--root` names the library tree, which may be a different
# worktree than the one these scripts were invoked from.
CHALLENGE_DIR = Path(__file__).resolve().parent / "challenges"
DEFAULT_CHALLENGE = "ldt"

# Read by `extract_closure.lean`; comma-separated fully qualified names.
TARGETS_ENV = "MIPSTARRE_COMPARATOR_TARGETS"

# `last` of a scope that runs to the end of its module
LAST_LINE = 10**9

_NAME_RE = re.compile(r"[a-z0-9][a-z0-9_-]*\Z")

_KEYS = {
    "name",
    "description",
    "imports",
    "targets",
    "header",
    "footer",
    "expected",
    "require_expected",
    "split",
    "common_opens",
    "extras",
    "module_preludes",
}

_PRELUDE_KEYS = {"namespace", "lines", "first", "last", "noncomputable"}


class ChallengeConfigError(ValueError):
    """A challenge configuration is missing a key, or a key has a wrong type."""


@dataclass(frozen=True)
class Prelude:
    """Elaboration context of one source scope of one module.

    The `open`s, `variable`s and `local notation` that the declarations of a
    source section were elaborated under, replayed around the snippets taken
    from lines `first`..`last` of that module.
    """

    namespace: tuple[str, ...]
    lines: tuple[str, ...]
    first: int = 1
    last: int = LAST_LINE
    noncomputable: bool = False

    @property
    def whole_file(self) -> bool:
        return self.first == 1 and self.last == LAST_LINE

    def covers(self, line: int) -> bool:
        return self.first <= line <= self.last


@dataclass(frozen=True)
class ChallengeConfig:
    """One comparator challenge, as configured on disk."""

    name: str
    path: Path
    description: str
    imports: tuple[str, ...]
    targets: tuple[str, ...]
    header: str | None
    footer: str | None
    expected: str
    require_expected: bool
    split: bool
    common_opens: tuple[str, ...]
    extras: dict[str, list[str]]
    module_preludes: dict[str, tuple[Prelude, ...]]

    def import_block(self) -> str:
        """The extractor's module header for this challenge."""
        return "".join(f"import {module}\n" for module in self.imports)

    def extractor_env(self) -> dict[str, str]:
        """Environment overrides telling the extractor which targets to close."""
        return {TARGETS_ENV: ",".join(self.targets)}


def _typed(data: dict[str, Any], key: str, kind: type, where: Path) -> Any:
    if key not in data:
        raise ChallengeConfigError(f"{where}: missing required key {key!r}")
    value = data[key]
    if not isinstance(value, kind):
        raise ChallengeConfigError(
            f"{where}: key {key!r} must be {kind.__name__}, got {type(value).__name__}"
        )
    return value


def _string_list(data: dict[str, Any], key: str, where: Path, *, nonempty: bool) -> tuple[str, ...]:
    value = _typed(data, key, list, where)
    if not all(isinstance(item, str) for item in value):
        raise ChallengeConfigError(f"{where}: key {key!r} must be a list of strings")
    if nonempty and not value:
        raise ChallengeConfigError(f"{where}: key {key!r} must not be empty")
    return tuple(value)


def _optional_path(data: dict[str, Any], key: str, where: Path) -> str | None:
    value = data.get(key)
    if value is None:
        return None
    if not isinstance(value, str):
        raise ChallengeConfigError(f"{where}: key {key!r} must be a string or null")
    return value


def _extras(data: dict[str, Any], where: Path) -> dict[str, list[str]]:
    raw = data.get("extras", {})
    if not isinstance(raw, dict):
        raise ChallengeConfigError(f"{where}: key 'extras' must be an object")
    table: dict[str, list[str]] = {}
    for name, lines in raw.items():
        if not isinstance(lines, list) or not all(isinstance(line, str) for line in lines):
            raise ChallengeConfigError(
                f"{where}: extras[{name!r}] must be a list of source lines"
            )
        table[name] = list(lines)
    return table


def _prelude(entry: Any, module: str, where: Path) -> Prelude:
    if not isinstance(entry, dict):
        raise ChallengeConfigError(
            f"{where}: module_preludes[{module!r}] must be an object with "
            "'namespace' and 'lines', or a list of such objects"
        )
    unknown = sorted(set(entry) - _PRELUDE_KEYS)
    if unknown:
        raise ChallengeConfigError(
            f"{where}: module_preludes[{module!r}] has unknown key(s) {unknown}"
        )
    namespace = entry.get("namespace", [])
    lines = entry.get("lines", [])
    for field, value in (("namespace", namespace), ("lines", lines)):
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            raise ChallengeConfigError(
                f"{where}: module_preludes[{module!r}][{field!r}] must be a list of strings"
            )
    first = entry.get("first", 1)
    last = entry.get("last", LAST_LINE)
    for field, value in (("first", first), ("last", last)):
        if not isinstance(value, int) or isinstance(value, bool) or value < 1:
            raise ChallengeConfigError(
                f"{where}: module_preludes[{module!r}][{field!r}] must be a positive integer"
            )
    if last < first:
        raise ChallengeConfigError(
            f"{where}: module_preludes[{module!r}] has 'last' before 'first'"
        )
    noncomputable = entry.get("noncomputable", False)
    if not isinstance(noncomputable, bool):
        raise ChallengeConfigError(
            f"{where}: module_preludes[{module!r}]['noncomputable'] must be a boolean"
        )
    return Prelude(
        namespace=tuple(namespace),
        lines=tuple(lines),
        first=first,
        last=last,
        noncomputable=noncomputable,
    )


def _module_preludes(data: dict[str, Any], where: Path) -> dict[str, tuple[Prelude, ...]]:
    raw = data.get("module_preludes", {})
    if not isinstance(raw, dict):
        raise ChallengeConfigError(f"{where}: key 'module_preludes' must be an object")
    table: dict[str, tuple[Prelude, ...]] = {}
    for module, entry in raw.items():
        entries = entry if isinstance(entry, list) else [entry]
        scopes = tuple(_prelude(item, module, where) for item in entries)
        if not scopes:
            raise ChallengeConfigError(
                f"{where}: module_preludes[{module!r}] must name at least one scope"
            )
        spans = sorted((scope.first, scope.last) for scope in scopes)
        for (_, earlier_last), (later_first, _) in zip(spans, spans[1:]):
            if later_first <= earlier_last:
                raise ChallengeConfigError(
                    f"{where}: module_preludes[{module!r}] has overlapping scopes; "
                    "one line of a module can only be elaborated in one context"
                )
        table[module] = scopes
    return table


def load_challenge(path: Path) -> ChallengeConfig:
    """Read and validate one challenge configuration file."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ChallengeConfigError(f"{path}: no such challenge configuration") from exc
    except json.JSONDecodeError as exc:
        raise ChallengeConfigError(f"{path}: invalid JSON — {exc}") from exc
    if not isinstance(data, dict):
        raise ChallengeConfigError(f"{path}: top level must be an object")

    unknown = sorted(set(data) - _KEYS)
    if unknown:
        raise ChallengeConfigError(f"{path}: unknown key(s) {unknown}")

    name = _typed(data, "name", str, path)
    if not _NAME_RE.match(name):
        raise ChallengeConfigError(
            f"{path}: name {name!r} must match {_NAME_RE.pattern} (it names the CLI selector)"
        )
    if name != path.stem:
        raise ChallengeConfigError(f"{path}: name {name!r} must equal the file stem {path.stem!r}")

    require_expected = data.get("require_expected", True)
    if not isinstance(require_expected, bool):
        raise ChallengeConfigError(f"{path}: key 'require_expected' must be a boolean")

    split = data.get("split", False)
    if not isinstance(split, bool):
        raise ChallengeConfigError(f"{path}: key 'split' must be a boolean")

    common_opens = data.get("common_opens", [])
    if not isinstance(common_opens, list) or not all(
        isinstance(line, str) for line in common_opens
    ):
        raise ChallengeConfigError(
            f"{path}: key 'common_opens' must be a list of strings"
        )

    return ChallengeConfig(
        name=name,
        path=path,
        description=str(data.get("description", "")),
        imports=_string_list(data, "imports", path, nonempty=True),
        targets=_string_list(data, "targets", path, nonempty=True),
        header=_optional_path(data, "header", path),
        footer=_optional_path(data, "footer", path),
        expected=_typed(data, "expected", str, path),
        require_expected=require_expected,
        split=split,
        common_opens=tuple(common_opens),
        extras=_extras(data, path),
        module_preludes=_module_preludes(data, path),
    )


def challenge_paths(directory: Path | None = None) -> list[Path]:
    """Every configuration file, in a deterministic (file name) order."""
    return sorted((directory or CHALLENGE_DIR).glob("*.json"))


def load_challenges(
    names: list[str] | None = None, directory: Path | None = None
) -> list[ChallengeConfig]:
    """Load the named challenges, or all of them in file-name order."""
    directory = directory or CHALLENGE_DIR
    available = {path.stem: path for path in challenge_paths(directory)}
    if names is None:
        return [load_challenge(path) for _, path in sorted(available.items())]

    selected: list[ChallengeConfig] = []
    for name in names:
        candidate = Path(name)
        if candidate.suffix == ".json" or candidate.parent != Path("."):
            selected.append(load_challenge(candidate))
            continue
        if name not in available:
            raise ChallengeConfigError(
                f"unknown challenge {name!r}; configured: {sorted(available)}"
            )
        selected.append(load_challenge(available[name]))
    return selected
