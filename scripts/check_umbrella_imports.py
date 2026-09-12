#!/usr/bin/env python3
"""Guard against Lean modules that no re-export file imports.

``lake build`` compiles the import closure of the library roots and nothing
else.  A module outside that closure type checks under ``lake env lean`` and
still gets no ``.olean``, so the per-file pre-push gate fails on it in a lane
hours after the merge.  On 2026-09-12 exactly that happened:
``MIPStarRE/QPBT/Combining/Points.lean`` did not import its split-out children
``Points.Absorption`` and ``Points.MarginalContraction``, every lane's gate
failed, and the lane runner grew three hand-patched revisions before anyone
looked at the import graph.  This turns it into a CI failure on the PR.

It is a pure reachability check over import headers, and only that:

* it NEVER edits a file — re-exports are serialized by the operator and workers
  are told not to touch ``MIPStarRE/QPBT.lean``, so this prints the exact line
  to add and the file to add it to, and stops;
* it reads no proof, no statement, no axiom, no declaration body;
* it has no opinion about whether a module should exist.

Roots: ``MIPStarRE.lean`` and every ``MIPStarRE/<Name>.lean`` that shadows a
``MIPStarRE/<Name>/`` directory (today ``LDT``, ``QPBT``, ``Quantum``) — the
re-export files AGENTS.md requires to be preserved.  A DEEPER re-export file is
deliberately not a root: unimported, it yields no oleans for its whole subtree,
which is the failure being guarded against.  ``*/Test/*`` modules are excluded
from the walk and are not roots.  Full protocol: ``local/protocols/ci.md`` §7.1.

Usage::

    python3 scripts/check_umbrella_imports.py --root . [--ci] [--warn-only]

Exit status: 0 clean (or ``--warn-only``), 1 findings, 2 the root is not a
MIPStarRE worktree.
"""

from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

LIB_DIR_NAME: str = "MIPStarRE"

# Matched against the path parts relative to the repository root.
EXCLUDE_DIRS: tuple[str, ...] = (".git", ".lake", ".worktrees", "lake-packages", "tmp")

# A directory component with this name marks a test target ("*/Test/*").
TEST_DIR_NAME: str = "Test"

EXIT_OK: int = 0
EXIT_FINDINGS: int = 1
EXIT_USAGE: int = 2


# ---------------------------------------------------------------------------
# Model
# ---------------------------------------------------------------------------


@dataclass
class Module:
    """One ``.lean` file, reduced to the only thing this check reads."""

    name: str  # MIPStarRE.QPBT.Combining.Points
    rel: str  # MIPStarRE/QPBT/Combining/Points.lean
    path: Path
    is_test: bool
    imports: tuple[str, ...] = ()


@dataclass
class Report:
    """Everything the walk found; rendering and exit status are derived."""

    root: Path
    roots: list[str] = field(default_factory=list)
    modules: dict[str, Module] = field(default_factory=dict)
    reachable: set[str] = field(default_factory=set)
    test_reachable: set[str] = field(default_factory=set)
    unreachable: list[str] = field(default_factory=list)
    primary: set[str] = field(default_factory=set)
    fixed_by: dict[str, str] = field(default_factory=dict)
    targets: dict[str, str | None] = field(default_factory=dict)
    unreadable: list[tuple[str, str]] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    @property
    def clean(self) -> bool:
        return not self.unreachable and not self.unreadable


# ---------------------------------------------------------------------------
# Walking
# ---------------------------------------------------------------------------


def _is_excluded(path: Path, root: Path) -> bool:
    """Return True if *path* is not a ``.lean`` file under a scanned directory."""

    if path.suffix != ".lean":
        return True
    try:
        rel_parts = path.relative_to(root).parts
    except ValueError:
        return True
    return any(part in EXCLUDE_DIRS for part in rel_parts)


def module_name(root: Path, path: Path) -> str:
    """``MIPStarRE/QPBT/Combining/Points.lean`` -> ``MIPStarRE.QPBT.Combining.Points``."""

    rel = path.relative_to(root)
    return ".".join(rel.with_suffix("").parts)


def is_test_module(root: Path, path: Path) -> bool:
    """Return True for ``*/Test/*`` modules (excluded from the walk and from the roots)."""

    rel = path.relative_to(root)
    return TEST_DIR_NAME in rel.parts[:-1]


def iter_lean_files(root: Path) -> list[Path]:
    """Return every scanned ``.lean`` file: ``MIPStarRE.lean`` plus ``MIPStarRE/**``."""

    found: list[Path] = []
    top = root / f"{LIB_DIR_NAME}.lean"
    if top.is_file():
        found.append(top)
    lib_dir = root / LIB_DIR_NAME
    if lib_dir.is_dir():
        for path in lib_dir.rglob("*.lean"):
            if path.is_file() and not _is_excluded(path, root):
                found.append(path)
    return sorted(found)


def strip_comments(line: str, depth: int) -> tuple[str, int]:
    """Remove Lean comments from one header line.

    ``depth`` is the nesting depth of ``/- ... -/`` carried in from the previous
    line; the updated depth is returned.  ``--`` ends the line.  Deliberately
    simple: this only ever runs over an import header, where there are no string
    literals to confuse it.
    """

    out: list[str] = []
    i = 0
    size = len(line)
    while i < size:
        if depth > 0:
            if line.startswith("-/", i):
                depth -= 1
                i += 2
            elif line.startswith("/-", i):
                depth += 1
                i += 2
            else:
                i += 1
            continue
        if line.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if line.startswith("--", i):
            break
        out.append(line[i])
        i += 1
    return "".join(out), depth


def parse_imports(text: str) -> tuple[str, ...]:
    """Return the module names imported by *text*.

    Lean 4 puts every ``import`` before the first command, with only comments
    (and an optional ``prelude``) interleaved, so the scan stops at the first
    real command.  That keeps an ``import`` word inside a docstring or a proof
    from being mistaken for an import.
    """

    imports: list[str] = []
    depth = 0
    for raw in text.splitlines():
        visible, depth = strip_comments(raw, depth)
        stripped = visible.strip()
        if not stripped:
            continue
        if stripped == "prelude":
            continue
        if stripped == "import" or stripped.startswith("import "):
            rest = stripped[len("import") :].strip()
            if rest:
                imports.append(rest.split()[0])
            continue
        break
    return tuple(imports)


def read_lean(path: Path) -> tuple[str | None, str | None, str | None]:
    """Return ``(text, unreadable_reason, decode_warning)``; never raises."""

    try:
        raw = path.read_bytes()
    except OSError as exc:  # permissions, a dangling symlink, a vanished file
        return None, str(exc), None
    try:
        return raw.decode("utf-8"), None, None
    except UnicodeDecodeError as exc:
        # Import lines are ASCII, so a replacement character in a docstring
        # cannot change the import graph.  Report it and carry on.
        return raw.decode("utf-8", errors="replace"), None, f"not valid UTF-8 ({exc.reason})"


def collect_modules(root: Path) -> tuple[dict[str, Module], list[tuple[str, str]], list[str]]:
    """Walk the tree.  Returns ``(modules, unreadable, warnings)``."""

    modules: dict[str, Module] = {}
    unreadable: list[tuple[str, str]] = []
    warnings: list[str] = []

    for path in iter_lean_files(root):
        rel = path.relative_to(root).as_posix()
        name = module_name(root, path)
        text, unreadable_reason, decode_warning = read_lean(path)
        if text is None:
            unreadable.append((rel, unreadable_reason or "unknown error"))
            continue
        if decode_warning:
            warnings.append(f"{rel}: {decode_warning}; parsed with replacement characters")
        modules[name] = Module(
            name=name,
            rel=rel,
            path=path,
            is_test=is_test_module(root, path),
            imports=parse_imports(text),
        )
    return modules, unreadable, warnings


# ---------------------------------------------------------------------------
# Reachability
# ---------------------------------------------------------------------------


def reexport_roots(root: Path, modules: dict[str, Module]) -> list[str]:
    """Return the re-export roots: ``MIPStarRE`` and every depth-1 directory shadow."""

    roots: list[str] = []
    if LIB_DIR_NAME in modules and not modules[LIB_DIR_NAME].is_test:
        roots.append(LIB_DIR_NAME)
    lib_dir = root / LIB_DIR_NAME
    if lib_dir.is_dir():
        for entry in sorted(lib_dir.iterdir()):
            if not entry.is_dir() or entry.name in EXCLUDE_DIRS:
                continue
            shadow = f"{LIB_DIR_NAME}.{entry.name}"
            module = modules.get(shadow)
            if module is not None and not module.is_test and shadow not in roots:
                roots.append(shadow)
    return roots


def closure(modules: dict[str, Module], starts: list[str]) -> set[str]:
    """Transitive import closure of *starts*, restricted to known modules."""

    seen: set[str] = set()
    stack = [name for name in starts if name in modules]
    while stack:
        name = stack.pop()
        if name in seen:
            continue
        seen.add(name)
        for imported in modules[name].imports:
            if imported in modules and imported not in seen:
                stack.append(imported)
    return seen


def reexport_file_for(
    name: str,
    modules: dict[str, Module],
    forbidden: set[str] | None = None,
) -> str | None:
    """Return the rel path of the re-export file *name* belongs in.

    The nearest existing ancestor module: ``…Combining.Points.Absorption`` goes
    into ``MIPStarRE/QPBT/Combining/Points.lean`` when that file exists, else
    into ``MIPStarRE/QPBT/Combining.lean``, else into ``MIPStarRE/QPBT.lean``.

    An ancestor in *forbidden* — the modules *name* already imports, directly or
    transitively — is skipped: importing it back would be an import cycle and
    Lake would refuse the build.  When a file was split out of its parent and
    still imports it, the fix therefore climbs to the next re-export file up.
    """

    blocked = forbidden or set()
    parts = name.split(".")
    for cut in range(len(parts) - 1, 0, -1):
        ancestor = ".".join(parts[:cut])
        module = modules.get(ancestor)
        if module is None or ancestor in blocked:
            continue
        return module.rel
    return None


def analyse(root: Path) -> Report:
    """Run the whole walk and return the findings."""

    modules, unreadable, warnings = collect_modules(root)
    report = Report(root=root, modules=modules, unreadable=unreadable, warnings=warnings)

    report.roots = reexport_roots(root, modules)
    report.reachable = closure(modules, report.roots)
    test_roots = [name for name, module in modules.items() if module.is_test]
    report.test_reachable = closure(modules, test_roots)

    unreachable = sorted(
        name
        for name, module in modules.items()
        if not module.is_test and name not in report.reachable
    )
    report.unreachable = unreachable

    # A module imported by another unreachable module is fixed for free once
    # that one is imported.  Only the sources of the unreachable subgraph need
    # an import line of their own.
    unreachable_set = set(unreachable)
    for name in unreachable:
        for imported in modules[name].imports:
            if imported in unreachable_set and imported not in report.fixed_by:
                report.fixed_by[imported] = name
    report.primary = {name for name in unreachable if name not in report.fixed_by}
    if unreachable and not report.primary:  # an import cycle among orphans
        report.primary = set(unreachable)
        report.fixed_by.clear()

    # Resolve the re-export file once, skipping any ancestor the module already
    # imports (importing it back would be a cycle).
    for name in report.primary:
        own_imports = closure(modules, [name]) - {name}
        report.targets[name] = reexport_file_for(name, modules, forbidden=own_imports)
    return report


# ---------------------------------------------------------------------------
# Rendering
# ---------------------------------------------------------------------------


def format_report(report: Report, ci: bool = False) -> list[str]:
    """Render *report* as the lines to print."""

    lines: list[str] = []

    for rel, reason in report.unreadable:
        if ci:
            lines.append(f"::error file={rel}::could not be read: {reason}")
        lines.append(f"UNREADABLE {rel}: {reason}")
    for warning in report.warnings:
        lines.append(f"WARNING {warning}")

    if not report.unreachable:
        if not report.unreadable:
            lines.append(
                f"All {len(report.modules)} Lean modules are reachable from the re-export "
                f"roots ({', '.join(report.roots) or 'none found'})."
            )
        return lines

    lines.append("")
    lines.append(
        f"{len(report.unreachable)} Lean module(s) are outside the import closure of the "
        f"re-export roots ({', '.join(report.roots) or 'none found'})."
    )
    lines.append("`lake build` produces no .olean for them, so the per-file pre-push gate")
    lines.append("and every downstream import will fail on them.")
    lines.append("")

    for name in report.unreachable:
        module = report.modules[name]
        target = report.targets.get(name)
        import_line = f"import {name}"
        if ci and name in report.primary:
            lines.append(f"::error file={module.rel}::unreachable module; add `{import_line}`")
        lines.append(f"  {module.rel}")
        lines.append(f"      module        {name}")
        if name in report.primary:
            if target is None:
                lines.append(
                    "      add to        no usable re-export file: every ancestor is missing,"
                )
                lines.append(
                    "                    or is already imported here so importing it back"
                )
                lines.append(
                    "                    would be a cycle.  Take this to the operator."
                )
            else:
                lines.append(f"      add to        {target}")
            lines.append(f"      import line   {import_line}")
        else:
            lines.append(
                f"      follows from  becomes reachable once {report.fixed_by[name]} is imported"
            )
        if name in report.test_reachable:
            lines.append(
                "      note          imported only from a */Test/* module; a test target"
            )
            lines.append(
                "                    produces no library olean, so this is still unreachable"
            )
        lines.append("")

    lines.append("This check never edits a re-export file: re-exports are serialized by the")
    lines.append("operator.  Add the line(s) above by hand, in the named file.")
    return lines


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Report Lean modules no re-export file imports (they get no olean).",
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="Repository root (default: .)",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Also emit ::error:: annotation lines for each finding.",
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="Print the same report but exit 0 (for a first run on an unclean tree).",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    root = args.root.resolve()

    if not (root / LIB_DIR_NAME).is_dir() and not (root / f"{LIB_DIR_NAME}.lean").is_file():
        print(
            f"ERROR: {root} has no {LIB_DIR_NAME}/ directory and no {LIB_DIR_NAME}.lean; "
            "this is not a MIPStarRE worktree (pass --root).",
            file=sys.stderr,
        )
        return EXIT_USAGE

    report = analyse(root)
    for line in format_report(report, ci=args.ci):
        print(line)

    if report.clean:
        return EXIT_OK
    if args.warn_only:
        print("--warn-only: reporting only, exiting 0.")
        return EXIT_OK
    return EXIT_FINDINGS


if __name__ == "__main__":
    raise SystemExit(main())
