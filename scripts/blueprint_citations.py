#!/usr/bin/env python3
"""Resolve durable blueprint labels and migrate legacy numeric locators.

Lean docstrings should store blueprint labels, not line ranges.  This helper
derives the current source span of each label from ``blueprint/src/chapter``.
It can also conservatively rewrite old ``chNN_*.tex:START-END`` citations when
the span exactly identifies a node or the surrounding syntax pairs it with one
unambiguous label from that chapter.
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from tex_utils import strip_tex_comment


TOKEN_RE = re.compile(r"\\(?P<kind>begin|end|label)\{(?P<value>[^}]+)\}")
CODE_LABEL_RE = re.compile(r"`(?P<label>[A-Za-z][A-Za-z0-9_.:-]+)`")
CANONICAL_CITATION_RE = re.compile(
    r"\b[Bb]lueprint(?:\s+(?:node|nodes|label|labels|entry|entries))?\s+"
    r"`(?P<label>[A-Za-z][A-Za-z0-9_.:-]+)`"
)
LEGACY_LOCATOR_RE = re.compile(
    r"`(?P<path>(?:blueprint/src/chapter/)?ch[0-9][A-Za-z0-9_.-]*\.tex):"
    r"(?P<start>[0-9]+)(?:(?P<dash>--|-|\u2013|\u2014)(?P<end>[0-9]+))?"
    r"(?P<extra>(?:,[0-9]+(?:--|-|\u2013|\u2014)[0-9]+)*)`"
)
STATEMENT_ENVS = {
    "definition",
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "remark",
    "example",
}
LEAN_LINE_WIDTH = 100


@dataclass(frozen=True)
class EnvironmentSpan:
    """One balanced TeX environment."""

    name: str
    start: int
    end: int


@dataclass(frozen=True)
class LabelLocation:
    """The current source span anchored by one active ``\\label``."""

    label: str
    path: str
    label_line: int
    start: int
    end: int

    @property
    def locator(self) -> str:
        suffix = str(self.start) if self.start == self.end else f"{self.start}-{self.end}"
        return f"{self.path}:{suffix}"


@dataclass(frozen=True)
class CitationUse:
    """A label token found in a file that a reviewer will inspect."""

    label: str
    path: str
    line: int


@dataclass
class _OpenEnvironment:
    name: str
    start: int


def _active_lines(path: Path) -> list[str]:
    return [strip_tex_comment(line) for line in path.read_text(
        encoding="utf-8", errors="replace"
    ).splitlines()]


def _parse_tex_file(path: Path, root: Path) -> list[LabelLocation]:
    """Return active labels in *path*, with enclosing statement/proof spans."""

    lines = _active_lines(path)
    stack: list[_OpenEnvironment] = []
    environments: list[EnvironmentSpan] = []
    labels: list[tuple[str, int]] = []

    for line_no, line in enumerate(lines, 1):
        for token in TOKEN_RE.finditer(line):
            kind = token.group("kind")
            value = token.group("value")
            if kind == "begin":
                stack.append(_OpenEnvironment(value, line_no))
            elif kind == "label":
                labels.append((value, line_no))
            else:
                match_at = next(
                    (index for index in range(len(stack) - 1, -1, -1)
                     if stack[index].name == value),
                    None,
                )
                if match_at is None:
                    continue
                opened = stack[match_at]
                del stack[match_at:]
                environments.append(EnvironmentSpan(value, opened.start, line_no))

    environments.sort(key=lambda span: (span.start, span.end - span.start))
    proof_spans = [span for span in environments if span.name == "proof"]
    rel_path = path.relative_to(root).as_posix()
    locations: list[LabelLocation] = []

    for label, label_line in labels:
        enclosing = [
            span for span in environments
            if span.start <= label_line <= span.end
        ]
        if enclosing:
            span = min(enclosing, key=lambda item: (item.end - item.start, -item.start))
            start, end = span.start, span.end
            if span.name in STATEMENT_ENVS:
                following = next(
                    (proof for proof in proof_spans if proof.start > span.end),
                    None,
                )
                if following is not None:
                    gap = lines[span.end:following.start - 1]
                    if all(not item.strip() for item in gap):
                        end = following.end
        else:
            start = end = label_line
        locations.append(LabelLocation(label, rel_path, label_line, start, end))

    return locations


def build_label_index(root: Path) -> dict[str, list[LabelLocation]]:
    """Index active blueprint labels below ``root/blueprint/src/chapter``."""

    chapter_root = root / "blueprint" / "src" / "chapter"
    if not chapter_root.is_dir():
        raise ValueError(f"blueprint chapter directory does not exist: {chapter_root}")
    index: dict[str, list[LabelLocation]] = {}
    for path in sorted(chapter_root.rglob("*.tex")):
        for location in _parse_tex_file(path, root):
            index.setdefault(location.label, []).append(location)
    return index


def _inside_root(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def collect_input_files(root: Path, paths: list[str], files_from: Path | None) -> list[Path]:
    """Resolve explicit repository paths without permitting traversal."""

    raw_paths = list(paths)
    if files_from is not None:
        raw_paths.extend(
            line.strip() for line in files_from.read_text(encoding="utf-8").splitlines()
            if line.strip()
        )

    files: set[Path] = set()
    for raw_path in raw_paths:
        candidate = Path(raw_path)
        if not candidate.is_absolute():
            candidate = root / candidate
        candidate = candidate.resolve(strict=False)
        if not _inside_root(candidate, root):
            raise ValueError(f"input path escapes repository root: {raw_path}")
        if candidate.is_dir():
            files.update(path for path in candidate.rglob("*") if path.is_file())
        elif candidate.is_file():
            files.add(candidate)
        # Deleted paths from a changed-file list are intentionally ignored.
    return sorted(files)


def find_citation_uses(
    files: list[Path], root: Path, index: dict[str, list[LabelLocation]]
) -> tuple[list[CitationUse], list[CitationUse]]:
    """Find resolvable label tokens and unknown blueprint-label tokens."""

    uses: set[CitationUse] = set()
    unknown: set[CitationUse] = set()
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        rel_path = path.relative_to(root).as_posix()
        for match in CODE_LABEL_RE.finditer(text):
            label = match.group("label")
            if label in index:
                uses.add(CitationUse(label, rel_path, text.count("\n", 0, match.start()) + 1))
            elif ":" in label:
                unknown.add(
                    CitationUse(label, rel_path, text.count("\n", 0, match.start()) + 1)
                )
        for match in CANONICAL_CITATION_RE.finditer(text):
            label = match.group("label")
            if label not in index:
                unknown.add(
                    CitationUse(label, rel_path, text.count("\n", 0, match.start()) + 1)
                )
    return sorted(uses, key=lambda use: (use.label, use.path, use.line)), sorted(
        unknown, key=lambda use: (use.label, use.path, use.line)
    )


def _format_resolutions(
    labels: list[str],
    origins: dict[str, list[CitationUse]],
    index: dict[str, list[LabelLocation]],
    output_format: str,
) -> tuple[str, bool]:
    rows: list[dict[str, object]] = []
    failed = False
    for label in labels:
        locations = index.get(label, [])
        if len(locations) != 1:
            failed = True
        rows.append({
            "label": label,
            "locations": [location.locator for location in locations],
            "cited_at": [f"{use.path}:{use.line}" for use in origins.get(label, [])],
        })

    if output_format == "json":
        return json.dumps(rows, indent=2, sort_keys=True) + "\n", failed

    if output_format == "plain":
        rendered = []
        for row in rows:
            locations = row["locations"]
            value = ", ".join(locations) if locations else "UNRESOLVED"
            rendered.append(f"{row['label']}\t{value}")
        return "\n".join(rendered) + ("\n" if rendered else ""), failed

    rendered = [
        "# Resolved blueprint citations",
        "",
        "Numeric spans below are derived from durable labels; they are not stored citations.",
        "",
    ]
    if not rows:
        rendered.append("_No blueprint labels were found in the selected files._")
    for row in rows:
        locations = row["locations"]
        location_text = ", ".join(f"`{item}`" for item in locations) or "**UNRESOLVED**"
        origin_text = row["cited_at"]
        suffix = ""
        if origin_text:
            suffix = "; cited at " + ", ".join(f"`{item}`" for item in origin_text)
        rendered.append(f"- `{row['label']}` -> {location_text}{suffix}")
    return "\n".join(rendered) + "\n", failed


def _comment_bounds(text: str, position: int) -> tuple[int, int]:
    start = text.rfind("/-", 0, position)
    end = text.find("-/", position)
    if start >= 0 and end >= 0:
        return start, end + 2
    line_start = text.rfind("\n", 0, position) + 1
    line_end = text.find("\n", position)
    return line_start, len(text) if line_end < 0 else line_end


def _candidate_for_locator(
    text: str,
    match: re.Match[str],
    index: dict[str, list[LabelLocation]],
) -> str | None:
    # One label cannot faithfully replace a locator that deliberately names
    # several disjoint spans. Such citations require a manual label list.
    if match.group("extra"):
        return None

    target_name = Path(match.group("path")).name
    old_start = int(match.group("start"))
    old_end = int(match.group("end") or match.group("start"))
    exact = [
        label
        for label, locations in index.items()
        if len(locations) == 1
        and Path(locations[0].path).name == target_name
        and (locations[0].start, locations[0].end) == (old_start, old_end)
    ]
    if exact:
        return exact[0] if len(exact) == 1 else None

    block_start, block_end = _comment_bounds(text, match.start())
    block = text[block_start:block_end]
    candidates: dict[str, list[re.Match[str]]] = {}
    for label_match in CODE_LABEL_RE.finditer(block):
        label = label_match.group("label")
        locations = index.get(label, [])
        if len(locations) != 1 or Path(locations[0].path).name != target_name:
            continue
        candidates.setdefault(label, []).append(label_match)

    if candidates:
        linked: set[str] = set()
        relative_start = match.start() - block_start
        relative_end = match.end() - block_start
        for label, label_matches in candidates.items():
            for label_match in label_matches:
                if label_match.end() <= relative_start:
                    between = block[label_match.end():relative_start]
                    if re.fullmatch(r"\s*\(\s*|\s*[,;]\s+[Bb]lueprint\s+", between):
                        linked.add(label)
                elif label_match.start() >= relative_end:
                    between = block[relative_end:label_match.start()]
                    after = block[label_match.end():]
                    if re.fullmatch(r"\s*\(\s*", between) and re.match(r"\s*\)", after):
                        linked.add(label)
        return next(iter(linked)) if len(linked) == 1 else None

    return None


def _wrap_blueprint_citation_lines(text: str) -> str:
    """Wrap generated blueprint-citation prose at the Lean line limit."""

    wrapped: list[str] = []
    for raw_line in text.splitlines(keepends=True):
        ending = "\n" if raw_line.endswith("\n") else ""
        line = raw_line[:-1] if ending else raw_line
        if (len(line) <= LEAN_LINE_WIDTH
                or not re.search(r"\b[Bb]lueprint\b", line)
                or CODE_LABEL_RE.search(line) is None):
            wrapped.append(raw_line)
            continue
        indent = line[:len(line) - len(line.lstrip())]
        current = line
        while len(current) > LEAN_LINE_WIDTH:
            split_at = current.rfind(" ", len(indent) + 1, LEAN_LINE_WIDTH + 1)
            if split_at < 0:
                break
            wrapped.append(current[:split_at].rstrip() + "\n")
            current = indent + current[split_at + 1:].lstrip()
        wrapped.append(current + ending)
    return "".join(wrapped)


def rewrite_text(
    text: str, index: dict[str, list[LabelLocation]]
) -> tuple[str, list[str]]:
    """Rewrite unambiguous legacy locators and return unresolved locator text."""

    replacements: list[tuple[int, int, str]] = []
    unresolved: list[str] = []
    for match in LEGACY_LOCATOR_RE.finditer(text):
        label = _candidate_for_locator(text, match, index)
        if label is None:
            unresolved.append(match.group(0))
            continue
        replacements.append((match.start(), match.end(), f"`{label}`"))

    rewritten = text
    for start, end, replacement in reversed(replacements):
        rewritten = rewritten[:start] + replacement + rewritten[end:]

    # Collapse the common legacy wording after the locator itself is replaced.
    def collapse_duplicate(match: re.Match[str]) -> str:
        link = match.group("link")
        label = match.group("label")
        if "\n" not in link:
            return f"blueprint `{label}`"
        indent_match = re.search(r"\n(?P<indent>[ \t]*)", link)
        indent = indent_match.group("indent") if indent_match else ""
        return f"blueprint\n{indent}`{label}`"

    rewritten = re.sub(
        r"`(?P<label>[A-Za-z][A-Za-z0-9_.:-]+)`"
        r"(?P<link>,\s+[Bb]lueprint\s+|;\s+[Bb]lueprint\s+|\s+in\s+)"
        r"`(?P=label)`",
        collapse_duplicate,
        rewritten,
    )
    rewritten = re.sub(
        r"(?P<prefix>\b[Bb]lueprint\s+)"
        r"`(?P<label>[A-Za-z][A-Za-z0-9_.:-]+)`\s*[,;]\s*`(?P=label)`",
        lambda match: f"{match.group('prefix')}`{match.group('label')}`",
        rewritten,
    )
    def collapse_parenthetical(match: re.Match[str]) -> str:
        label = match.group("label")
        whitespace = match.group("whitespace")
        if "\n" not in whitespace:
            return f"blueprint `{label}`"
        indent_match = re.search(r"\n(?P<indent>[ \t]*)", whitespace)
        indent = indent_match.group("indent") if indent_match else ""
        return f"blueprint\n{indent}`{label}`"

    rewritten = re.sub(
        r"`(?P<label>[A-Za-z][A-Za-z0-9_.:-]+)`\s*"
        r"(?P<whitespace>\(\s*)`(?P=label)`\s*\)",
        collapse_parenthetical,
        rewritten,
    )
    return _wrap_blueprint_citation_lines(rewritten), unresolved


def _resolve_command(args: argparse.Namespace, root: Path) -> int:
    index = build_label_index(root)
    files = collect_input_files(root, args.paths, args.files_from)
    uses, unknown = find_citation_uses(files, root, index)
    labels = list(args.labels)
    origins: dict[str, list[CitationUse]] = {}
    for use in uses:
        if use.label not in labels:
            labels.append(use.label)
        origins.setdefault(use.label, []).append(use)
    for use in unknown:
        if use.label not in labels:
            labels.append(use.label)
        origins.setdefault(use.label, []).append(use)
    rendered, failed = _format_resolutions(labels, origins, index, args.format)
    sys.stdout.write(rendered)
    return 1 if failed else 0


def _rewrite_command(args: argparse.Namespace, root: Path) -> int:
    index = build_label_index(root)
    files = collect_input_files(root, args.paths, args.files_from)
    changes: list[tuple[Path, str, str]] = []
    unresolved: list[tuple[Path, str]] = []
    for path in files:
        old = path.read_text(encoding="utf-8", errors="replace")
        new, missing = rewrite_text(old, index)
        if old != new:
            changes.append((path, old, new))
        unresolved.extend((path, locator) for locator in missing)

    for path, locator in unresolved:
        rel_path = path.relative_to(root).as_posix()
        print(f"unresolved: {rel_path}: {locator}", file=sys.stderr)
    if unresolved and not args.allow_unresolved:
        print("refusing partial rewrite; pass --allow-unresolved to rewrite safe matches",
              file=sys.stderr)
        return 1

    if args.write:
        for path, _old, new in changes:
            path.write_text(new, encoding="utf-8")
    else:
        for path, old, new in changes:
            rel_path = path.relative_to(root).as_posix()
            sys.stdout.writelines(difflib.unified_diff(
                old.splitlines(keepends=True),
                new.splitlines(keepends=True),
                fromfile=rel_path,
                tofile=rel_path,
            ))
    action = "rewrote" if args.write else "would rewrite"
    print(f"{action} {len(changes)} file(s); {len(unresolved)} unresolved locator(s)",
          file=sys.stderr)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="repository root (default: parent of scripts/)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    resolve = subparsers.add_parser("resolve", help="resolve labels to current spans")
    resolve.add_argument("labels", nargs="*", help="blueprint labels to resolve")
    resolve.add_argument("--path", dest="paths", action="append", default=[],
                         help="scan a repository file or directory for label tokens")
    resolve.add_argument("--files-from", type=Path,
                         help="scan repository paths listed one per line")
    resolve.add_argument("--format", choices=("markdown", "plain", "json"),
                         default="plain")

    rewrite = subparsers.add_parser("rewrite", help="replace unambiguous legacy locators")
    rewrite.add_argument("paths", nargs="*", help="repository files or directories to rewrite")
    rewrite.add_argument("--files-from", type=Path,
                         help="rewrite repository paths listed one per line")
    rewrite.add_argument("--write", action="store_true",
                         help="write changes in place (default: print a diff)")
    rewrite.add_argument("--allow-unresolved", action="store_true",
                         help="rewrite safe matches while reporting unresolved locators")

    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if args.command == "resolve":
            return _resolve_command(args, root)
        return _rewrite_command(args, root)
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
