#!/usr/bin/env python3
"""Assemble the body of a comparator `Challenge.lean` from the extractor's TSV.

Input: the TSV produced by ``extract_closure.lean`` (one declaration per row:
name, module path, start line, end line).  For each declaration this script
re-reads its source lines and records the namespace stack active at that
point (tracking ``namespace``/``section``/``end`` lines), orders declarations
topologically (module import rank, then line number), and emits the snippets
grouped under merged namespace blocks with provenance comments.

The elaboration context that the kernel closure cannot see (attribute commands,
``CoeFun`` instances, ``variable``/``open`` blocks) lives in the ``extras`` and
``module_preludes`` tables of the selected challenge configuration under
``challenges/``; the script fails if one of *that challenge's* keys no longer
matches any extracted declaration.  See README.md in this directory for the
full regeneration pipeline.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from challenge_config import (
    DEFAULT_CHALLENGE,
    ChallengeConfig,
    ChallengeConfigError,
    load_challenges,
)

Entry = tuple[str, str, int, int, list[str]]


class StaleContextTables(ValueError):
    """A challenge's ``extras``/``module_preludes`` key matches no declaration."""


def source_range_with_context(
    lines: list[str], start: int, end: int
) -> tuple[int, list[str]]:
    """Extend a declaration range to include adjacent scoped context commands."""
    # Lean's source range starts at a declaration's docstring and can omit a
    # declaration-scoped command immediately before it.  Preserve that command:
    # dropping `open scoped Classical in`, for example, removes the local
    # decidability instances needed to re-elaborate the definition body.
    if start > 1 and re.fullmatch(r"open\s+scoped\s+.+\s+in", lines[start - 2].strip()):
        start -= 1
    return start, lines[start - 1 : end]


class Assembler:
    def __init__(
        self,
        repo_root: Path,
        extras: dict[str, list[str]] | None = None,
        module_preludes: dict[str, tuple[list[str], list[str]]] | None = None,
    ) -> None:
        self.repo_root = repo_root
        self.extras = extras or {}
        self.module_preludes = module_preludes or {}
        self._file_cache: dict[str, list[str]] = {}
        self.out: list[str] = []
        self.cur_ns: list[str] = []
        self.open_prelude: tuple[str, list[str]] | None = None

    def get_lines(self, path: str) -> list[str]:
        if path not in self._file_cache:
            text = (self.repo_root / path).read_text(encoding="utf-8")
            self._file_cache[path] = text.splitlines()
        return self._file_cache[path]

    def ns_stack_at(self, path: str, line_no: int) -> list[str]:
        """Namespace stack (list of names) active just before 1-indexed line_no."""
        stack: list[tuple[str, str | None]] = []
        for raw in self.get_lines(path)[: line_no - 1]:
            s = raw.strip()
            m = re.match(r"namespace\s+([\w.À-￿']+)", s)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = re.match(r"section\s*([\w.À-￿']*)", s)
            if m and s.startswith("section"):
                stack.append(("sec", m.group(1) or None))
                continue
            m = re.match(r"end\s*([\w.À-￿']*)\s*(?:--.*)?$", s)
            if m and s.startswith("end") and stack:
                stack.pop()
        return [n for kind, n in stack if kind == "ns" and n is not None]

    def imports_of(self, path: str) -> list[str]:
        # imports are only legal at the top of a Lean file, so scanning the
        # whole file for ^import is safe and robust against comment headers
        return [
            m.group(1).replace(".", "/") + ".lean"
            for raw in self.get_lines(path)
            if (m := re.match(r"import\s+([\w.]+)", raw))
        ]

    def module_ranks(self, mods: set[str]) -> dict[str, int]:
        rank: dict[str, int] = {}

        def visit(p: str, depth: int = 0) -> None:
            if p in rank or depth > 200:
                return
            rank[p] = -1  # in progress
            local = [d for d in self.imports_of(p) if d.startswith("MIPStarRE/")]
            for d in local:
                if rank.get(d) != -1:
                    visit(d, depth + 1)
            rank[p] = max((rank.get(d, 0) for d in local), default=0) + 1

        for p in sorted(mods):
            visit(p)
        return rank

    def switch_ns(self, target: list[str]) -> None:
        common = 0
        while (
            common < min(len(self.cur_ns), len(target))
            and self.cur_ns[common] == target[common]
        ):
            common += 1
        for n in reversed(self.cur_ns[common:]):
            self.out.append(f"end {n}")
        for n in target[common:]:
            self.out.append(f"namespace {n}")
        self.cur_ns = target

    def close_prelude(self) -> None:
        if self.open_prelude:
            self.switch_ns(self.open_prelude[1])
            self.out.append("end  -- module scope")
            self.open_prelude = None

    def emit(self, entries: list[Entry], generated: list[tuple[str, str]]) -> str:
        # compiler-generated declarations (no source range) regenerate
        # identically during elaboration; record them up front as comments so
        # they never interact with namespace or prelude state
        if generated:
            self.out.append("-- Compiler-generated declarations in the closure (no source")
            self.out.append("-- range); they regenerate identically during elaboration:")
            for name, path in generated:
                self.out.append(f"--   {name}  (from {path})")

        emitted_ranges: set[tuple[str, int]] = set()
        prev_path: str | None = None
        for name, path, a, b, src in entries:
            if (path, a) in emitted_ranges:  # deriving twins share the range
                continue
            emitted_ranges.add((path, a))
            if path != prev_path:
                self.close_prelude()
                if path in self.module_preludes:
                    base_ns, lines = self.module_preludes[path]
                    self.switch_ns(base_ns)
                    self.out.append("")
                    self.out.append(f"-- elaboration context of {path}")
                    self.out.append("section")
                    self.out.extend(lines)
                    self.open_prelude = (path, base_ns)
                prev_path = path
            self.switch_ns(self.ns_stack_at(path, a))
            self.out.append("")
            self.out.append(f"-- source: {path}:{a}-{b}  ({name})")
            self.out.extend(src)
            self.out.extend(self.extras.get(name, []))
        self.close_prelude()
        self.switch_ns([])
        return "\n".join(self.out)


def read_entries(
    asm: Assembler, tsv: Path
) -> tuple[list[Entry], list[tuple[str, str]]]:
    entries: list[Entry] = []
    generated: list[tuple[str, str]] = []
    for row in tsv.read_text(encoding="utf-8").splitlines():
        if not row or "\t" not in row:
            continue
        name, path, a, b = row.split("\t")
        if a == "NORANGE":
            generated.append((name, path))
            continue
        start, end = int(a), int(b)
        start, source = source_range_with_context(asm.get_lines(path), start, end)
        entries.append((name, path, start, end, source))
    return entries, generated


def assemble(challenge: ChallengeConfig, root: Path, tsv: Path) -> str:
    """Assembled body text; raises ``StaleContextTables`` on an unmatched key."""
    asm = Assembler(root, challenge.extras, challenge.module_preludes)
    entries, generated = read_entries(asm, tsv)

    rank = asm.module_ranks({e[1] for e in entries})
    entries.sort(key=lambda e: (rank.get(e[1], 999), e[2]))

    body = asm.emit(entries, generated)

    unused_extras = set(challenge.extras) - {name for name, *_ in entries}
    unused_preludes = set(challenge.module_preludes) - {e[1] for e in entries}
    if unused_extras or unused_preludes:
        raise StaleContextTables(
            f"stale context tables in {challenge.path} — "
            f"unmatched extras keys: {sorted(unused_extras)}; "
            f"unmatched module_preludes keys: {sorted(unused_preludes)}"
        )
    return body


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tsv", type=Path, help="TSV from extract_closure.lean")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="repository root (default: current directory)",
    )
    parser.add_argument(
        "--challenge",
        default=DEFAULT_CHALLENGE,
        help=(
            "challenge name under challenges/, or a path to a configuration "
            f"file (default: {DEFAULT_CHALLENGE})"
        ),
    )
    args = parser.parse_args()

    try:
        challenge = load_challenges([args.challenge])[0]
        print(assemble(challenge, args.root, args.tsv))
    except (ChallengeConfigError, StaleContextTables) as exc:
        print(exc, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
