#!/usr/bin/env python3
"""Find declarations a git ref already has, by name or by normalised statement.

The scanning half of the duplicate-work guard of issue #576, and a sibling of
``check_duplicate_private_helpers.py``: both compare Lean declarations after a
cheap textual normalisation, that one within a checkout, this one across git
refs.  It parses a ref's Lean sources with ``blueprint_lean_sync``'s parser
through ``git show``, so no checkout, no build and no model call is involved.

Three match kinds, from strongest to weakest:

``fqn``
    the same fully qualified name — a genuine name collision on merge;
``statement``
    a different name whose statement normalises to the same string;
``short``
    the same last name component elsewhere inside the ``MIPStarRE`` namespace.

The normal form strips comments, cuts the proof at the top-level
``:=``/``by``/``where``, renames binder names positionally and collapses
whitespace.  That finds copies and alpha-renamings, which is what the duplicated
dispatches produced.  It does not attempt definitional equality, so a
``statement`` or ``short`` match is a prompt to read both declarations, never by
itself a verdict about the mathematics.

``local/bin/dup_check.py`` is the workflow front end: the CLI, the declaration
claims registry and the dispatch-time check.
"""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from blueprint_lean_sync import (  # noqa: E402
    LeanDecl,
    collect_blueprint_entries,
    collect_file_lean_decls,
    strip_lean_comments_preserve_lines,
)

#: The namespace whose short names are project-owned; a bare last component is
#: only interesting as a duplicate inside it (Mathlib reuses short names).
PROJECT_NAMESPACE = "MIPStarRE"

#: Lean source root, relative to the repository root.
LEAN_ROOT_NAME = "MIPStarRE"

#: Declaration kinds worth guarding: the ones a prover task produces.
GUARDED_KINDS = frozenset({"theorem", "lemma", "def", "abbrev", "instance"})

_IDENT = r"[A-Za-z_][A-Za-z0-9_'!?₀-₉]*"
_IDENT_RE = re.compile(r"(?<![\w.'])" + _IDENT)
_BINDER_GROUP_RE = re.compile(r"[(\[{⦃]\s*((?:" + _IDENT + r"\s+)*" + _IDENT + r")\s*:")
_DECL_HEAD_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?"
    r"(?:(?:noncomputable|protected|private|nonrec|partial|unsafe)\s+)*"
    r"(?:def|theorem|lemma|abbrev|instance|class|structure|inductive|axiom|opaque)\s+"
    r"[\w'+]+(?:\.[\w'+]+)*(?:\.\{[^}]+\})?",
    re.DOTALL,
)
_OPENERS = "([{⟨⦃"
_CLOSERS = ")]}⟩⦄"


class DupScanError(RuntimeError):
    """A usage or environment failure; the CLI reports it as exit code 2."""


def utcstamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------
# git plumbing — every read is local; nothing here fetches
# ---------------------------------------------------------------------------

def git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise DupScanError(
            f"git {' '.join(args[:3])}... failed: {(proc.stderr or '').strip()[:400]}"
        )
    return proc.stdout


def ref_exists(repo: Path, ref: str) -> bool:
    proc = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "--verify", "--quiet",
         f"{ref}^{{commit}}"],
        capture_output=True, text=True,
    )
    return proc.returncode == 0


def ref_lean_files(repo: Path, ref: str) -> list[str]:
    out = git(repo, "ls-tree", "-r", "--name-only", ref, "--", f"{LEAN_ROOT_NAME}/")
    return [line for line in out.splitlines() if line.endswith(".lean")]


def ref_file_text(repo: Path, ref: str, path: str) -> str | None:
    proc = subprocess.run(
        ["git", "-C", str(repo), "show", f"{ref}:{path}"],
        capture_output=True, text=True,
    )
    return None if proc.returncode != 0 else proc.stdout


def merge_base(repo: Path, a: str, b: str) -> str:
    return git(repo, "merge-base", a, b).strip()


def changed_lean_files(repo: Path, base: str, head: str) -> list[str]:
    out = git(repo, "diff", "--name-only", f"{base}...{head}",
              "--", f"{LEAN_ROOT_NAME}/")
    return [line for line in out.splitlines() if line.endswith(".lean")]


# ---------------------------------------------------------------------------
# Statement extraction and normalisation
# ---------------------------------------------------------------------------

def cut_at_proof(text: str) -> str:
    """Return the signature part of a declaration: everything before the proof.

    Cuts at the first top-level ``:=``, ``by`` or ``where``.  Bracket depth
    keeps a ``:=`` inside a structure instance or a ``by`` inside a default
    argument from ending the signature early.
    """
    depth = 0
    index = 0
    size = len(text)
    while index < size:
        char = text[index]
        if char in _OPENERS:
            depth += 1
        elif char in _CLOSERS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if text.startswith(":=", index):
                return text[:index]
            if text.startswith("where", index) and _is_token_at(text, index, 5):
                return text[:index]
            if text.startswith("by", index) and _is_token_at(text, index, 2):
                return text[:index]
        index += 1
    return text


def _is_token_at(text: str, start: int, length: int) -> bool:
    before = text[start - 1] if start > 0 else " "
    after = text[start + length] if start + length < len(text) else " "
    return not (before.isalnum() or before in "_.'") and not (
        after.isalnum() or after in "_.'"
    )


def normalize_statement(statement: str) -> str:
    """A cheap normal form: head removed, binders renamed, whitespace collapsed.

    Empty output means the statement could not be normalised usefully (for
    example a structure whose whole content is its fields); callers treat an
    empty normal form as "no statement match available".
    """
    body = cut_at_proof(statement)
    head = _DECL_HEAD_RE.match(body)
    if head:
        body = body[head.end():]
    order: list[str] = []
    for match in _BINDER_GROUP_RE.finditer(body):
        for name in match.group(1).split():
            if name not in order:
                order.append(name)
    mapping = {name: f"v{index}" for index, name in enumerate(order)}
    if mapping:
        body = _IDENT_RE.sub(lambda m: mapping.get(m.group(0), m.group(0)), body)
    return re.sub(r"\s+", " ", body).strip()


# ---------------------------------------------------------------------------
# Declaration inventories
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class DeclRecord:
    """One declaration, with the normal form of its statement."""
    fqn: str
    short_name: str
    kind: str
    file: str
    line: int
    normalized: str

    @property
    def location(self) -> str:
        return f"{self.file}:{self.line}"

    def as_dict(self) -> dict:
        return {"fqn": self.fqn, "short_name": self.short_name, "kind": self.kind,
                "file": self.file, "line": self.line}


def last_component(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def decls_from_text(text: str, rel_path: str) -> list[DeclRecord]:
    """Parse one Lean file's contents into declaration records."""
    # ``collect_file_lean_decls`` uses its two paths only to derive the relative
    # path it reports; anchoring both under one synthetic prefix makes that
    # derivation give back *rel_path* for any shape of input.
    anchor = Path("/dup-scan")
    try:
        parsed: list[LeanDecl] = collect_file_lean_decls(
            anchor / rel_path, anchor / "root", text=text
        )
    except TypeError:  # pragma: no cover - guards an un-upgraded helper
        raise DupScanError(
            "scripts/blueprint_lean_sync.collect_file_lean_decls does not accept "
            "text=; update it before using dup_scan.py"
        )
    lines = strip_lean_comments_preserve_lines(text)
    records: list[DeclRecord] = []
    for decl in parsed:
        if decl.is_private or decl.kind not in GUARDED_KINDS:
            continue
        span = "\n".join(lines[decl.line - 1: decl.end_line])
        records.append(DeclRecord(
            fqn=decl.fqn, short_name=last_component(decl.fqn), kind=decl.kind,
            file=rel_path, line=decl.line, normalized=normalize_statement(span),
        ))
    return records


@dataclass
class Inventory:
    """All guarded declarations of a ref, indexed for the three match kinds."""
    by_fqn: dict[str, DeclRecord] = field(default_factory=dict)
    by_short: dict[str, list[DeclRecord]] = field(default_factory=dict)
    by_statement: dict[str, list[DeclRecord]] = field(default_factory=dict)

    def add(self, record: DeclRecord) -> None:
        self.by_fqn.setdefault(record.fqn, record)
        self.by_short.setdefault(record.short_name, []).append(record)
        if record.normalized:
            self.by_statement.setdefault(record.normalized, []).append(record)

    def __len__(self) -> int:
        return len(self.by_fqn)


def build_inventory(repo: Path, ref: str, paths: list[str] | None = None) -> Inventory:
    """Index the guarded declarations of *ref* (optionally only *paths*)."""
    inventory = Inventory()
    for rel in (paths if paths is not None else ref_lean_files(repo, ref)):
        text = ref_file_text(repo, ref, rel)
        if text is None:
            continue
        for record in decls_from_text(text, rel):
            inventory.add(record)
    return inventory


def new_declarations(repo: Path, base: str, head: str) -> list[DeclRecord]:
    """Declarations present at *head* but not at *base*, over the changed files."""
    changed = changed_lean_files(repo, base, head)
    if not changed:
        return []
    base_fqns = set(build_inventory(repo, base, changed).by_fqn)
    head_inventory = build_inventory(repo, head, changed)
    return [record for fqn, record in sorted(head_inventory.by_fqn.items())
            if fqn not in base_fqns]


# ---------------------------------------------------------------------------
# Matching
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Match:
    """One duplicate: what was asked about, how it matched, and where."""
    query: str
    kind: str  # fqn | statement | short
    target: DeclRecord

    def as_dict(self) -> dict:
        return {"query": self.query, "match": self.kind,
                "location": self.target.location, **self.target.as_dict()}

    def as_line(self) -> str:
        return (f"DUPLICATE {self.kind:<9} {self.query} -> "
                f"{self.target.location}  {self.target.fqn}")


def in_project_namespace(fqn: str) -> bool:
    return fqn == PROJECT_NAMESPACE or fqn.startswith(PROJECT_NAMESPACE + ".")


def match_name(inventory: Inventory, name: str) -> list[Match]:
    """Name matches: the exact fully qualified name, then the last component."""
    matches: list[Match] = []
    seen: set[str] = set()
    exact = inventory.by_fqn.get(name)
    if exact is not None:
        matches.append(Match(name, "fqn", exact))
        seen.add(exact.location)
    for record in inventory.by_short.get(last_component(name), []):
        if record.location in seen or not in_project_namespace(record.fqn):
            continue
        seen.add(record.location)
        matches.append(Match(name, "short", record))
    return matches


def match_declaration(inventory: Inventory, record: DeclRecord) -> list[Match]:
    """Name matches for a declaration, plus a normalised-statement match."""
    matches = match_name(inventory, record.fqn)
    seen = {match.target.location for match in matches}
    if record.normalized:
        for other in inventory.by_statement.get(record.normalized, []):
            if other.location in seen:
                continue
            seen.add(other.location)
            matches.append(Match(record.fqn, "statement", other))
    return matches


def node_lean_names(repo_root: Path, labels: list[str]) -> list[str]:
    """The ``\\lean{...}`` names of the blueprint nodes carrying *labels*."""
    blueprint_src = repo_root / "blueprint" / "src"
    if not blueprint_src.is_dir():
        raise DupScanError(f"no blueprint sources at {blueprint_src}")
    wanted = set(labels)
    entries = collect_blueprint_entries(blueprint_src)
    names: list[str] = []
    for entry in entries:
        if entry.label in wanted and entry.lean_decl not in names:
            names.append(entry.lean_decl)
    missing = wanted - {entry.label for entry in entries if entry.label}
    if missing:
        raise DupScanError("no blueprint node with label " + ", ".join(sorted(missing)))
    return names


def render_matches(matches: list[Match], queried: int, ref: str) -> str:
    if not matches:
        return f"no duplicate of {queried} name(s)/declaration(s) on {ref}"
    return "\n".join(
        [match.as_line() for match in matches]
        + [f"{len(matches)} duplicate(s) on {ref} for {queried} queried "
           f"name(s)/declaration(s)"]
    )


# ---------------------------------------------------------------------------
# The superseded-PR sweep
# ---------------------------------------------------------------------------

def sweep(repo: Path, ref: str, pulls: list[dict]) -> dict:
    """Per open PR: the new declarations that *ref* already contains.

    *pulls* are ``{number, head_ref, title, url}`` rows.  A head branch missing
    from the local object store is reported as skipped, never as clean.
    """
    inventory = build_inventory(repo, ref)
    results: list[dict] = []
    for pull in sorted(pulls, key=lambda row: row["number"]):
        entry = {"number": pull["number"], "title": pull["title"],
                 "url": pull["url"], "head_ref": pull["head_ref"],
                 "new_declarations": 0, "duplicates": [], "by_kind": {},
                 "skipped": ""}
        head = next(
            (candidate for candidate in
             (f"github/{pull['head_ref']}", pull["head_ref"])
             if ref_exists(repo, candidate)), None)
        if head is None:
            entry["skipped"] = "head branch not present locally"
            results.append(entry)
            continue
        try:
            added = new_declarations(repo, merge_base(repo, ref, head), head)
        except DupScanError as exc:
            entry["skipped"] = str(exc)[:200]
            results.append(entry)
            continue
        entry["new_declarations"] = len(added)
        for record in added:
            for match in match_declaration(inventory, record):
                entry["duplicates"].append(match.as_dict())
        entry["by_kind"] = {
            kind: sum(1 for hit in entry["duplicates"] if hit["match"] == kind)
            for kind in ("fqn", "statement", "short")
        }
        results.append(entry)
    flagged = [row for row in results if row["duplicates"]]
    return {
        "ref": ref,
        "generated_at": utcstamp(),
        "ref_declarations": len(inventory),
        "pull_requests": results,
        "flagged": [row["number"] for row in flagged],
        "flagged_by_name": [row["number"] for row in flagged
                            if row["by_kind"].get("fqn")],
    }


def render_sweep_markdown(report: dict, *, title: str, issue: int | None,
                          pr: int | None, detail_cap: int = 12) -> str:
    """The ``audits/`` document for a sweep report, with its YAML front matter."""
    flagged = report["flagged"]
    by_name = report.get("flagged_by_name", [])
    rows = report["pull_requests"]
    numbers = lambda values: ", ".join("#" + str(value) for value in values)

    front = [
        "---",
        f'title: "{title}"',
        f"date: {report['generated_at'][:10]}",
        "purpose: >",
        "  Model-free sweep of every open pull request for declarations the PR",
        "  adds against its merge base that the published main branch already",
        "  contains, by name or by normalised statement.",
        f'issue: "#{issue}"' if issue else 'issue: ""',
        f'pr: "#{pr}"' if pr else 'pr: ""',
        "---",
    ]
    body = [
        "",
        f"# {title}",
        "",
        "## Headline",
        "",
        f"- Open pull requests examined: **{len(rows)}**",
        f"- With at least one new declaration `{report['ref']}` already contains: "
        f"**{len(flagged)}**" + (f" — {numbers(flagged)}" if flagged else ""),
        f"- Of those, matched by **fully qualified name** (the strongest signal): "
        f"**{len(by_name)}**" + (f" — {numbers(by_name)}" if by_name else ""),
        "",
        "## Method",
        "",
        f"Generated {report['generated_at']} by `local/bin/dup_check.py sweep` "
        f"against `{report['ref']}` "
        f"({report['ref_declarations']} guarded declarations indexed).",
        "For each open pull request the sweep parses only the Lean files the PR",
        "touches, at the PR head and at its merge base, and calls a declaration",
        "*new* when the head has a fully qualified name the merge base lacks.",
        "Each new declaration is matched against the reference three ways:",
        "",
        "| match | meaning |",
        "|---|---|",
        "| `fqn` | the same fully qualified name is already declared on the "
        "reference |",
        "| `statement` | a different name whose statement normalises to the same "
        "string (comments stripped, proof cut at the top-level `:=`/`by`/`where`, "
        "binder names renamed positionally, whitespace collapsed) |",
        f"| `short` | the same last name component elsewhere inside the "
        f"`{PROJECT_NAMESPACE}` namespace |",
        "",
        "No model was called and no proof was checked.",
        "",
        "## Limitations",
        "",
        "- The comparison is textual. A `statement` or `short` match is a prompt",
        "  to read both declarations, never by itself a verdict about the",
        "  mathematics; a `fqn` match is a genuine name collision on merge.",
        "- A stacked pull request whose base branch has since merged into the",
        "  reference shows its parent's declarations as new against its own merge",
        "  base, so part of its count is stack staleness rather than a second",
        "  proof of the same result. Read the per-PR detail before acting.",
        "- Only the reference is searched. An overlap between two *open* pull",
        "  requests is invisible here; the declaration-claims registry",
        "  (`local/registry/declaration-claims.jsonl`) is what covers that case.",
        "- A head branch missing from the local object store is reported as",
        "  skipped, not as clean: the sweep never fetches on its own.",
        "",
        "## Per pull request",
        "",
        "| PR | new declarations | already on the reference | fqn | statement | short |",
        "|---:|---:|---:|---:|---:|---:|",
    ]
    ordered = sorted(rows, key=lambda row: (-len(row["duplicates"]), row["number"]))
    for row in ordered:
        if row["skipped"]:
            body.append(f"| #{row['number']} | – | – | – | – | "
                        f"skipped: {row['skipped']} |")
            continue
        kinds = row.get("by_kind", {})
        body.append(
            f"| #{row['number']} | {row['new_declarations']} | "
            f"{len(row['duplicates'])} | {kinds.get('fqn', 0)} | "
            f"{kinds.get('statement', 0)} | {kinds.get('short', 0)} |"
        )

    body += ["", "## Matches in detail", ""]
    if not flagged:
        body.append("No open pull request adds a declaration the reference already has.")
    for row in ordered:
        if not row["duplicates"]:
            continue
        body += ["", f"### PR #{row['number']} — {row['title']}".rstrip(), ""]
        if row["url"]:
            body += [row["url"], ""]
        for hit in row["duplicates"][:detail_cap]:
            body.append(f"- **{hit['match']}** `{hit['fqn']}` already at "
                        f"`{hit['location']}`")
        extra = len(row["duplicates"]) - detail_cap
        if extra > 0:
            body.append(f"- … and {extra} more (re-run the sweep with `--json`)")
    body.append("")
    return "\n".join(front + body)
