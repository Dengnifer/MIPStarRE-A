#!/usr/bin/env python3
"""Validate the local issue tree against the invariants GitHub used to enforce.

On GitHub, four of these properties were free.  Native sub-issues guaranteed at
most one parent and kept both directions of the relationship in one server-side
row; the label API rejected a name that did not exist; the pin API refused a
fourth pin.  In a directory of markdown files nothing enforces any of it, which
is why the study of the parent workflow called out "the local tree needs a
validator for parent-child symmetry and acyclicity, since frontmatter has no
server enforcing it".  This is that validator.

Checks:

* every ``issues/NNNN-slug.md`` parses, and its ``id`` matches its filename;
* ids are unique and slugs are lowercase-kebab and bracket-free
  (docs/CONTRIBUTING.md:122-124);
* ``parent`` is a scalar, not a list — one parent maximum, GitHub's native
  sub-issue invariant;
* ``parent``/``children`` are symmetric in both directions and every referenced
  id exists;
* the parent relation is acyclic;
* labels are a subset of ``local/labels.yml``, and none appear in its ``banned``
  block (docs/CONTRIBUTING.md:217-219, 292-294);
* at most three issues are pinned (docs/CONTRIBUTING.md:224-228);
* ``state``/``state_reason`` agree: closed issues carry a reason, open ones do
  not — ``track.py`` counts only ``completed`` toward tracking progress, so a
  closed issue with a null reason would silently stall a parent's counter.

Report-only: it never edits an issue.  Exit status is 0 when clean, 1 when any
error is found, 2 on a usage or parse failure.

Usage:
    validate_tree.py
    validate_tree.py --format json
    validate_tree.py --strict          # warnings become errors
    validate_tree.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
try:
    import track
except ModuleNotFoundError as exc:  # pragma: no cover - defensive
    sys.stderr.write(
        "validate_tree.py: cannot import local/bin/track.py, which holds the "
        f"issue data layer ({exc}).\n"
    )
    raise SystemExit(2)

from track import LayerError  # noqa: E402


MAX_PINNED = 3
VALID_STATES = ("open", "closed")
VALID_REASONS = ("completed", "not-planned")


class Findings:
    def __init__(self) -> None:
        self.errors: list[dict[str, str]] = []
        self.warnings: list[dict[str, str]] = []

    def error(self, where: str, check: str, message: str) -> None:
        self.errors.append({"where": where, "check": check, "message": message})

    def warn(self, where: str, check: str, message: str) -> None:
        self.warnings.append({"where": where, "check": check, "message": message})


def _check_file_naming(path: Path, meta: dict, findings: Findings) -> str | None:
    match = track.ISSUE_FILE_RE.match(path.name)
    if not match:
        findings.error(
            path.name, "naming",
            "filename must be NNNN-slug.md with a 4-digit id and a lowercase-kebab, "
            "bracket-free slug (docs/CONTRIBUTING.md:122-124)",
        )
        return None
    file_id = match.group(1)
    meta_id = str(meta.get("id", ""))
    if meta_id != file_id:
        findings.error(
            path.name, "naming",
            f"frontmatter id {meta_id!r} does not match the filename id {file_id!r}",
        )
    return file_id


def _check_scalar_fields(issue: track.Issue, findings: Findings) -> None:
    where = issue.path.name
    for field in track.ISSUE_FIELDS:
        if field not in issue.meta:
            findings.error(where, "schema", f"missing frontmatter field {field!r}")

    state = issue.meta.get("state")
    if state not in VALID_STATES:
        findings.error(where, "state", f"state is {state!r}; expected one of {VALID_STATES}")
    reason = issue.meta.get("state_reason")
    if state == "closed":
        if reason not in VALID_REASONS:
            findings.error(
                where, "state",
                f"closed issue has state_reason {reason!r}; expected one of "
                f"{VALID_REASONS}. track.py counts only 'completed' toward a "
                "tracking parent's progress, so a null reason stalls the counter.",
            )
    elif reason is not None:
        findings.error(
            where, "state",
            f"open issue carries state_reason {reason!r}; it must be null",
        )

    if not isinstance(issue.meta.get("pinned"), bool):
        findings.error(
            where, "schema",
            f"pinned is {issue.meta.get('pinned')!r}; expected true or false",
        )
    if not isinstance(issue.meta.get("labels") or [], list):
        findings.error(where, "schema", "labels must be a list")
    if not isinstance(issue.meta.get("children") or [], list):
        findings.error(where, "schema", "children must be a list")

    title = str(issue.meta.get("title") or "")
    if not title.strip():
        findings.error(where, "schema", "title is empty")
    try:
        track.check_bracket_free(title, "title")
    except LayerError as exc:
        findings.error(where, "bracket-free", str(exc).splitlines()[0])

    for field in ("created", "updated"):
        value = issue.meta.get(field)
        if not isinstance(value, str) or not re.fullmatch(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value
        ):
            findings.warn(
                where, "schema",
                f"{field} is {value!r}; expected an ISO-8601 UTC stamp "
                "like 2026-08-30T04:12:00Z",
            )


def _check_labels(issue: track.Issue, taxonomy: track.Taxonomy, findings: Findings) -> None:
    where = issue.path.name
    for name in issue.labels:
        if name in taxonomy.banned:
            findings.error(
                where, "label-banned",
                f"label {name!r} is banned: {taxonomy.banned[name]}",
            )
        elif name not in taxonomy:
            findings.error(
                where, "label-unknown",
                f"label {name!r} is not defined in local/labels.yml. "
                "The taxonomy file is the local source of truth (it replaces "
                "'treat GitHub as the source of truth', docs/CONTRIBUTING.md:286-289); "
                "add the label there or drop it here.",
            )


def _check_links(issues: dict[str, track.Issue], findings: Findings) -> None:
    for ident, issue in issues.items():
        where = issue.path.name

        try:
            parent_id = issue.parent
        except LayerError as exc:
            findings.error(where, "one-parent", str(exc))
            continue

        if parent_id is not None:
            if parent_id == ident:
                findings.error(where, "one-parent", "issue is its own parent")
            elif parent_id not in issues:
                findings.error(
                    where, "dangling-parent",
                    f"parent #{parent_id} has no issue file",
                )
            elif ident not in issues[parent_id].children:
                findings.error(
                    where, "symmetry",
                    f"#{ident} names parent #{parent_id}, but #{parent_id} does not "
                    f"list #{ident} in children. Both halves must be written; "
                    "issue_new.py --parent does that.",
                )

        seen: set[str] = set()
        for child_id in issue.children:
            if child_id in seen:
                findings.error(where, "duplicate-child", f"child #{child_id} listed twice")
                continue
            seen.add(child_id)
            if child_id == ident:
                findings.error(where, "one-parent", "issue is its own child")
                continue
            child = issues.get(child_id)
            if child is None:
                findings.error(
                    where, "dangling-child", f"child #{child_id} has no issue file"
                )
                continue
            try:
                child_parent = child.parent
            except LayerError:
                continue
            if child_parent != ident:
                findings.error(
                    where, "symmetry",
                    f"#{ident} lists child #{child_id}, but #{child_id} has parent "
                    f"{('#' + child_parent) if child_parent else 'null'}. An issue "
                    "has at most one parent, so the two records disagree.",
                )


def _check_acyclic(issues: dict[str, track.Issue], findings: Findings) -> None:
    """Walk parent links; report the first cycle reached from each start."""
    state: dict[str, int] = {}  # 0 = visiting, 1 = done

    for start in issues:
        if state.get(start) == 1:
            continue
        path: list[str] = []
        node: str | None = start
        while node is not None and state.get(node) != 1:
            if node in path:
                cycle = path[path.index(node):] + [node]
                findings.error(
                    issues[node].path.name, "cycle",
                    "parent chain forms a cycle: " + " -> ".join("#" + n for n in cycle),
                )
                break
            path.append(node)
            state[node] = 0
            current = issues.get(node)
            if current is None:
                break
            try:
                node = current.parent
            except LayerError:
                break
            if node is not None and node not in issues:
                break
        for node_id in path:
            state[node_id] = 1


def _check_pins(issues: dict[str, track.Issue], findings: Findings) -> None:
    pinned = [i for i in issues.values() if i.meta.get("pinned") is True]
    if len(pinned) > MAX_PINNED:
        findings.error(
            "issues/", "pinned",
            f"{len(pinned)} issues are pinned ("
            + ", ".join("#" + i.id for i in sorted(pinned, key=lambda x: x.id))
            + f"); the cap is {MAX_PINNED} (docs/CONTRIBUTING.md:224-228)",
        )


def _check_prs(repo_root: Path, issues: dict[str, track.Issue],
               taxonomy: track.Taxonomy, findings: Findings) -> None:
    """Light consistency pass over the PR registry."""
    for pr in track.iter_prs(repo_root):
        where = str(pr.path.parent.name) + "/pr.md"
        for field in track.PR_FIELDS:
            if field not in pr.meta:
                findings.error(where, "schema", f"missing frontmatter field {field!r}")
        if pr.meta.get("state") not in ("open", "merged", "closed"):
            findings.error(
                where, "state",
                f"state is {pr.meta.get('state')!r}; expected open, merged, or closed",
            )
        issue_id = pr.issue
        if issue_id and issue_id not in issues:
            findings.error(where, "dangling-issue", f"issue #{issue_id} has no file")
        branch = pr.branch
        if branch:
            match = re.search(r"issue-(\d+)", branch)
            if not match:
                findings.error(
                    where, "branch",
                    f"branch {branch!r} does not embed 'issue-<id>'; track.py's "
                    "issue-(\\d+) regex cannot recover the link "
                    "(DESIGN.md:106-107)",
                )
            elif issue_id and track.normalize_id(match.group(1)) != issue_id:
                findings.error(
                    where, "branch",
                    f"branch {branch!r} embeds a different issue than "
                    f"frontmatter's #{issue_id}",
                )
            try:
                track.check_bracket_free(branch, "branch", track.FORBIDDEN_REF_CHARS)
            except LayerError as exc:
                findings.error(where, "bracket-free", str(exc).splitlines()[0])
        for name in pr.labels:
            if name in taxonomy.banned:
                findings.error(where, "label-banned",
                               f"label {name!r} is banned: {taxonomy.banned[name]}")
            elif name not in taxonomy:
                findings.error(where, "label-unknown",
                               f"label {name!r} is not defined in local/labels.yml")


def validate(repo_root: Path, *, include_prs: bool) -> Findings:
    findings = Findings()
    taxonomy = track.load_taxonomy(repo_root)

    directory = track.issues_dir(repo_root)
    if not directory.is_dir():
        raise LayerError(
            f"no issue tree at {directory}. Create the first issue with "
            "local/bin/issue_new.py; there is nothing to validate yet."
        )

    issues: dict[str, track.Issue] = {}
    for path in sorted(directory.glob("*.md")):
        try:
            meta, body = track.split_frontmatter(path.read_text(encoding="utf-8"))
        except LayerError as exc:
            findings.error(path.name, "parse", str(exc))
            continue
        issue = track.Issue(path, meta, body)
        file_id = _check_file_naming(path, meta, findings)
        ident = file_id or str(meta.get("id", path.stem))
        if ident in issues:
            findings.error(
                path.name, "duplicate-id",
                f"id {ident} is also used by {issues[ident].path.name}",
            )
            continue
        issues[ident] = issue

    for issue in issues.values():
        _check_scalar_fields(issue, findings)
        _check_labels(issue, taxonomy, findings)

    _check_links(issues, findings)
    _check_acyclic(issues, findings)
    _check_pins(issues, findings)
    if include_prs:
        _check_prs(repo_root, issues, taxonomy, findings)

    findings.scanned = len(issues)  # type: ignore[attr-defined]
    return findings


def render_text(findings: Findings) -> str:
    lines = [f"scanned {getattr(findings, 'scanned', 0)} issue file(s)"]
    for kind, rows in (("ERROR", findings.errors), ("warning", findings.warnings)):
        for row in rows:
            lines.append(f"{kind} {row['where']} [{row['check']}] {row['message']}")
    if not findings.errors and not findings.warnings:
        lines.append("tree is consistent")
    else:
        lines.append(
            f"{len(findings.errors)} error(s), {len(findings.warnings)} warning(s)"
        )
    return "\n".join(lines) + "\n"


def render_json(findings: Findings) -> str:
    return json.dumps(
        {
            "scanned": getattr(findings, "scanned", 0),
            "errors": findings.errors,
            "warnings": findings.warnings,
            "ok": not findings.errors,
        },
        indent=2,
    ) + "\n"


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="validate_tree.py",
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--repo-root", type=Path, default=track.default_repo_root(),
                        help="repository root (default: two levels above this script)")
    parser.add_argument("--format", choices=("text", "json"), default="text",
                        help="output format (default: text)")
    parser.add_argument("--output", type=Path,
                        help="write the report here instead of stdout")
    parser.add_argument("--no-prs", action="store_true",
                        help="skip the PR registry consistency pass")
    parser.add_argument("--strict", action="store_true",
                        help="treat warnings as errors")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        findings = validate(args.repo_root.resolve(), include_prs=not args.no_prs)
    except LayerError as exc:
        sys.stderr.write(f"validate_tree.py: {exc}\n")
        return 2
    rendered = render_json(findings) if args.format == "json" else render_text(findings)
    if args.output:
        track.atomic_write(args.output, rendered)
        sys.stdout.write(f"wrote {args.output}\n")
    else:
        sys.stdout.write(rendered)
    if findings.errors or (args.strict and findings.warnings):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
