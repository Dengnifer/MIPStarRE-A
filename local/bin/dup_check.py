#!/usr/bin/env python3
"""Duplicate-work guard for declarations — the workflow front end (issue #576).

Two quota sinks motivated this tool.  Tasks covering the same mathematics were
dispatched weeks apart, so several open PRs prove or declare results ``main``
already contains; nobody noticed until review or merge.  And nothing told an
issue author that another open issue was already producing the same
declaration.

The scanning itself lives in ``scripts/dup_scan.py``, beside the repository's
other Lean-source audits; this module is the CLI, the declaration-claims
registry and the dispatch-time check.  No subcommand calls a model, and only
``sweep``'s list of open PRs touches the network.

``check``
    Search a ref (``github/main`` by default) for declarations given by
    ``--name``, by a blueprint node's ``\\lean{}`` names (``--node``), or added
    by a branch or open PR against its merge base (``--branch`` / ``--pr``).
``sweep``
    The same over every open PR, written as an ``audits/`` document.
``claim`` / ``claims-check`` / ``claims-release`` / ``claims-list``
    The append-only registry binding declaration names to the issue producing
    them, checked at issue creation and at dispatch.
``predispatch``
    The one-call form ``dispatch.sh`` uses before a prover/fixer session.

Exit codes: ``0`` clean, ``2`` usage or environment error, ``3`` duplicates
found (or a conflicting claim), ``4`` advisory — nothing was claimed for the
issue, or the ref is absent locally, so nothing could be checked.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO_ROOT_DEFAULT = _HERE.parent.parent
sys.path.insert(0, str(_REPO_ROOT_DEFAULT / "scripts"))

from dup_scan import (  # noqa: E402
    DupScanError,
    Match,
    build_inventory,
    last_component,
    match_declaration,
    match_name,
    merge_base,
    new_declarations,
    node_lean_names,
    ref_exists,
    render_matches,
    render_sweep_markdown,
    sweep,
    utcstamp,
)

#: Registry path, relative to the repository root.
REGISTRY_REL = Path("local/registry/declaration-claims.jsonl")


# ---------------------------------------------------------------------------
# The declaration-claims registry
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ClaimRow:
    """One append-only registry line."""
    ts: str
    action: str  # claim | release
    issue: int
    names: tuple[str, ...] = ()
    nodes: tuple[str, ...] = ()
    by: str = ""
    note: str = ""

    def as_dict(self) -> dict:
        row: dict = {"ts": self.ts, "action": self.action, "issue": self.issue}
        if self.names:
            row["names"] = list(self.names)
        if self.nodes:
            row["nodes"] = list(self.nodes)
        if self.by:
            row["by"] = self.by
        if self.note:
            row["note"] = self.note
        return row


def registry_path(repo_root: Path, override: str | None = None) -> Path:
    return Path(override) if override else repo_root / REGISTRY_REL


def read_claims(path: Path) -> list[ClaimRow]:
    if not path.exists():
        return []
    rows: list[ClaimRow] = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        try:
            raw = json.loads(line)
        except json.JSONDecodeError as exc:
            raise DupScanError(f"{path}:{number}: not JSON ({exc.msg})")
        try:
            rows.append(ClaimRow(
                ts=str(raw["ts"]), action=str(raw["action"]), issue=int(raw["issue"]),
                names=tuple(raw.get("names", ())), nodes=tuple(raw.get("nodes", ())),
                by=str(raw.get("by", "")), note=str(raw.get("note", "")),
            ))
        except (KeyError, TypeError, ValueError) as exc:
            raise DupScanError(f"{path}:{number}: malformed claim row ({exc})")
    return rows


def open_claims(rows: list[ClaimRow]) -> dict[int, ClaimRow]:
    """The newest ``claim`` per issue that no later ``release`` cancelled."""
    latest: dict[int, ClaimRow] = {}
    for row in rows:
        if row.action == "claim":
            latest[row.issue] = row
        elif row.action == "release":
            latest.pop(row.issue, None)
    return latest


def append_claim(path: Path, row: ClaimRow) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(row.as_dict(), sort_keys=True) + "\n")


def claim_conflicts(rows: list[ClaimRow], issue: int,
                    names: list[str]) -> list[tuple[str, ClaimRow]]:
    """Names of *issue* already held by an open claim of another issue."""
    conflicts: list[tuple[str, ClaimRow]] = []
    for other_issue, row in sorted(open_claims(rows).items()):
        if other_issue == issue:
            continue
        held_shorts = {last_component(held) for held in row.names}
        for name in names:
            if name in row.names or last_component(name) in held_shorts:
                conflicts.append((name, row))
    return conflicts


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------

def _resolve_repo(args) -> Path:
    repo = Path(args.repo).resolve() if args.repo else _REPO_ROOT_DEFAULT
    if not (repo / ".git").exists():
        raise DupScanError(f"{repo} is not a git checkout (no .git)")
    return repo


def _require_ref(repo: Path, ref: str) -> None:
    if not ref_exists(repo, ref):
        raise DupScanError(
            f"ref {ref!r} is not present in {repo}; fetch it first "
            f"(this tool never fetches on its own)"
        )


def _queried_names(repo: Path, args) -> list[str]:
    names = list(args.name)
    if args.node:
        names.extend(node_lean_names(repo, list(args.node)))
    return names


def _matches_on_ref(repo: Path, ref: str, names: list[str]) -> list[Match]:
    if not names or not ref_exists(repo, ref):
        return []
    inventory = build_inventory(repo, ref)
    return [match for name in names for match in match_name(inventory, name)]


def cmd_check(args) -> int:
    repo = _resolve_repo(args)
    _require_ref(repo, args.ref)
    names = _queried_names(repo, args)
    head = args.branch
    if args.pr is not None and head is None:
        head = _pr_head_ref(repo, args.pr)
    inventory = build_inventory(repo, args.ref)

    matches = [match for name in names for match in match_name(inventory, name)]
    queried = len(names)
    if head:
        _require_ref(repo, head)
        for record in new_declarations(repo, merge_base(repo, args.ref, head), head):
            queried += 1
            matches.extend(match_declaration(inventory, record))
    if queried == 0:
        raise DupScanError("nothing to check: pass --name, --node, --branch or --pr")

    if args.json:
        print(json.dumps({"ref": args.ref, "queried": queried,
                          "duplicates": [match.as_dict() for match in matches]},
                         indent=2, sort_keys=True))
    elif not args.quiet:
        print(render_matches(matches, queried, args.ref))
    return 3 if matches else 0


def _pr_head_ref(repo: Path, number: int) -> str:
    """The local ref for an open PR's head branch, via the GitHub layer."""
    sys.path.insert(0, str(_HERE))
    import gh_common  # noqa: E402  (lazy: only this path needs the network)

    branch = (gh_common.pr_view(number).get("head") or {}).get("ref")
    if not branch:
        raise DupScanError(f"PR {number} has no head ref")
    for candidate in (f"github/{branch}", branch):
        if ref_exists(repo, candidate):
            return candidate
    raise DupScanError(
        f"PR {number} head {branch!r} is not present locally; fetch it first")


def open_pull_requests(prs_file: str | None) -> list[dict]:
    """Open PRs as ``{number, head_ref, title, url}``; from a file when given."""
    if prs_file:
        raw = json.loads(Path(prs_file).read_text())
        rows = raw["pulls"] if isinstance(raw, dict) else raw
        return [{"number": int(row["number"]),
                 "head_ref": str(row.get("head_ref") or row["head"]["ref"]),
                 "title": str(row.get("title", "")),
                 "url": str(row.get("url", ""))} for row in rows]
    sys.path.insert(0, str(_HERE))
    import gh_common  # noqa: E402

    return [{"number": int(row["number"]), "head_ref": str(row["head"]["ref"]),
             "title": str(row.get("title", "")),
             "url": str(row.get("html_url", ""))}
            for row in gh_common.api("pulls?state=open", paginate=True) or []]


def cmd_sweep(args) -> int:
    repo = _resolve_repo(args)
    _require_ref(repo, args.ref)
    report = sweep(repo, args.ref, open_pull_requests(args.prs_file))
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    if args.out:
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(render_sweep_markdown(
            report, title=args.title, issue=args.issue, pr=args.pr),
            encoding="utf-8")
        if not args.json:
            print(f"wrote {out}")
    if not args.json and not args.out:
        print(json.dumps(report, indent=2, sort_keys=True))
    return 3 if report["flagged"] else 0


def _claim_names(repo: Path, args) -> list[str]:
    names = _queried_names(repo, args)
    if not names:
        raise DupScanError("pass at least one --name or --node")
    return names


def cmd_claim(args) -> int:
    repo = _resolve_repo(args)
    names = _claim_names(repo, args)
    path = registry_path(repo, args.registry)
    conflicts = claim_conflicts(read_claims(path), args.issue, names)
    matches = _matches_on_ref(repo, args.ref, names)
    for name, row in conflicts:
        print(f"CONFLICT claim     {name} -> issue #{row.issue} claimed it {row.ts}")
    for match in matches:
        print(match.as_line())
    blocked = bool(conflicts or matches)
    if blocked and not args.force:
        print("refusing to record the claim; re-run with --force to override "
              "after resolving the overlap")
        return 3
    append_claim(path, ClaimRow(
        ts=utcstamp(), action="claim", issue=args.issue, names=tuple(names),
        nodes=tuple(args.node), by=args.by, note=args.note))
    print(f"claimed {len(names)} name(s) for issue #{args.issue} in {path}")
    return 3 if blocked else 0


def cmd_claims_check(args) -> int:
    repo = _resolve_repo(args)
    names = _claim_names(repo, args)
    conflicts = claim_conflicts(
        read_claims(registry_path(repo, args.registry)), args.issue, names)
    matches = _matches_on_ref(repo, args.ref, names)
    if args.json:
        print(json.dumps({
            "issue": args.issue, "names": names,
            "claim_conflicts": [{"name": name, "issue": row.issue, "ts": row.ts}
                                for name, row in conflicts],
            "duplicates": [match.as_dict() for match in matches],
        }, indent=2, sort_keys=True))
    else:
        for name, row in conflicts:
            print(f"CONFLICT claim     {name} -> issue #{row.issue} "
                  f"claimed it {row.ts}")
        print(render_matches(matches, len(names), args.ref))
    return 3 if (conflicts or matches) else 0


def cmd_claims_release(args) -> int:
    repo = _resolve_repo(args)
    path = registry_path(repo, args.registry)
    if args.issue not in open_claims(read_claims(path)):
        print(f"issue #{args.issue} holds no open claim in {path}")
        return 0
    append_claim(path, ClaimRow(ts=utcstamp(), action="release", issue=args.issue,
                                by=args.by, note=args.note))
    print(f"released the claim of issue #{args.issue}")
    return 0


def cmd_claims_list(args) -> int:
    repo = _resolve_repo(args)
    path = registry_path(repo, args.registry)
    rows = open_claims(read_claims(path))
    if args.json:
        print(json.dumps([row.as_dict() for _, row in sorted(rows.items())],
                         indent=2, sort_keys=True))
        return 0
    if not rows:
        print(f"no open declaration claims in {path}")
        return 0
    for issue, row in sorted(rows.items()):
        print(f"#{issue}  {row.ts}  {row.by or '-'}  {', '.join(row.names)}")
    return 0


def cmd_predispatch(args) -> int:
    """The dispatch-time form: check issue N's claimed names against *ref*.

    Exit ``4`` (nothing claimed, or the ref is absent locally) is advisory, not
    a failure: it tells the operator to record what the task will produce
    before the session starts.
    """
    repo = _resolve_repo(args)
    claim = open_claims(
        read_claims(registry_path(repo, args.registry))).get(args.issue)
    if claim is None:
        print(f"no declaration claim registered for issue #{args.issue}; "
              f"record one with: local/bin/dup_check.py claim --issue "
              f"{args.issue} --name <FullyQualified.Name>")
        return 4
    if not ref_exists(repo, args.ref):
        print(f"ref {args.ref} not present locally; duplicate check skipped")
        return 4
    matches = _matches_on_ref(repo, args.ref, list(claim.names))
    print(render_matches(matches, len(claim.names), args.ref))
    return 3 if matches else 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="dup_check.py", description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    def common(p):
        p.add_argument("--repo", help="repository checkout (default: this one)")
        p.add_argument("--ref", default="github/main",
                       help="reference to search (default: github/main)")
        p.add_argument("--json", action="store_true", help="machine-readable output")
        return p

    def named(p):
        p.add_argument("--issue", type=int, required=True)
        p.add_argument("--name", action="append", default=[])
        p.add_argument("--node", action="append", default=[])
        p.add_argument("--registry", help=f"registry file (default: {REGISTRY_REL})")
        return p

    check = common(sub.add_parser("check", help="search a ref for duplicates"))
    check.add_argument("--name", action="append", default=[],
                       help="declaration name (fully qualified or a last component)")
    check.add_argument("--node", action="append", default=[],
                       help="blueprint node label; its \\lean{} names are checked")
    check.add_argument("--branch", help="branch/ref whose new declarations are checked")
    check.add_argument("--pr", type=int, help="open PR whose head branch is checked")
    check.add_argument("--quiet", action="store_true")
    check.set_defaults(func=cmd_check)

    sw = common(sub.add_parser("sweep",
                               help="report superseded declarations of open PRs"))
    sw.add_argument("--prs-file",
                    help="JSON list of open PRs instead of the GitHub read")
    sw.add_argument("--out", help="write the Markdown report here")
    sw.add_argument("--title", default="Superseded-PR sweep")
    sw.add_argument("--issue", type=int)
    sw.add_argument("--pr", type=int)
    sw.set_defaults(func=cmd_sweep)

    cl = named(common(sub.add_parser("claim", help="claim declaration names")))
    cl.add_argument("--by", default="", help="who records the claim")
    cl.add_argument("--note", default="")
    cl.add_argument("--force", action="store_true",
                    help="record the claim even when it conflicts")
    cl.set_defaults(func=cmd_claim)

    named(common(sub.add_parser(
        "claims-check",
        help="check names against open claims and the ref"))).set_defaults(
            func=cmd_claims_check)

    cr = common(sub.add_parser("claims-release", help="release an issue's claim"))
    cr.add_argument("--issue", type=int, required=True)
    cr.add_argument("--registry")
    cr.add_argument("--by", default="")
    cr.add_argument("--note", default="")
    cr.set_defaults(func=cmd_claims_release)

    ls = common(sub.add_parser("claims-list", help="list open claims"))
    ls.add_argument("--registry")
    ls.set_defaults(func=cmd_claims_list)

    pd = common(sub.add_parser(
        "predispatch", help="the dispatch-time duplicate check for one issue"))
    pd.add_argument("--issue", type=int, required=True)
    pd.add_argument("--registry")
    pd.set_defaults(func=cmd_predispatch)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        return args.func(args)
    except DupScanError as exc:
        print(f"dup_check.py: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
