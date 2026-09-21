#!/usr/bin/env python3
r"""Turn a chapter plan into the tracker / packet issue tree on GitHub.

GitHub is the record: the tracker holds one sub-issue per chapter, each chapter
holds its packets, and every prerequisite is a real ``blocked_by`` dependency
edge, never a bullet in a body.  This script only orders the work and calls the
two tools that already own those writes — ``local/bin/issue_new.py`` (create,
adoption-safe through its ``--key``) and ``gh_common.py add-blocked-by``
(idempotent).  Re-running it creates nothing twice: numbers are written back
into the plan file, and the issue keys make an interrupted run adopt rather
than duplicate.

Plan file (JSON).  ``id`` values are local to this file and are what
``blocked_by`` refers to; every node needs exactly one of ``body`` / ``body_file``
(``body_file`` is relative to the plan file):

    {
      "key": "ch-plan",                       // optional; prefix of the issue keys
      "tracker": {
        "title": "Tracking - the main theorem",
        "body_file": "tracker.md",
        "labels": ["tracking"]
      },
      "chapters": [
        {"id": "ch01", "title": "Chapter 1 - definitions",
         "body": "Blueprint chapter ch01.", "labels": ["formalization"]},
        {"id": "ch02", "title": "Chapter 2 - the main estimate",
         "body": "Blueprint chapter ch02.", "blocked_by": ["ch01"]}
      ],
      "packets": [
        {"id": "p02a", "chapter": "ch02", "title": "Packet - the estimate itself",
         "body": "...", "blocked_by": ["p01a"], "labels": ["formalization"]},
        {"id": "p01a", "chapter": "ch01", "title": "Packet - the basic definitions",
         "body": "..."}
      ]
    }

After a run the file also carries ``"created": {"tracker": 12, "ch01": 13, …}``
and ``issues.tracker_root`` in ``local/project.json`` points at the tracker.

Usage:
    local/bin/tracker_tree.py plan.json [--dry-run] [--root REPO]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT_DEFAULT = Path(__file__).resolve().parents[2]

TRACKER_ID = "tracker"


class PlanError(Exception):
    """The plan cannot be executed; the message says which node and why."""


def slugify(text: str) -> str:
    slug = re.sub(r"[^A-Za-z0-9]+", "-", text).strip("-").lower()
    return slug[:48].strip("-") or "tracker"


def run_cmd(cmd: list[str], cwd: Path) -> tuple[int, str, str]:
    """Every external call goes through here, so tests can replace it."""
    try:
        proc = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True,
                              timeout=300)
    except FileNotFoundError:
        return 127, "", f"{cmd[0]}: not found"
    except subprocess.TimeoutExpired:
        return 124, "", f"{cmd[0]}: timed out"
    return proc.returncode, proc.stdout, proc.stderr


# ── reading the plan ────────────────────────────────────────────────────────


class Node:
    """One issue to create: a tracker, a chapter or a packet."""

    def __init__(self, ident: str, kind: str, raw: dict, plan_dir: Path) -> None:
        self.ident = ident
        self.kind = kind
        self.title = str(raw.get("title") or "").strip()
        if not self.title:
            raise PlanError(f"{kind} {ident!r} has no title")
        if "[" in self.title or "]" in self.title:
            raise PlanError(f"{kind} {ident!r}: issue titles are bracket-free")
        body = raw.get("body")
        body_file = raw.get("body_file")
        if bool(body) == bool(body_file):
            raise PlanError(
                f"{kind} {ident!r} needs exactly one of \"body\" and \"body_file\"")
        if body_file:
            path = (plan_dir / body_file).resolve()
            if not path.is_file():
                raise PlanError(f"{kind} {ident!r}: body_file {body_file} does not exist")
            self.body = path.read_text(encoding="utf-8")
        else:
            self.body = str(body)
        self.labels = [str(name) for name in raw.get("labels") or []]
        self.blocked_by = [str(name) for name in raw.get("blocked_by") or []]
        self.parent_id = str(raw.get("chapter") or "") if kind == "packet" else (
            "" if kind == "tracker" else TRACKER_ID)
        if kind == "packet" and not self.parent_id:
            self.parent_id = TRACKER_ID


def read_plan(path: Path) -> tuple[dict, list[Node]]:
    try:
        plan = json.loads(path.read_text(encoding="utf-8"))
    except ValueError as exc:
        raise PlanError(f"{path} is not valid JSON: {exc}")
    if not isinstance(plan, dict) or "tracker" not in plan:
        raise PlanError(f"{path} has no \"tracker\" object")
    plan_dir = path.parent
    nodes = [Node(TRACKER_ID, "tracker", plan["tracker"], plan_dir)]
    seen = {TRACKER_ID}
    for kind, key in (("chapter", "chapters"), ("packet", "packets")):
        for raw in plan.get(key) or []:
            ident = str(raw.get("id") or "").strip()
            if not ident:
                raise PlanError(f"every {kind} needs an \"id\"")
            if ident in seen:
                raise PlanError(f"duplicate id {ident!r}")
            seen.add(ident)
            nodes.append(Node(ident, kind, raw, plan_dir))
    by_id = {node.ident: node for node in nodes}
    for node in nodes:
        for other in node.blocked_by + ([node.parent_id] if node.parent_id else []):
            if other not in by_id:
                raise PlanError(f"{node.kind} {node.ident!r} refers to unknown id {other!r}")
    return plan, nodes


def order(nodes: list[Node]) -> list[Node]:
    """Tracker first, then parents before children and blockers before blocked."""
    done: list[Node] = []
    placed: set[str] = set()
    pending = list(nodes)
    while pending:
        progressed = False
        for node in list(pending):
            needs = set(node.blocked_by)
            if node.parent_id:
                needs.add(node.parent_id)
            if needs <= placed:
                done.append(node)
                placed.add(node.ident)
                pending.remove(node)
                progressed = True
        if not progressed:
            stuck = ", ".join(sorted(node.ident for node in pending))
            raise PlanError(
                f"the plan has a cycle or an unreachable node: {stuck}. "
                "Every blocked_by and chapter reference must eventually reach the tracker."
            )
    return done


# ── creating the tree ───────────────────────────────────────────────────────


def issue_key(plan: dict, node: Node) -> str:
    prefix = str(plan.get("key") or slugify(plan["tracker"].get("title", "tracker")))
    return f"{prefix}-{node.ident}"


def create_issue(root: Path, node: Node, key: str, parent: int | None) -> int:
    with tempfile.NamedTemporaryFile("w", suffix=".md", encoding="utf-8",
                                     delete=False) as handle:
        handle.write(node.body)
        body_file = handle.name
    try:
        cmd = [sys.executable, str(root / "local" / "bin" / "issue_new.py"),
               "--title", node.title, "--body-file", body_file, "--key", key]
        for label in node.labels:
            cmd += ["--label", label]
        if parent is not None:
            cmd += ["--parent", str(parent)]
        rc, out, err = run_cmd(cmd, root)
    finally:
        os.unlink(body_file)
    number = (out or "").strip().splitlines()
    if rc != 0 or not number or not number[-1].strip().isdigit():
        raise PlanError(f"creating {node.ident!r} failed: {(err or out).strip() or rc}")
    return int(number[-1].strip())


def add_edge(root: Path, issue: int, blocker: int) -> None:
    rc, out, err = run_cmd([sys.executable, str(root / "local" / "bin" / "gh_common.py"),
                            "add-blocked-by", str(issue), str(blocker)], root)
    if rc != 0:
        raise PlanError(f"blocking #{issue} on #{blocker} failed: {(err or out).strip() or rc}")


def set_tracker_root(root: Path, number: int) -> bool:
    path = root / "local" / "project.json"
    if not path.is_file():
        return False
    try:
        config = json.loads(path.read_text(encoding="utf-8"))
    except ValueError:
        return False
    config.setdefault("issues", {})["tracker_root"] = number
    path.write_text(json.dumps(config, indent=2, ensure_ascii=False) + "\n",
                    encoding="utf-8")
    return True


def render(nodes: list[Node], created: dict) -> str:
    lines = []
    for node in nodes:
        depth = {"tracker": 0, "chapter": 1, "packet": 2}[node.kind]
        number = created.get(node.ident)
        mark = f"#{number}" if number else "(new)"
        blockers = ", ".join(node.blocked_by)
        lines.append("  " * depth + f"- {mark} [{node.ident}] {node.title}"
                     + (f"   blocked by: {blockers}" if blockers else ""))
    return "\n".join(lines)


def build(plan_path: Path, root: Path, dry_run: bool) -> int:
    plan, nodes = read_plan(plan_path)
    ordered = order(nodes)
    created: dict[str, int] = {k: int(v) for k, v in (plan.get("created") or {}).items()}

    if dry_run:
        print(f"{len(ordered)} issues in creation order "
              f"({sum(1 for n in ordered if n.kind == 'chapter')} chapters, "
              f"{sum(1 for n in ordered if n.kind == 'packet')} packets):")
        print(render(ordered, created))
        edges = [(node.ident, other) for node in ordered for other in node.blocked_by]
        print(f"{len(edges)} blocked_by edges:")
        for issue, blocker in edges:
            print(f"  {issue} blocked by {blocker}")
        print("dry run: nothing was created.")
        return 0

    for node in ordered:
        if node.ident in created:
            continue
        parent = created.get(node.parent_id) if node.parent_id else None
        created[node.ident] = create_issue(root, node, issue_key(plan, node), parent)
        print(f"#{created[node.ident]} {node.ident} {node.title}")
        plan["created"] = created
        plan_path.write_text(json.dumps(plan, indent=2, ensure_ascii=False) + "\n",
                             encoding="utf-8")

    for node in ordered:
        for other in node.blocked_by:
            add_edge(root, created[node.ident], created[other])
    plan["created"] = created
    plan_path.write_text(json.dumps(plan, indent=2, ensure_ascii=False) + "\n",
                         encoding="utf-8")
    root_number = created[TRACKER_ID]
    wrote = set_tracker_root(root, root_number)
    print(f"tracker #{root_number}"
          + (" recorded as issues.tracker_root in local/project.json" if wrote
             else " (local/project.json not found; record the tracker there by hand)"))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("plan", type=Path, help="the chapter plan (JSON)")
    parser.add_argument("--dry-run", action="store_true",
                        help="print the tree and the dependency edges, create nothing")
    parser.add_argument("--root", type=Path, default=REPO_ROOT_DEFAULT,
                        help="repository root (default: the checkout this script lives in)")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)
    try:
        return build(args.plan, args.root.resolve(), args.dry_run)
    except PlanError as exc:
        sys.stderr.write(f"tracker_tree.py: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
