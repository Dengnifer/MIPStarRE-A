#!/usr/bin/env python3
"""daemon-scan.py [adj-list-file] — the merge daemon's candidate scan, in ONE GraphQL call.

Prints one line per candidate: ``PR:ISSUE:BRANCH:SLUG:MODE:HEAD``.  A candidate is an
open PR whose head commit carries `local-ci/summary` = SUCCESS and `local-review/summary`
= SUCCESS and whose newest marked review for that head has no unresolved ledger line
(MODE ``clean``), or whose number stands in the adjudication list (MODE ``adj``) with at
least CI success.  Diagnostics go to stderr; exit 1 on API failure.

One call, not three per PR: the per-PR REST scan the first daemon used took over half an
hour once sixty PRs were open, and a scan that slow merges nothing.

Provenance: kit-src/tmp-scripts/daemon-scan.py with the repository owner and name
hard-coded into the query.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import service_env  # noqa: E402

#: Branch naming of local/bin/pr_open.py: issue-<number>-<slug>.
BRANCH_RE = re.compile(r"^issue-0*([0-9]+)-(.*)$")
QUERY = """query($owner:String!, $name:String!) {
  repository(owner:$owner, name:$name) {
    pullRequests(states:OPEN, first:100, orderBy:{field:UPDATED_AT, direction:DESC}) {
      nodes {
        number headRefName headRefOid
        commits(last:1) { nodes { commit { status { contexts { context state } } } } }
        reviews(last:8) { nodes { body } } } } } }"""


def scan(owner: str, name: str, adjudicated: set[str], timeout: int = 120) -> list[str]:
    proc = subprocess.run(
        ["gh", "api", "graphql", "-f", f"query={QUERY}", "-F", f"owner={owner}", "-F", f"name={name}"],
        capture_output=True, text=True, timeout=timeout,
        env=dict(os.environ, GH_PROMPT_DISABLED="1", GH_PAGER="cat", NO_COLOR="1"))
    if proc.returncode != 0:
        raise RuntimeError("graphql failed: " + (proc.stderr or proc.stdout)[:200])
    nodes = json.loads(proc.stdout)["data"]["repository"]["pullRequests"]["nodes"]
    return rows(nodes, adjudicated)


def rows(nodes: list[dict], adjudicated: set[str]) -> list[str]:
    """The candidate lines for one page of PR nodes (pure: the unit test drives this)."""
    out: list[str] = []
    for pull in nodes:
        number = str(pull["number"])
        branch = pull["headRefName"]
        head = pull["headRefOid"]
        match = BRANCH_RE.match(branch)
        if not match:
            continue
        issue, slug = match.group(1), match.group(2)
        contexts: dict[str, str] = {}
        for node in pull["commits"]["nodes"]:
            status = (node["commit"] or {}).get("status") or {}
            for entry in status.get("contexts") or []:
                contexts[entry["context"]] = entry["state"]
        if contexts.get("local-ci/summary") != "SUCCESS":
            continue
        clean = False
        if contexts.get("local-review/summary") == "SUCCESS":
            bodies = [r["body"] or "" for r in pull["reviews"]["nodes"]
                      if "mipstarre-review" in (r["body"] or "") and f"head={head}" in (r["body"] or "")]
            if bodies:
                clean = len(re.findall(r"^- \[ \]", bodies[-1], re.M)) == 0
        if clean:
            out.append(f"{number}:{issue}:{branch}:{slug}:clean:{head}")
        elif number in adjudicated:
            out.append(f"{number}:{issue}:{branch}:{slug}:adj:{head}")
    return out


def main(argv: list[str]) -> int:
    adjudicated: set[str] = set()
    if argv and os.path.exists(argv[0]):
        adjudicated = set(Path(argv[0]).read_text(encoding="utf-8").split())
    try:
        owner, name = service_env.slug().split("/", 1)
    except (RuntimeError, ValueError) as exc:
        print(f"scan: {exc}", file=sys.stderr)
        return 1
    try:
        lines = scan(owner, name, adjudicated)
    except subprocess.TimeoutExpired:
        print("scan: graphql timeout", file=sys.stderr)
        return 1
    except Exception as exc:
        print(f"scan: {exc}", file=sys.stderr)
        return 1
    for line in lines:
        print(line)
    print(f"scan: {len(lines)} candidates", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
