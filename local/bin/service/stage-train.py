#!/usr/bin/env python3
"""stage-train.py PR PR [PR...] — verify the members and the quiet-window preconditions,
then write <daemon>/train-approved.json pinning each member's exact head.

It never runs the train itself: the merge daemon picks the batch up on its next pass and
hands it to local/bin/daemon_train.py, whose member gates re-check GitHub and remain
authoritative.

Member rules, each paid for in an incident:
  * At least two distinct PRs — a single PR takes the ordinary path.
  * A FRESH PR is never a train member: it merges alone, and listing it makes the whole
    train refuse.
  * The local branch tip must equal the PR head.  An unpushed helper commit made one
    batch be staged three times in a row.
  * A member set that was refused before is never re-staged automatically.
  * No member may carry an open claim (the in-repo claim list, local/bin/claim.sh).

Quiet window (a train needs the primary checkout untouched for its whole run): the daemon
alive, no train marker present, no local/bin/ci.sh running, the primary clean and on the
base branch at the published tip.

Provenance: kit-src/tmp-scripts/meta-stage-train.py, hard-coded to one repository path,
one cache directory and an owner-side copy of the claim tool.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import service_env  # noqa: E402

BASE_BRANCH = "main"


def select_members(rows: list[dict], *, refused: set[str] = frozenset()) -> tuple[list[dict], list[str]]:
    """Split candidate rows into train members and reasons for refusal.

    Each row: ``number``, ``head``, ``ok`` (open, non-draft, based on the base branch,
    CI and review summary success), ``fresh``, ``local_tip`` (the local branch tip, or
    ``""`` when the branch is not present locally), ``claim`` (the claim tool's report).
    Pure: no git, no network — the unit test drives this directly.
    """
    reasons: list[str] = []
    members: list[dict] = []
    for row in rows:
        number = row["number"]
        if not row.get("ok"):
            reasons.append(f"PR {number} is not approved and green at its current head")
            continue
        if row.get("fresh"):
            reasons.append(f"PR {number} is fresh; it merges alone and must not be in a train")
            continue
        tip = row.get("local_tip") or ""
        if tip and tip != row["head"]:
            reasons.append(f"PR {number}: local branch tip {tip[:10]} != PR head {row['head'][:10]} "
                           "(unpushed or stale local branch)")
            continue
        if "free" not in (row.get("claim") or "").lower():
            reasons.append(f"PR {number} is claimed: {(row.get('claim') or '')[:60]}")
            continue
        members.append({"number": number, "head": row["head"]})
    if len({m["number"] for m in members}) < 2:
        reasons.append("a train needs at least two distinct clean members")
        members = []
    key = ",".join(str(m["number"]) for m in members)
    if members and key in refused:
        reasons.append(f"members {key} were refused before: not re-staged automatically")
        members = []
    return members, reasons


#: One member key ("7,9,11") per line; written by auto-merge.py when a train ended with
#: the daemon down, read here so the same set is never staged again by itself.
REFUSED_FILE = "train-refused-members.txt"


def read_refused(daemon: Path) -> set[str]:
    try:
        return {line.strip() for line in (daemon / REFUSED_FILE).read_text(encoding="utf-8").splitlines()
                if line.strip()}
    except OSError:
        return set()


def remember_refused(daemon: Path, key: str) -> None:
    if not key:
        return
    daemon.mkdir(parents=True, exist_ok=True)
    with open(daemon / REFUSED_FILE, "a", encoding="utf-8") as handle:
        handle.write(key + "\n")


def _sh(*cmd: str) -> subprocess.CompletedProcess:
    return subprocess.run(list(cmd), capture_output=True, text=True)


def collect(repo: Path, numbers: list[int]) -> list[dict]:
    service_env.use_local_bin()
    from gh_common import api, latest_statuses
    from pr_merge import head_is_fresh

    claim = str(service_env.claim_tool())
    rows: list[dict] = []
    for number in numbers:
        pull = api(f"pulls/{number}")
        head = pull["head"]["sha"]
        statuses = latest_statuses(head)
        ci = statuses.get("local-ci/summary", {}).get("state")
        review = statuses.get("local-review/summary", {}).get("state")
        ok = (pull["state"] == "open" and not pull.get("draft")
              and pull["base"]["ref"] == BASE_BRANCH and ci == "success" and review == "success")
        try:
            fresh = bool(head_is_fresh(repo, f"github/{BASE_BRANCH}", head))
        except Exception:
            fresh = False  # fail closed: an unknown freshness is not "stale enough to train"
            ok = False
        tip = _sh("git", "-C", str(repo), "rev-parse", "-q", "--verify",
                  "refs/heads/" + pull["head"]["ref"]).stdout.strip()
        held = _sh("bash", claim, "check", str(number)).stdout.strip()
        print(f"PR {number} head {head[:10]} ci={ci} review={review} base={pull['base']['ref']} "
              f"fresh={fresh} claim={held[:60]}")
        rows.append({"number": number, "head": head, "ok": ok, "fresh": fresh,
                     "local_tip": tip, "claim": held})
    return rows


def quiet_window(repo: Path, daemon: Path) -> list[str]:
    bad: list[str] = []
    for name in ("train-approved.json", "train-approved.running.json"):
        if (daemon / name).exists():
            bad.append(f"{name} exists")
    pid = (daemon / "daemon.pid").read_text().strip() if (daemon / "daemon.pid").exists() else ""
    if not pid or _sh("kill", "-0", pid).returncode != 0:
        bad.append("the merge daemon is not running")
    # ci.sh is started with a relative path from the repository root, so this pattern is
    # machine-wide on purpose; waiting one window too long is the safe direction.
    if _sh("pgrep", "-f", "local/bin/ci[.]sh").stdout.strip():
        bad.append("a ci.sh run is in progress (it writes builds.jsonl in the primary)")
    if _sh("pgrep", "-f", f"{repo}/local/bin/(pr_train|daemon_train)[.]py").stdout.strip():
        bad.append("a train of this repository is already running")
    _sh("git", "-C", str(repo), "fetch", "-q", "github", BASE_BRANCH)
    if _sh("git", "-C", str(repo), "status", "--porcelain").stdout.strip():
        bad.append("the primary checkout is dirty (publish records first: records.sh)")
    if _sh("git", "-C", str(repo), "rev-parse", BASE_BRANCH).stdout != \
            _sh("git", "-C", str(repo), "rev-parse", f"github/{BASE_BRANCH}").stdout:
        bad.append(f"local {BASE_BRANCH} != github/{BASE_BRANCH}")
    if _sh("git", "-C", str(repo), "rev-parse", "--abbrev-ref", "HEAD").stdout.strip() != BASE_BRANCH:
        bad.append(f"the primary is not on {BASE_BRANCH}")
    return bad


def main(argv: list[str]) -> int:
    try:
        numbers = [int(a) for a in argv]
    except ValueError:
        print("usage: stage-train.py PR PR [PR...]", file=sys.stderr)
        return 2
    if len(set(numbers)) < 2:
        print("need at least two distinct PRs", file=sys.stderr)
        return 2
    repo = service_env.repo_root()
    daemon = service_env.daemon_dir()
    daemon.mkdir(parents=True, exist_ok=True)
    refused = read_refused(daemon)
    bad = quiet_window(repo, daemon)
    members, reasons = select_members(collect(repo, numbers), refused=refused)
    bad.extend(reasons)
    if bad or not members:
        print("NOT STAGED:")
        for line in bad:
            print(" -", line)
        return 3
    target = daemon / "train-approved.json"
    target.write_text(json.dumps({"members": members}) + "\n", encoding="utf-8")
    print("STAGED", target.read_text(encoding="utf-8").strip())
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
