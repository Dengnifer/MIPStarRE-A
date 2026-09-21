#!/usr/bin/env python3
"""gate.py PR [PR...] — the fail-closed review gate the operating session runs.

For each PR it requires, at the EXACT current head: an open non-draft PR based on the
project's integration branch; one review carrying the `mipstarre-review` marker for
that head; a VERDICT trailer; zero unchecked finding boxes; every `local-ci/*` context
success; a complete CI manifest for that head; and no GitHub CHANGES_REQUESTED review
on that head.  Only then does it publish `local-review/summary` = success and read the
status back; an adverse verdict publishes failure instead.  Absent or stale evidence
publishes nothing at all.

Rules this enforces, and why (origin incidents):
* A verdict on an earlier SHA never carries over — the marker pins the head.
* The status is read back after posting: a write that was not observed is not evidence.
* The PR is claimed through the IN-REPO claim list (local/bin/claim.sh) for the length
  of the posting, so two parties cannot gate the same PR at once.

Provenance: kit-src/tmp-scripts/meta-gate.py, whose repository path, repository slug
and reviewer account name were hard-coded.  The review-author check is informational
here: on an organisation-owned repository the posting account is legitimately not the
slug owner, so it may not fail a gate closed.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import service_env  # noqa: E402

service_env.use_local_bin()
from gh_common import api, latest_statuses, post_status  # noqa: E402
from pr_merge import CI_CONTEXTS, CLOSES_RE, UNCHECKED_FINDING_RE, VERDICT_RE  # noqa: E402

REPO = service_env.repo_root()
CLAIM = service_env.claim_tool()
BASE_BRANCH = "main"
REVIEW_CONTEXT = "local-review/summary"


def _claim(action: str, number: int, note: str) -> subprocess.CompletedProcess:
    return subprocess.run(["bash", str(CLAIM), action, "main", "review", str(number), note],
                          capture_output=True, text=True)


def gate(number: int) -> str:
    pull = api(f"pulls/{number}")
    if pull["state"] != "open" or pull.get("merged") or pull.get("draft"):
        return f"PR {number}: not an open non-draft PR"
    head = pull["head"]["sha"]
    why: list[str] = []
    info: list[str] = []
    if pull["base"]["ref"] != BASE_BRANCH:
        why.append(f"base is {pull['base']['ref']}, not {BASE_BRANCH}")

    reviews = api(f"pulls/{number}/reviews", paginate=True)
    marker = f"<!-- mipstarre-review pr={number} head={head} -->"
    marked = [r for r in reviews if r["commit_id"] == head and marker in (r.get("body") or "")]
    if not marked:
        return (f"PR {number}: no marked review at the current head {head[:10]}: "
                "nothing posted")
    # If a retry ever left two marker reviews on one head, the NEWEST is operative.
    review = marked[-1]
    body = review["body"] or ""
    verdict_match = VERDICT_RE.search(body)
    unchecked = len(UNCHECKED_FINDING_RE.findall(body))
    statuses = latest_statuses(head)
    current = statuses.get(REVIEW_CONTEXT, {}).get("state")

    if review.get("state") != "COMMENTED":
        why.append(f"review state {review.get('state')}, expected COMMENTED "
                   "(local verdicts are COMMENT reviews; adverseness travels in the status)")
    author = ((review.get("user") or {}).get("login") or "?")
    try:
        owner = service_env.slug().split("/")[0]
    except RuntimeError:
        owner = ""
    if owner and author.lower() != owner.lower():
        info.append(f"review posted by {author}, not the slug owner {owner}")

    if not verdict_match:
        why.append("VERDICT trailer missing")
    elif not body.rstrip().endswith("VERDICT: " + verdict_match.group(1)):
        info.append("verdict trailer is not the last line")

    if [r for r in reviews if r.get("state") == "CHANGES_REQUESTED" and r.get("commit_id") == head]:
        why.append("GitHub CHANGES_REQUESTED review on this head")

    bad_ci = [c for c in CI_CONTEXTS if statuses.get(c, {}).get("state") != "success"]
    if bad_ci:
        why.append("CI not all success: " + ",".join(bad_ci))

    manifest = service_env.ci_manifest(number, head)
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
        if data["head_sha"] != head or data["conclusion"] != "success" or data["partial"]:
            why.append("CI manifest not a complete success")
    except Exception as exc:
        why.append(f"CI manifest unreadable: {exc}")

    # Which issues GitHub will auto-close on merge: reported, never decided here
    # (merge gate 7 of pr_merge.py is the authority).
    subprocess.run(["git", "-C", str(REPO), "fetch", "-q", "github"], check=False)
    base_sha = api(f"git/ref/heads/{BASE_BRANCH}")["object"]["sha"]
    merge_base = subprocess.run(["git", "-C", str(REPO), "merge-base", base_sha, head],
                                capture_output=True, text=True).stdout.strip()
    messages = ""
    if merge_base:
        messages = subprocess.run(
            ["git", "-C", str(REPO), "log", "--format=%B", f"{merge_base}..{head}"],
            capture_output=True, text=True).stdout
    closing = list(dict.fromkeys(CLOSES_RE.findall((pull.get("body") or "") + "\n" + messages)))
    if closing:
        info.append(f"closing references {closing} (merge gate 7 checks them)")

    verdict = verdict_match.group(1) if verdict_match else "?"
    try:
        url = f"https://github.com/{service_env.slug()}/pull/{number}#pullrequestreview-{review['id']}"
    except RuntimeError:
        url = None

    suffix = (" [" + "; ".join(info) + "]") if info else ""
    if verdict == "CHANGES_REQUESTED" or unchecked > 0:
        if current != "failure":
            post_status(head, REVIEW_CONTEXT, "failure",
                        f"Independent review {review['id']}: {verdict}; "
                        f"{unchecked} unresolved finding(s)", url)
        return (f"PR {number}: ADVERSE review {review['id']} {verdict} unchecked={unchecked} "
                f"at {head[:10]}: summary failure" + suffix)
    if verdict not in ("APPROVED", "COMMENTED"):
        why.append(f"verdict {verdict}")
    if why:
        return (f"PR {number}: NOT gated at {head[:10]} (review {review['id']} {verdict}): "
                + "; ".join(why) + suffix)
    if current == "success":
        return (f"PR {number}: already gated: review {review['id']} {verdict} head {head} "
                f"summary success" + suffix)

    claimed = _claim("claim", number, f"gate of review {review['id']}")
    if claimed.returncode != 0:
        return f"PR {number}: claim refused: {claimed.stdout.strip()[:120]}"
    try:
        post_status(head, REVIEW_CONTEXT, "success",
                    f"Independent review {review['id']}: {verdict}; zero unresolved findings", url)
        # Read the status back: an unobserved write is not evidence.
        read_back = latest_statuses(head)
        if read_back.get(REVIEW_CONTEXT, {}).get("state") != "success":
            raise RuntimeError(f"{REVIEW_CONTEXT} did not read back as success")
        note = (f"review {review['id']} {verdict} exact {head[:10]}, all {len(CI_CONTEXTS)} CI "
                "contexts, zero unchecked; summary success posted and read back")
        outcome = f"PR {number}: GATED head {head} review {review['id']} {verdict}"
    except Exception as exc:
        note = f"gate failed while posting: {exc}"
        outcome = f"PR {number}: {note}"
    _claim("release", number, note)
    return outcome + suffix


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__.splitlines()[0], file=sys.stderr)
        return 2
    for arg in argv:
        try:
            print(gate(int(arg)))
        except Exception as exc:  # fail closed and keep going: one bad PR is not all of them
            print(f"PR {arg}: ERROR {type(exc).__name__}: {exc}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
