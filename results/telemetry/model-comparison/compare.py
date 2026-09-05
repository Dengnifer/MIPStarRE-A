#!/usr/bin/env python3
"""Compare the codex models used for dispatched subagents, by role.

Side product of the 2026-09-05 switch from gpt-5.6-sol to gpt-6-astra.
Standard library only; see README.md in this directory.  Re-run with:

    python3 results/telemetry/model-comparison/compare.py
"""

import json
import os
import re
import statistics
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
SESSIONS = os.path.join(ROOT, "results/telemetry/sessions.jsonl")
CAPTURE_DIR = os.path.join(ROOT, "results/telemetry/sessions")
REVIEWS = os.path.join(ROOT, "results/telemetry/reviews")
SNAPSHOT = os.path.join(ROOT, "results/telemetry/github-snapshot/open-pulls.json")
LANES = os.path.expanduser("~/.cache/mipstarre-dev/watchdog/lanes")
PULLS_CACHE = os.path.expanduser("~/.cache/mipstarre-dev/model-comparison/pulls.json")
REPO = "Dengnifer/MIPStarRE-A"
SWITCH = datetime(2026, 9, 5, 15, 46, tzinfo=timezone.utc)  # astra becomes the default
MODEL_RE = re.compile(r"^gpt-[A-Za-z0-9._-]+$")


def jsonl(path):
    try:
        with open(path, errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if line:
                    try:
                        yield json.loads(line)
                    except ValueError:
                        continue
    except OSError:
        return


def dig(obj, *path):
    for key in path:
        if not isinstance(obj, dict):
            return None
        obj = obj.get(key)
    return obj if isinstance(obj, str) and MODEL_RE.match(obj) else None


# ------------------------------------------------------------------ the model

def model_from_stream(path, limit=40):
    """Model from a codex event stream: rollout session_meta/turn_context/world_state.

    Capture files (`codex exec --json`) carry no model field today; this
    function is used for both so a future capture format is picked up for free.
    """
    if not path or not os.path.exists(path):
        return None
    try:
        with open(path, errors="replace") as fh:
            for i, line in enumerate(fh):
                if i >= limit:
                    break
                if '"model"' not in line:
                    continue
                try:
                    evt = json.loads(line)
                except ValueError:
                    continue
                pay = evt.get("payload") or {}
                for cand in (dig(pay, "model"),
                             dig(pay, "base_instructions", "provenance", "model"),
                             dig(pay, "state", "model"),
                             dig(evt, "model")):
                    if cand:
                        return cand
    except OSError:
        return None
    return None


def lane_models():
    """issue -> model, from `dispatch <role> for #N (model X, ...)` lane lines."""
    out = defaultdict(set)
    pat = re.compile(r"\(model (gpt-[A-Za-z0-9._-]+)")
    try:
        names = os.listdir(LANES)
    except OSError:
        return {}
    for name in names:
        if not name.endswith(".lane.log"):
            continue
        issue = name[: -len(".lane.log")]
        try:
            with open(os.path.join(LANES, name), errors="replace") as fh:
                for line in fh:
                    m = pat.search(line)
                    if m:
                        out[issue].add(m.group(1))
        except OSError:
            continue
    return {k: next(iter(v)) for k, v in out.items() if len(v) == 1}


def parse_ts(value):
    """`start`/`end` are ISO with a colonless offset (`+0800`), which
    datetime.fromisoformat only accepts from Python 3.11 on."""
    text = re.sub(r"([+-]\d{2})(\d{2})$", r"\1:\2", str(value or "").replace("Z", "+00:00"))
    try:
        stamp = datetime.fromisoformat(text)
    except (TypeError, ValueError):
        return None
    if stamp.tzinfo is None:
        stamp = stamp.replace(tzinfo=timezone.utc)
    return stamp.astimezone(timezone.utc)


def derive_model(row, lanes):
    if row.get("model"):
        return row["model"], "registry"
    for src, path in (("capture", row.get("capture")), ("rollout", row.get("rollout"))):
        full = path if (path and os.path.isabs(path)) else (os.path.join(ROOT, path) if path else None)
        got = model_from_stream(full)
        if got:
            return got, src
    issue = str(row.get("issue") or "")
    if issue in lanes:
        return lanes[issue], "lane-log"
    start = parse_ts(row.get("start"))
    if start is not None:
        return ("gpt-5.6-sol" if start < SWITCH else "gpt-6-astra"), "time-rule"
    return "unknown", "none"


# ---------------------------------------------------------------- the outcome

def load_pulls():
    """PRs by head branch: gh (cached outside the repo) plus the open-PR snapshot."""
    pulls = {}
    for pr in json.load(open(SNAPSHOT)) if os.path.exists(SNAPSHOT) else []:
        branch = (pr.get("head") or {}).get("ref")
        if branch:
            pulls[branch] = {"number": pr.get("number"), "merged": bool(pr.get("merged_at")),
                             "state": (pr.get("state") or "").upper()}
    fresh = None
    try:
        proc = subprocess.run(
            ["gh", "pr", "list", "--repo", REPO, "--state", "all", "--limit", "500",
             "--json", "number,state,headRefName,mergedAt"],
            capture_output=True, text=True, timeout=180)
        if proc.returncode == 0:
            fresh = json.loads(proc.stdout)
            os.makedirs(os.path.dirname(PULLS_CACHE), exist_ok=True)
            with open(PULLS_CACHE, "w") as fh:
                json.dump(fresh, fh)
    except (OSError, ValueError, subprocess.SubprocessError):
        fresh = None
    if fresh is None and os.path.exists(PULLS_CACHE):
        try:
            fresh = json.load(open(PULLS_CACHE))
        except (OSError, ValueError):
            fresh = None
    for pr in fresh or []:
        if pr.get("headRefName"):
            pulls[pr["headRefName"]] = {"number": pr.get("number"),
                                        "merged": bool(pr.get("mergedAt")),
                                        "state": pr.get("state") or ""}
    return pulls


FINDING_RE = re.compile(r"^\s*-\s*\[[ xX]\]\s*F\d+\b")


def count_findings(row):
    """Ledger findings of the review this session produced, or None."""
    paths = []
    pr = str(row.get("pr") or "")
    if pr and os.path.isdir(REVIEWS):
        hits = [os.path.join(REVIEWS, f) for f in sorted(os.listdir(REVIEWS))
                if f.startswith("pr%s-" % pr)]
        if len(hits) == 1:  # more than one body per PR cannot be joined to a session
            paths.append(hits[0])
    cap = row.get("capture") or ""
    if cap.endswith(".jsonl"):
        last = cap[: -len(".jsonl")] + ".last.md"
        paths.append(last if os.path.isabs(last) else os.path.join(ROOT, last))
    for path in paths:
        try:
            text = open(path, errors="replace").read()
        except OSError:
            continue
        if "findings:begin" in text:
            text = text.split("findings:begin", 1)[1].split("findings:end", 1)[0]
        elif "## Findings" in text:
            text = text.split("## Findings", 1)[1].split("\n## ", 1)[0]
        else:
            continue
        return sum(1 for line in text.splitlines() if FINDING_RE.match(line))
    return None


# ------------------------------------------------------------------ reporting

def med(values):
    return statistics.median(values) if values else None


def fmt(value, digits=0):
    if value is None:
        return "n/a"
    return ("%.*f" % (digits, value)) if digits else "%d" % round(value)


def pct(num, den):
    return "n/a" if not den else "%.0f%%" % (100.0 * num / den)


def bucket(row):
    role = row.get("role") or "unknown"
    if role == "prover" and re.fullmatch(r"pr\d+", str(row.get("issue") or "")):
        return "fixer (autofix)"
    return role


def summarize(rows, role, pulls):
    wall = [r["wall_s"] for r in rows if isinstance(r.get("wall_s"), (int, float))]
    usage = [r.get("usage") or {} for r in rows]
    out = [u.get("output") for u in usage if isinstance(u.get("output"), (int, float))]
    inp = [u.get("input") for u in usage if isinstance(u.get("input"), (int, float))]
    cached = sum(u.get("cached_input") or 0 for u in usage)
    turns = [r["turns"] for r in rows if isinstance(r.get("turns"), (int, float))]
    cells = [str(len(rows)), pct(sum(1 for r in rows if r.get("exit") == 0), len(rows)),
             fmt(med(wall)), fmt(statistics.mean(wall) if wall else None),
             fmt(med(out)), fmt(med(inp)), pct(cached, sum(inp) or 0),
             fmt(statistics.mean(turns) if turns else None, 1)]
    if role in ("prover", "fixer (autofix)"):
        prs = [pulls.get(os.path.basename(r.get("worktree") or "")) for r in rows]
        known = [p for p in prs if p]
        cells += [pct(len(known), len(rows)),
                  pct(sum(1 for p in known if p["merged"]), len(known))]
    if role == "reviewer":
        f = [n for n in (count_findings(r) for r in rows) if n is not None]
        cells += ["%s (n=%d)" % (fmt(med(f), 1), len(f))]
    return cells


HEAD = ["model", "sessions", "exit 0", "wall_s med", "wall_s mean", "out tok med",
        "in tok med", "cached in", "turns mean"]


def table(role, rows, pulls):
    head = list(HEAD)
    if role in ("prover", "fixer (autofix)"):
        head += ["PR opened", "of those merged"]
    if role == "reviewer":
        head += ["ledger findings med"]
    by_model = defaultdict(list)
    for r in rows:
        by_model[r["_model"]].append(r)
    lines = ["| " + " | ".join(head) + " |",
             "|" + "|".join(["---"] * len(head)) + "|"]
    for model in sorted(by_model, key=lambda m: (-len(by_model[m]), m)):
        lines.append("| `%s` | %s |" % (model, " | ".join(summarize(by_model[model], role, pulls))))
    return "\n".join(lines)


def main():
    rows = list(jsonl(SESSIONS))
    lanes = lane_models()
    sources = Counter()
    for row in rows:
        row["_model"], src = derive_model(row, lanes)
        sources[src] += 1
    pulls = load_pulls()
    by_role = defaultdict(list)
    for row in rows:
        by_role[bucket(row)].append(row)

    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    parts = ["# codex model comparison — sol vs astra, by role", "",
             "Generated by `results/telemetry/model-comparison/compare.py` at %s." % now,
             "Read `README.md` in this directory first: the assignment of models to",
             "tasks is not random, so nothing here is causal.", "",
             "Sessions: **%d** from `results/telemetry/sessions.jsonl`. Model derivation source: "
             % len(rows) + ", ".join("%s %d" % (k, v) for k, v in sources.most_common()) + ".",
             "Overall: " + ", ".join("`%s` %d" % (m, n) for m, n in
                                     Counter(r["_model"] for r in rows).most_common()) + ".", ""]
    for role in sorted(by_role, key=lambda r: (-len(by_role[r]), r)):
        parts += ["## %s (%d sessions)" % (role, len(by_role[role])), "",
                  table(role, by_role[role], pulls), ""]
    parts += ["`in tok med` is `usage.input` (which includes cached input); `cached in` is",
              "`sum(cached_input)/sum(input)` over the group. Reviewer findings come from the",
              "review ledger (`results/telemetry/reviews/` when one body matches the PR, else",
              "the session's own `.last.md`); `n=` is how many sessions it was derivable for.",
              "Prover outcomes join the session worktree branch to a pull request.", ""]
    report = "\n".join(parts)

    with open(os.path.join(HERE, "latest.md"), "w") as fh:
        fh.write(report)
    counts = Counter(r["_model"] for r in rows)
    entry = "- %s — %d sessions: %s\n" % (
        now, len(rows), ", ".join("%s %d" % (m, n) for m, n in counts.most_common()))
    readme = os.path.join(HERE, "README.md")
    if os.path.exists(readme):
        with open(readme, "a") as fh:
            fh.write(entry)
    sys.stdout.write(report)
    sys.stdout.write("\nAppended to README.md run log: " + entry)


if __name__ == "__main__":
    main()
