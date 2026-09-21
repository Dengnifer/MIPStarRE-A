#!/usr/bin/env python3
"""auto-merge.py — the model-free loop the operating session leaves running between turns.

Every interval (default 4 minutes), for at most a horizon (default 10 hours) or until
<state>/auto-merge.stop appears:

  1. keep the merge daemon alive (a refused train is reconciled by train-recover.sh);
  2. run the fail-closed gate (gate.py) over every open PR — it publishes the review
     summary only for a marked review at the exact head with green CI and no unchecked
     findings;
  3. a gated PR that is fresh merges alone through the daemon;
  4. two or more gated, unclaimed, non-fresh PRs that dry-merge cleanly are staged as ONE
     train, but only in a quiet window: no ci.sh running, no worker session holding the
     primary, the primary clean after the records commit.

It never edits repository files, never closes anything and never merges by hand.  PRs
listed in <state>/auto-merge.skip (one number per line) are left alone — that file
replaces the origin's hard-coded skip list.

The quiet window has one more interlock: anything that runs a worker OUTSIDE a lane and
therefore writes telemetry into the primary checkout (a one-off dispatch by hand) must
create <state>/worker-slot.busy while it runs and remove it afterwards.  A train needs
the primary untouched for its whole run, so this loop stages none while that file
exists.

Options: --interval SECONDS, --hours HOURS, --once (one pass, then exit; the unit test
and a dry check use this).

Provenance: kit-src/tmp-scripts/meta-auto-merge-v3.py, which hard-coded the repository
path, the cache directory and a list of six PR numbers.
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import service_env  # noqa: E402

BASE_BRANCH = "main"


def _load(name: str, filename: str):
    """Import a sibling tool whose file name contains a hyphen."""
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Loop:
    def __init__(self, repo: Path, state: Path, interval: int) -> None:
        self.repo = repo
        self.state = state
        self.daemon = state / "daemon"
        self.interval = interval
        self.log_path = state / "auto-merge.log"
        self.staged_last = ""
        self.stage_train = _load("kit_stage_train", "stage-train.py")

    # ---------------------------------------------------------------- helpers
    def sh(self, *cmd: str, **kwargs) -> subprocess.CompletedProcess:
        return subprocess.run(list(cmd), capture_output=True, text=True, cwd=str(self.repo), **kwargs)

    def log(self, message: str) -> None:
        self.state.mkdir(parents=True, exist_ok=True)
        stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        with open(self.log_path, "a", encoding="utf-8") as handle:
            handle.write(f"{stamp} {message}\n")

    def daemon_alive(self) -> bool:
        try:
            return self.sh("kill", "-0", (self.daemon / "daemon.pid").read_text().strip()).returncode == 0
        except Exception:
            return False

    def train_marker(self) -> bool:
        return (self.daemon / "train-approved.json").exists() or \
               (self.daemon / "train-approved.running.json").exists()

    def skip_set(self) -> set[int]:
        try:
            text = (self.state / "auto-merge.skip").read_text(encoding="utf-8")
        except OSError:
            return set()
        out = set()
        for line in text.split():
            try:
                out.add(int(line))
            except ValueError:
                pass
        return out

    # ------------------------------------------------------------------- pass
    def one_pass(self) -> None:
        service_env.use_local_bin()
        from gh_common import api, latest_statuses
        from pr_merge import head_is_fresh

        if not self.daemon_alive() and self.staged_last:
            self.stage_train.remember_refused(self.daemon, self.staged_last)
            self.log(f"train {self.staged_last} ended with the daemon down: remembered as refused")
            self.staged_last = ""
        if not self.daemon_alive():
            if (self.daemon / "stop").exists():
                self.log("the daemon is stopped on purpose (stop file): idle")
                return
            result = self.sh("bash", str(HERE / "train-recover.sh"))
            self.log("daemon was down: recover rc=%s %s"
                     % (result.returncode, (result.stdout or result.stderr).strip()[-160:]))

        skip = self.skip_set()
        pulls = [p for p in api("pulls?state=open&per_page=100")
                 if p["number"] not in skip and not p.get("draft") and p["base"]["ref"] == BASE_BRANCH]
        if pulls:
            gated = self.sh("python3", str(HERE / "gate.py"), *[str(p["number"]) for p in pulls],
                            env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
            for line in gated.stdout.splitlines():
                if ": GATED " in line or ": ADVERSE " in line:
                    self.log(line[:200])

        self.sh("git", "fetch", "-q", "github")
        base = self.sh("git", "rev-parse", f"github/{BASE_BRANCH}").stdout.strip()
        claim = str(service_env.claim_tool())
        rows = []
        for pull in pulls:
            head = pull["head"]["sha"]
            statuses = latest_statuses(head)
            if statuses.get("local-ci/summary", {}).get("state") != "success" or \
               statuses.get("local-review/summary", {}).get("state") != "success":
                continue
            try:
                fresh = bool(head_is_fresh(self.repo, base, head))
            except Exception:
                fresh = False
            rows.append({
                "number": pull["number"], "head": head, "ok": True, "fresh": fresh,
                "local_tip": self.sh("git", "rev-parse", "-q", "--verify",
                                     "refs/heads/" + pull["head"]["ref"]).stdout.strip(),
                "claim": self.sh("bash", claim, "check", str(pull["number"])).stdout,
            })

        refused = self.stage_train.read_refused(self.daemon)
        ready, reasons = self.stage_train.select_members(rows, refused=refused)
        if not ready:
            # A single gated non-fresh PR just waits, and a fresh PR merges alone
            # through the daemon: neither is worth a line every pass.
            interesting = [r for r in reasons
                           if "at least two" not in r and "is fresh" not in r]
            if interesting:
                self.log("not staging: " + "; ".join(interesting)[:200])

        busy = (self.state / "worker-slot.busy").exists()
        if ready and busy:
            self.log("a worker session holds the primary: the train for %s waits"
                     % [m["number"] for m in ready])
        elif ready and not self.train_marker() and not self.sh("pgrep", "-f", "local/bin/ci[.]sh").stdout.strip():
            numbers = [str(m["number"]) for m in ready]
            pre = self.sh("bash", str(HERE / "train-precheck.sh"), *numbers).stdout
            clean = [int(line.split()[1]) for line in pre.splitlines()
                     if line.startswith("PR ") and "merges clean" in line]
            key = ",".join(str(n) for n in clean)
            if key in refused:
                self.log(f"members {key} were refused before: not re-staged")
            elif len(clean) >= 2:
                self.sh("bash", str(HERE / "records.sh"), "records before the train")
                staged = self.sh("python3", str(HERE / "stage-train.py"), *[str(n) for n in clean],
                                 env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
                last = (staged.stdout.strip().splitlines() or ["?"])[-1][:160]
                self.log(f"stage {clean} -> {last}")
                if staged.returncode == 0:
                    self.staged_last = key
        elif not self.train_marker() and self.sh("git", "status", "--porcelain").stdout.strip():
            result = self.sh("bash", str(HERE / "records.sh"), "records")
            self.log("records: " + (result.stdout.strip().splitlines() or ["?"])[-1][:120])

    def run(self, hours: float, once: bool) -> int:
        self.state.mkdir(parents=True, exist_ok=True)
        (self.state / "auto-merge.pid").write_text(str(os.getpid()))
        self.log("started")
        end = time.time() + hours * 3600
        while True:
            try:
                self.one_pass()
            except Exception as exc:
                self.log(f"ERROR {type(exc).__name__}: {str(exc)[:200]}")
            if once or time.time() >= end or (self.state / "auto-merge.stop").exists():
                break
            time.sleep(self.interval)
        self.log("ended")
        return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--interval", type=int, default=240, help="seconds between passes")
    parser.add_argument("--hours", type=float, default=10.0, help="how long to keep going")
    parser.add_argument("--once", action="store_true", help="one pass, then exit")
    args = parser.parse_args(argv)
    loop = Loop(service_env.repo_root(), service_env.state_dir(), args.interval)
    return loop.run(args.hours, args.once)


if __name__ == "__main__":
    raise SystemExit(main())
