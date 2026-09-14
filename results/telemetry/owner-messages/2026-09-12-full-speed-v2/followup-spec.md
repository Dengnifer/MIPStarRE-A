# Follow-up work items on top of the full-speed-v2 PR (owner instructions of 2026-09-12 09:xxZ)

## W8 — chsh build farm, enabled only in full speed mode
Owner rule: in full speed mode the compute and storage of the chsh server are used alongside ghz; outside full speed mode chsh is
never used. Facts (side session report, snapshot/chsh/report.md; script snapshot/chsh/build-on-chsh.sh):
- chsh = 220.181.114.116:6681 user drx from the Mac; from ghz use HostName 192.168.1.18 port 22 (key authorized; known_hosts in
  /tmp/chsh-setup/known_hosts; ghz's ~/.ssh/config already has "Host chsh"). aarch64, 192 cores, 2 TB RAM, /data/users/drx ZFS
  10 TB free. Layout mirrors ghz: /home/drx/MIPStarRE-qpbt (checkout, behind main), ~/.elan Lean 4.32.0 aarch64,
  /data/users/drx/mipstarre-cache/{packages (Mathlib, byte-identical to ghz), hot-main, seed/build (hardlink seed), builds/<lane>}.
- No codex on chsh, and none must be installed (internet about 16 KB/s); chsh is a pure build node fed from ghz by rsync (86.7 MB/s).
- build-on-chsh.sh <worktree> [targets...] runs ON ghz: rsync sources (excluding .lake .git .worktrees results/telemetry) to
  chsh builds/<name>, cp -al seed, lake build there, rsync back only written files under .lake/build/{lib,ir}, exit with lake's code;
  per-lane flock; measured cold lane 15 s, one-file change 17 s round trip, full warm build 19 min.
- Refresh of chsh's checkout + seed when main moves: rsync the primary checkout to chsh and rebuild the seed (report step 4).
Design requirements: (1) the offload is a function of the run mode only: `run_mode.py get compute.offload` (or the equivalent field
the v2 briefing defines) must be true only when the brief says full speed AND lists chsh under compute hosts; default false;
the pause sets it false; (2) lane runner and ci.sh build steps call the offload when enabled and FALL BACK to the local build on any
ssh/rsync failure (never fail a lane because chsh is unreachable), logging which host built; (3) a seed refresh runs after every
merge (daemon hook) or at least hourly while enabled, detached, with its own lock; (4) the pre-push per-file gate (`lake env lean`)
stays on ghz; (5) the script is versioned under results/telemetry/owner-tools/build-on-chsh.sh and installed by the v2 installer
(owner-tools/install.sh or whatever W4 named it) into ~/tools or ~/.local/bin on ghz, with the ssh options from the report (HostName
192.168.1.18, port 22, BatchMode, UserKnownHostsFile under ~/.cache/mipstarre-dev/watchdog/chsh/known_hosts copied from
/tmp/chsh-setup/known_hosts by the installer); (6) tests: bash -n, a dry-run mode that prints the commands, and a unit test for the
mode gating; (7) runbook text in local/protocols (full speed section): what chsh is, the rule, how to verify usage
(`watchdog/chsh/offload.log`), what to do if chsh is down (nothing: automatic fallback).

## W9 — full speed mode = every role on astra, reviewers included; telemetry records the resolved model
Owner rule: in full speed mode all subagents are astra, reviewers included (review is a semantic-alignment phase and needs the
strong model as much as proving). Requirements: (1) the run-brief template's full-speed example sets `models.override: "astra-all"`
and the runbook says so; `run.speed == fast` without an explicit override defaults to astra-all (documented); (2) dispatch.sh /
model_policy.py record the RESOLVED model and the override source in the session row (W2 claims this: verify and add a test); (3)
the PATH shim no longer rewrites models (W2/W4: verify) and the installer removes the rewrite; (4) the fixer default
(`MIPSTARRE_FIX_MODEL`) and lane defaults follow the policy (auto), never a hard-coded model; (5) a check in the janitor or the
daily digest that counts sessions per resolved model so a wrong model shows up on #27 within an hour.
