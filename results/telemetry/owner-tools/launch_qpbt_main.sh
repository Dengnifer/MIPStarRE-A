#!/usr/bin/env bash
# launch_qpbt_main.sh — RETIRED.  Use local/bin/main-session.sh.
#
# This script started a codex TUI in tmux `qpbt` with a hard-coded /goal line and pasted
# /tmp/qpbt-main-handoff.md into it.  Three things made it wrong to keep:
#   - it invoked `codex` with no model, effort or speed tier, so the main session ran at
#     whatever the ambient default was;
#   - its sibling main-session-astra-v3.sh `exec`'d an absolute ~/.local/bin/codex, bypassing
#     the PATH shim and therefore the run's service_tier (2026-09-12: the owner switched to
#     fast speed three times and the main session never received it);
#   - it carried a goal and a handoff path inside the script, so the briefing lived in two
#     places at once.
#
# local/bin/main-session.sh replaces all of it: model, effort, CODEX_HOME and speed come
# from local/bin/run_mode.py get, and codex is invoked THROUGH the installed shim.  The goal
# is set by the owner (or rendered by goal-keeper.sh from run_mode.py show), and the state
# briefing is the run brief plus the persona, not a file in /tmp.
#
# To start the main session inside the tmux pane, from the repository root:
#     tmux send-keys -t qpbt 'cd <repo> && local/bin/main-session.sh' Enter
#
# This stub stays only so an old crontab row, alias or note reaches the replacement instead
# of failing silently.  It never starts a session.
set -u

CACHE_ROOT="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}"
OWNER_BIN="${MIPSTARRE_OWNER_BIN:-$CACHE_ROOT/owner-bin}"
ROOT="${MIPSTARRE_REPO_ROOT:-}"
if [ -z "$ROOT" ] && [ -r "$OWNER_BIN/repo-root" ]; then ROOT="$(cat "$OWNER_BIN/repo-root")"; fi
if [ -z "$ROOT" ]; then ROOT="$HOME/MIPStarRE-qpbt"; fi

cat >&2 <<EOF
launch_qpbt_main.sh is retired (see results/telemetry/owner-tools/README.md).
Start the main session with:

    cd $ROOT && local/bin/main-session.sh

which reads the model, effort, CODEX_HOME and speed tier from run_mode.py and goes through
the installed PATH shim.  Nothing was started.
EOF
exit 2
