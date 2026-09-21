# `local/bin/session/` — running a main session unattended

These are the tools the operator uses to start the project's MAIN session, keep it
working, notice when its API key dies, hand it over to a successor and stop it.
Everything they need comes from `local/project.json` through `config.sh`; nothing
here knows the name of a repository, a tmux session, a key or a host.

Every tool takes `--dry-run` (or `KIT_DRY_RUN=1`) and then prints what it would
send or launch without touching tmux or codex. Start there when you are new.

## The order of a normal day

| step | command |
|---|---|
| is a key alive? | `local/bin/session/probe-key.sh <key>` |
| bring everything up | `local/bin/session/resume.sh --key <key> --lanes <n> --briefing <file> --goal <file>` |
| where do we stand? | `local/bin/session/status.sh` |
| say something to the main session | `local/bin/session/say.sh --mode idle\|interrupt\|queue --file <f>` |
| hand the session over | `local/bin/session/standdown.sh --minutes 30 --reason "..." --next-layout "..."` |
| start the successor | `local/bin/session/main-tui.sh start --key <key> --briefing <file>` |
| land by a time, killing nothing | `local/bin/session/pause.sh graceful $(date -d "+3 hours" +%s)` |
| stop everything now | `local/bin/session/pause.sh now --reason "..."` |
| run anything at a time | `local/bin/session/timer.sh <epoch> --detach -- <command...>` |

`resume.sh` also starts the three things that run by themselves:
`goal-keeper.sh` (re-sends the goal, keeps turns short), `key-watch.sh` (proves a
key is dead before retiring it) and `pause-watch.sh` (acts on the `cutoff` and
`pause-now` markers). Each writes `<name>.{pid,stop,log}` in the state directory
and stops when you `touch <name>.stop`.

## Four rules these tools encode

1. **A key is probed before anything starts.** A main session on a dead key looks
   idle; every turn fails silently and a night is lost.
2. **Pane text is a hint, never evidence.** A key is retired only after a direct
   probe of its own endpoint fails — once when the answer names a quota or auth
   refusal, twice 45 s apart for a bare 401/402/403/429/503. A retired key never
   comes back on its own.
3. **A long paste becomes an attachment.** One Enter does not always submit it,
   so `say.sh` presses Enter again while `Pasted Content` is still in the
   composer, and reports when it could not confirm the send.
4. **Tab queues, Escape interrupts.** To reach a session whose goal loop never
   idles, queue the text (`--mode queue`) and it arrives at the end of the turn.

## The state directory

`$KIT_STATE_DIR` (`<cache_root>/watchdog/`) is outside the repository and holds
everything these tools remember: `goal-text`, `turn-max`, `main-key`,
`max-codex*`, `key-disabled/<key>`, `paused`, `cutoff`, `pause-now`,
`main-standdown.done`, `handoff.md`, `events-meta.log`. None of it is committed.

## Knobs that are not project configuration

`KIT_DRY_RUN=1`, `KIT_SAY=<path>` (another message tool), `KIT_MAIN_PID_CMD`
(how to find the running TUI on an unusual setup), `KIT_KEY_HOME_<KEY>` (a key
home before `local/project.json` names it), and the `KIT_KEYWATCH_*` thresholds
and error patterns. `config.sh` does not touch these, so they survive it.
