# Issue 257 handoff
Base: PR238 merge `32a32edee16d3932525e4b1da9f84009e1fbb13b`; session -02 preserves
`orc-257-20260906-01` work/time. No installation, agents, probes, merges or primary writes;
#252/#247 and proof budgets remain separate. Norms: `local/protocols/useful-queue.md`.
Main's private cache `useful-queue/queue.json` starts as
`{"version":1,"enabled":false,"packets":[]}`. Packet fields: unique lowercase `id`,
`kind` (dispatch/review), positive `issue`, absolute clean prepared `worktree`, exact
40-hex `head`, `effort` (max/xhigh), `parents` (every prerequisite's issue/pr/merge_sha).
Dispatch adds role (prover/simplifier/blueprint/splitter/scout), absolute task_file and
task_sha256; review instead adds pr. Tasks are main-authorized UTF-8, not issue/log data.
Publish through primary pr_open.py with --repo-root; detach primary ci.sh with --worktree.
A separate reviewer follows exact-green CI; this session cannot dispatch or merge.
After approved integration, stop old supervisor, update queue/router/dispatch/review together,
create STOP, inspect via `python3 local/bin/useful_queue.py`. Only main enables, removes STOP,
and runs `python3 local/bin/useful_queue.py --run --watch 5`. Ceiling ten, review costs two.
Main supplies useful packets and adopts uncertainty; never delete history to retry.
Preserved 577-test pass; resumed fixtures consolidate the same scenarios. Rerun focused/full
tests, Bash/Python syntax, whitespace and hooks; none is production admission evidence.
