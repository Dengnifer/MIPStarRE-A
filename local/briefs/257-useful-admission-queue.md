# Issue 257 packet schema
Norms and deployment boundaries: `local/protocols/useful-queue.md`.
Main's private cache `useful-queue/queue.json` starts as
`{"version":1,"enabled":false,"packets":[]}`. Packet fields: unique lowercase `id`,
`kind` (dispatch/review), positive `issue`, absolute clean prepared `worktree`, exact
40-hex `head`, `effort` (max/xhigh), `parents` (every prerequisite's issue/pr/merge_sha).
Dispatch adds role (prover/simplifier/blueprint/splitter/scout), absolute task_file and
task_sha256; review instead adds pr. Tasks are main-authorized UTF-8, not issue/log data.
