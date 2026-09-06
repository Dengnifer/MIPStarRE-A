# Issue 257 packet schema
Norms and deployment boundaries: `local/protocols/useful-queue.md`.
Main's private cache `useful-queue/queue.json` starts as
`{"version":1,"enabled":false,"packets":[]}`. Packet fields: unique lowercase `id`,
`kind` (dispatch/review), positive `issue`, absolute clean prepared `worktree`, exact
40-hex `head`, `effort` (max/xhigh), `parents` (every prerequisite's issue/pr/merge_sha).
Dispatch adds role (prover/simplifier/blueprint/splitter/scout), absolute task_file and
task_sha256; review instead adds pr. Tasks are main-authorized UTF-8, not issue/log data.
Dispatch may also specify `sandbox` under the protocol's role restrictions; omission
retains the historical default and packet identity. No existing packet is migrated.

## Main-only held-publication reconciliation checklist
For original IDs `proof-publication-{243,244,246}-after-queue-merge` only:
- Keep HOLD and the supervisor stopped; preserve intents, fingerprints, attempts,
  receipts, captures, refusals and append-only events. Each observed attempt is 1.
- Bind `prover-{243,244,246}-20260906-02` to original tickets respectively:
  `cccc03cad2e5477b85c42d8bcce82aae`, `8c97d1457c7a449693d2aa715c4e3f00`,
  `ab2721671bb4407da61aa56f82245877`. Exit-zero receipts are not publication evidence.
- Read exact current GitHub heads/statuses through gh_common.py and check worktree
  ownership. Main assigns deterministic canonical publication completion, not an
  author rerun, renamed packet, sandbox retrofit, or automatic retry.
- After disposition and no outstanding clients, main alone reconciles under
  controller then router locks and decides HOLD. Independent review and CI for
  this new extension must precede deployment. This checklist executes nothing;
  no #27 publication/substitute or owner-inbox action is authorized.
