# Comparator publication validation, 2026-09-21

PR 663 is published at `a534c7f97ba34fd561ae03134f90b81ee4e395c1`, with tree
`23fa6da9aa3e50abf8438369479b7ab762e54df0`. PR 660 head
`418e0271d898b5cee443c48490056ef0bff55eab` is its second parent. MAIN verified
that the published Lean source is unchanged from the previously built source
tree `9e681b196dd70bef743de35de5f402237d2a2f72`.

Canonical CI finished successfully in 421 seconds. Its manifest is complete
(`partial: false`), all eight steps succeeded, and MAIN read back all nine
`local-ci/*` statuses as success on the exact published commit. The detached
wrapper returned 0. Evidence:

- Manifest: `~/.cache/mipstarre-dev/ci-manifests/pr663-a534c7f97ba34fd561ae03134f90b81ee4e395c1.json`.
- Logs: `~/.cache/mipstarre-dev/ci-logs/663/a534c7f97ba34fd561ae03134f90b81ee4e395c1/`.
- Operator wrapper log: `/tmp/main-ci663-a534c7f9-20260921.log`.

CI required a separate blueprint axiom audit. MAIN ran
`python3 scripts/blueprint_leanok_axioms.py --ci` in the unchanged PR worktree,
from 11:44:26 to 11:44:36 UTC. It checked 1837 declarations across 368 modules:
1837 passed, none failed. No proof-level `\leanok` declaration depended on
`sorryAx`. The exit receipt is 0 and the full log is
`/tmp/main-blueprint-audit663-a534c7f9-20260921.log`.

The author thread `01a0c3ac-2fe0-7b43-bee6-d27e35913279` completed at
11:33:39.603 UTC after 1182.847 seconds and was closed before admitting the
independent PR 659 reviewer. Its terminal usage and all predecessor costs are
retained in `sessions.jsonl`. No author review or comparator acceptance was
claimed. The independent PR 663 review is prepared but waits for the sole
native delegate slot; no second model session was admitted.

Both PR 659 and PR 663 are fresh under the published merge predicate against
main `2f4f0a01859a9ac575f59fc468061684d8303fc5`. If independently approved while
still fresh, each belongs on the ordinary merge path, not a train. Recheck
after any intervening merge. MAIN never invokes the merge operation.

Official comparator acceptance of all four target closures, including generated
private auxiliaries, remains unestablished. The official run must use the
unchanged comparator, real landrun and nanoda, the permitted standard axioms,
and a verified merged-main revision. Local compilation and the preceding CI
checks do not discharge that requirement. PR 650 and issues 666 and 667 retain
their separate documentation obligations; the artifact is not yet complete.
