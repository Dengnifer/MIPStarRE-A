---
id: "0004"
branch: "issue-0007-github-native-workflow"
issue: "0007"
base: "main"
state: "open"
head_sha: "5b9befcb1bf644b4aadcace2d238455b007b1837"
ci_status: null
review_state: null
fix_iterations: 0
auto_fix: true
labels: ["bug", "ci", "documentation", "infrastructure"]
created: "2026-08-31T14:17:20Z"
merged_commit: null
---

# feat(local): add GitHub write-through records

### Motivation

- The owner-directed 2026-08-31 re-hybridization moved track A to the standalone
  `Dengnifer/MIPStarRE-A` repository, but the operative lifecycle still writes
  only local issue and PR records. Issue #0007 tracks the required adapter and
  cites `HANDOFF.md` step 0 and the corresponding `EVOLUTION.md` decision.
- GitHub publication must retain the local same-head CI/review merge gate and a
  durable offline record; isolated `gh` calls would duplicate records after an
  ambiguous failure and lose post-merge recovery state.

### Description

- Add a shared, retry-hardened GitHub adapter with stable local-id markers,
  explicit local-to-GitHub identities, per-operation reconciliation state, and
  deterministic fake-`gh` tests.
- Integrate issue creation/closure, PR publication/merge, exact-SHA CI statuses,
  and exact-SHA COMMENT reviews while preserving atomic local records and the
  existing merge gate.
- Replace broad branch pushes with explicit-ref publication, seed the migrated
  issue/PR mappings, and update the normative workflow documentation and
  evolution ledger. Lean, blueprint, paper sources, and frozen GitHub Actions
  remain unchanged.

### Testing

- Run the focused Python regression suite with a fake `gh` and temporary Git
  remotes; no test may mutate the real GitHub repository.
- Run `local/bin/validate_tree.py`, shell/Python syntax checks, and
  `git diff --check`.
- Run `local/bin/ci.sh 0004`; the final entry will be updated with the exact
  gate results before merge.

---
Closes #0007
