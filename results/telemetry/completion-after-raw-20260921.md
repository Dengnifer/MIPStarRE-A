# Completion checkpoint after the raw-effect repair

Checked merge commit: `ee868cab15356655fddd68edba3e7c1e46e285f8` (PR668).
Command:

```
python3 scripts/completion_gate.py check --track qpbt --commit ee868cab15356655fddd68edba3e7c1e46e285f8 --json
```

Exit1, expected unfinished state. Machine-readable output is retained at
`/tmp/main-completion-after-raw-20260921.json`.

| Criterion | Result | Evidence |
| --- | --- | --- |
| C1 proof integrity | PASS |332 QPBT Lean files; no prohibited site |
| C2 headline axioms | DELEGATED |All four required audit assertions exist; values are checked by the CI build |
| C3 paper gaps terminal | FAIL |The register has no Terminal status column |
| C4 blueprint marked | FAIL |11 of528 linked nodes are unmarked and unexempted |
| C5 Lean comparator | FAIL |No verified QPBT completion-record block |
| C6 docs truthful | PASS |One document checked; no stale open-site claim |
| C7 artifact readiness | FAIL |DEVIATIONS.md, ARTIFACT.md and make_artifact.sh are not yet on main |

The C4 nodes are unchanged from the earlier baseline: canonical-complement
definition and lemma; generalized-pauli; pauli-observable-expansion; cl-func;
cl-dist; typed-cl-functions; typed-cl-distributions; qld-xz-lines; combine-map;
qld-4-13. Issue667 owns the source-faithful adoption/marking work. The narrow C6
check does not discharge issue666's broader truthfulness findings.

This is a checkpoint, not a completion claim. PR668's independently reviewed
head passed full CI and the required supplementary audit (1837 PASS,0 FAIL)
before service integration. Four-target official comparator verification,
artifact packaging, the remaining source/document audits and final build and
snapshot evidence remain required at the final declared commit.
