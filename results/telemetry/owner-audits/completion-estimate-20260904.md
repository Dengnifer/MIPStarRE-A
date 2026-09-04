# Completion estimate — 2026-09-04 03:40Z (owner session, Fable 5.1 workflow of 6 read-only agents)

Question: days until every stage-4.3 obligation on the QPBT route is proved, `pauli_soundness`
connected without bridge assumptions, blueprint status matching, main green.

## Measured (main 22d3eef → c240b6b)
- Denominator: 168 `sorry` sites on main (165 after PR 95) + 26 in open PR 46 (ch16 skeleton) = 194.
  LDT dependency: 0 real sorries. Filed packets name 62 sites; 132 (68 %) have no packet
  (ch14 Observables 50, ch15 Combining 24, ch16 21, conditional linearity, completeness).
- Difficulty split of the ~141 still to prove after open PRs merge: routine 52 / medium 51 / hard 39.
- Fleet rate (stage 4.3, first 4 h): successful prover session median 32 min, ~3.9 sites per
  session on routine algebra; prover launch failures 41 %, reviewer 39 % (429 waves + multi-agent
  fan-out, now contained); 1.8 review rounds per PR (3.2 over project history); Lean PR
  open→merge median 1.55 h; merged-to-main ~19 sites per fleet-day (lagging indicator).
- Long poles: Magic Square rigidity #77 (from-scratch robust self-test, no source text on the host,
  external axiom forbidden); NV quantum linearity theorem (currently "external result", \notready);
  LD-soundness transport with a theorem-level gap in the paper route
  (docs/paper-gaps/qpbt_ld-dimension-divisibility.tex, repair route #71/#74 not established);
  13 of 28 ch15 nodes \notready; PR 46 (26 sites) unreviewed after 15 reviewer attempts;
  five owner decisions are hard stops before the inventory can read zero.

## Estimates
| source | optimistic | expected | pessimistic |
|---|---|---|---|
| estimator (rates × classes, 3 slots, 70 % uptime) | 3 d | 6 d | 18 d |
| refuter "too pessimistic" (statements fixed → ch14/15 parallel; capacity ~4 productive slots) | 2.5 d | 4 d | 11 d |
| refuter "too optimistic" (hard content unmeasured; no source text; LD gap; \notready chain; hand-back) | 10 d | 21–28 d | 60+ d |

Owner-session synthesis: the routine/medium remainder (~100 sites) is a 3–5 day job at the
current cap; the calendar is set by three research-grade serial proofs (rigidity, linearity,
LD transport) that no session has attempted yet. Expected ≈ 3 weeks; optimistic 10 days;
pessimistic 6+ weeks (open-ended if the LD repair needs new definitions).

Levers, largest first: (1) decide the five owner questions now, above all whether the NV
linearity theorem stays an explicit external statement; (2) start #77 split into 4–5 sub-issues
and the LD transport immediately, so the hard-content rate is measured within a day;
(3) keep one slot on reviewers and merge green PRs within ~1.5 h; (4) file packets for the
132 unfiled sites ahead of the provers; (5) hold concurrency ≤5 to keep 429 failures ~20 %.
