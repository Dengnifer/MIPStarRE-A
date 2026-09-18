# Declaration-level faithfulness audit — preserved seed-indexed low-degree soundness

Published as PR #600. Preservation of the PR #542 packet (`issue-527-proof-exists-ld-soundness`,
head `ac7cd808af2db7204ca2f056e38298f3b647d950`, authored 2026-09-12, never
reviewed) onto current `github/main` `2e25304971b70661bc990bbcddefbcde6edd0bd6`.

Authorized by the main session's disposition for PR 542 (`opus-requests.txt`,
line `542 MAIN DISPOSITION`) and by the meta session on 2026-09-18. This
session is the *publisher* of preserved work, not its author and not its
reviewer: a fresh independent review remains the next gate.

The immutable source is `references/qpbt-paper/` (MIP\*=RE, arXiv:2001.04383);
the secondary source is `references/neexp-paper/` (arXiv:1904.05870).

## 1. Why a new branch rather than a refresh of PR 542

PR 542 branched from `ae124f8f`. Since then `main` renamed the private helper
`map_uniformDistribution_seed` to the public `uniformDistribution_map_ldSeed`
and rewrote its two call sites — inside the exact block of declarations that
this packet relocates to a new file. Merging `main` into the PR branch would
have carried the pre-rename copy of that block into the new file and dropped
`main`'s public lemma, a silent content regression rather than an append-only
conflict. `Combining/Defs.lean`, `Combining/ErrorBounds.lean` and
`blueprint/src/chapter/ch13_qpbt_test.tex` also moved. The packet was therefore
re-applied declaration by declaration onto current `main`.

`python3 local/bin/dup_check.py check --pr 542` reports `no duplicate of 3
name(s)/declaration(s) on github/main`: nothing in the packet is already on
`main`, so nothing was dropped.

## 2. What the packet does, and what it deliberately does not do

The printed proof of `lem:ld-soundness`
(`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:439-458`)
reduces the theorem to Theorem 4.7 of the tensor-code paper via two steps the
source asserts but does not justify:

1. the claimed identity between the two-prover tensor code test for
   `code^(⊗m)` and the game `G^ld` at `k = 1`; and
2. the admissibility of the printed choice `K = m^3 d` against that theorem's
   own requirement `K ≥ 12 m (d + 1)`.

**Both remain open source gaps under issue #527. This branch does not prove
either of them, does not assume either of them, and does not claim that the
seed-indexed integration settles them.** The Lean proof reaches the same
conclusion by an entirely different route — the directly indexed game, the
combining reduction of NEEXP Theorem 4.43-from-4.40, and the correlated seed
dilation — so the two printed steps are *avoided*, not discharged. That
distinction is stated in the theorem docstring, in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, in
`docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex` and in the gap register.

No statement was weakened, strengthened, or given a bridge hypothesis. No
`sorry`, `admit`, `axiom` or `native_decide` was introduced.

## 3. Declaration table

`✔` in the axioms column means exactly `[propext, Classical.choice,
Quot.sound]`, verified by `#print axioms` from
`/tmp/opus-4c1273fd-probe.lean`, a probe file outside the worktree, against
the built worktree.

### 3.1 Declaration whose *proof* changes (statement untouched)

| declaration | file:line | paper locator | relation to paper | hypotheses | axioms |
| --- | --- | --- | --- | --- | --- |
| `MIPStarRE.QPBT.exists_ld_soundness` | `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:82` | `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-438` (Theorem, "Quantum soundness of the simultaneous classical low-degree test", blueprint `lem:ld-soundness`) | **exact** | `L : LdParams`; `0 < ε`; `S : Strategy (ldGame L)`; `S.IsProjective`; `1 - ε ≤ S.value`. No added hypothesis of any kind. | ✔ |

The statement is **character-for-character identical** to the one on
`github/main` (27 lines, `theorem exists_ld_soundness :` through `:= by`;
`diff` is empty). Only the tactic block changed: `sorry` was replaced by a
complete proof. Point-by-point against the paper:

* error function: the paper's `δ_ld(ε,q,m,d,k) = a (dmk)^a (ε^b + q^(-b) +
  2^(-bmd))` with universal `a ≥ 1`, `0 < b ≤ 1`, and the Lean `deltaLd`
  (`LowDegreeGameMeasurements.lean:377`) agree term by term. `deltaLd` is
  unchanged by this branch.
* conclusion: the paper's three displays — `A^{Point,u} ≈ G^Bob[...]`,
  `G^Alice[...] ≈ B^{Point,u}`, and `G^Alice_g ≈ G^Bob_g` — appear in the
  same order with the same bound `deltaLd a b ε L.q L.m L.d L.k`, the first
  two under the uniform law on `F_q^m` and the third with no question
  distribution (`uniformDistribution Unit`), exactly as the paper's closing
  sentence prescribes.
* quantifier order: `∃ a b, … ∀ L ε, … ∀ S, …` matches the paper's "There
  exists a function … such that … for all ε > 0 and parameter tuple … for all
  projective strategies".
* boundary encoding: positivity and the divisibility of `q` by `m` are carried
  by `LdParams`; finite-dimensional carriers and the total postprocessing
  `ldPointValuesOrZero`, which folds answers of the wrong form to the zero
  tuple so that the point family stays a POVM, are formal encodings already
  present on `main` and not introduced here.

Proof route (all inputs already proved on `main`): apply
`exists_direct_ld_soundness` to the correlated seed dilation
`ldStrategyToDirect`; compress both polynomial measurements with
`seedFiberCompressPolyMeasTuple`; the two mixed relations transfer exactly
through `ldStrategyToDirect_pointPolynomial_compression` and
`ldStrategyToDirect_polynomialPoint_compression`; the global relation is
recovered from those two plus the point-agreement branch
(`ldPointPair_consistencyDefect_le`, weight `1/9`, so `9ε`) by
`consistencyDefect_trans_le`, and the tuple collision bound below; the
resulting `E + 2√(9ε+E) + md/q` is absorbed by replacing `(a,b)` with
`(10a, b/2)`.

**Discrepancy to flag for the main session.** The packet instruction said the
printed theorem should keep its `sorry` "unless the packet honestly proves it,
which the scouts say it does not". Assessment: the packet **does** honestly
prove it. The evidence is the kernel, not the author's claim — the statement
is textually unchanged, the branch builds, and `#print axioms
MIPStarRE.QPBT.exists_ld_soundness` returns `[propext, Classical.choice,
Quot.sound]` with no `sorryAx`. Re-inserting a `sorry` over a complete
kernel-checked proof would have destroyed the packet's only unique
contribution, which this job exists to preserve, so the proof is published and
the discrepancy is raised here instead. The conservative half of the
instruction is honoured in full: see §4.

### 3.2 New declarations

| declaration | file:line | paper locator | relation to paper | hypotheses | axioms |
| --- | --- | --- | --- | --- | --- |
| `MIPStarRE.QPBT.polyTupleAgreement_avg_le_mdq` | `MIPStarRE/QPBT/Test/LowDegreeGameTheorems.lean:34` | none — formalization auxiliary. Nearest source idea: the Schwartz--Zippel step of `lem:ld-sandwich`, `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501` | **no paper counterpart** (auxiliary) | `L : LdParams`; `g g' : PolyTuple L`; `g ≠ g'` | ✔ |
| `MIPStarRE.QPBT.ten_sqrt_deltaLd_le` | `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedError.lean:19` | none — scalar arithmetic about the paper's `δ_ld`, `…08_…tex:414-417` | **no paper counterpart** (auxiliary) | `D : DirectLdParams`; `1 ≤ a`; `0 ≤ ε` | ✔ |
| `MIPStarRE.QPBT.error_and_collision_le_deltaLd` | `MIPStarRE/QPBT/Combining/DirectLowDegree/Transport/SeedError.lean:66` | none — scalar arithmetic about the paper's `δ_ld`, `…08_…tex:414-417` | **no paper counterpart** (auxiliary) | `D : DirectLdParams`; `1 ≤ a`; `b ≤ 1`; `0 < ε`; `ε ≤ 1` | ✔ |

Notes.

* `polyTupleAgreement_avg_le_mdq` bounds by `m d / q` the probability that two
  *distinct* polynomial tuples collide at a uniform point. It is proved by
  choosing one coordinate where they differ (`Function.ne_iff`) and invoking
  the existing `directPolynomialAgreement_avg_le_mdq`
  (`…/Transport/Simultaneous.lean:77`). There is no union bound over
  coordinates, so the bound does not degrade in `k`. It applies to tuples that
  have *already been constructed*; it does not construct simultaneous
  measurements coordinatewise, and therefore does not touch the refuted route
  of `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`, whose counterexample
  remains valid.
* The two `SeedError` lemmas are pure real-arithmetic facts about `deltaLd`
  (`10√(δ_ld(a,b)) ≤ δ_ld(10a,b/2)`, and `ε ≤ δ_ld`, `md/q ≤ δ_ld` for
  `ε ≤ 1`). They neither define nor alter anything the paper states.

### 3.3 Declarations relocated with no change of statement or proof

`MIPStarRE/QPBT/Test/LowDegreeGameMeasurements.lean` is new and holds the
sampling and measurement block that used to sit above the soundness theorem in
`LowDegreeGameTheorems.lean`, so that the soundness file may import the
`Combining.DirectLowDegree` stack without an import cycle. `diff` of `main`'s
`LowDegreeGameTheorems.lean` against the new `LowDegreeGameMeasurements.lean`
shows exactly two hunks: the module docstring, and the removal of the
soundness theorem. Every declaration below is byte-identical to `main`,
statement and proof, and none is re-stated or re-proved here:

`ldSpaceSplit` (:41, private), `map_uniformDistribution_point` (:62, private),
`uniformDistribution_map_ldSeed` (:86), `uniformDistribution_map_chiIndex`
(:110), `aLinePointDist_point_marginal_uniform` (:121),
`aLinePointDist_mem_line` (:148), `dLinePointDist_point_marginal_uniform`
(:170), `dLinePointDist_mem_line` (:197), `dLinePointDist_prefix_zero` (:223),
`isTypedCondLinearFamily_ldCL` (:242), `ldQuestionDistribution_eq_typedCL`
(:260), `ldQuestionDistribution_isTypedCL` (:304), `evalPolyTupleAt` (:351),
`pointSpaceOf` (:357), `ldPointQuestionOf` (:364), `ldPointValuesOrZero`
(:370), `deltaLd` (:377).

Paper locators for the block are unchanged
(`…08_…tex:243-287` for the sampling and measurement definitions,
`…08_…tex:414-417` for `deltaLd`); the relation of each to the paper is as it
was on `main` and is not re-litigated by this branch.

### 3.4 Non-declaration edits

| file | change |
| --- | --- |
| `MIPStarRE/QPBT.lean` | aggregate gains `…Test.LowDegreeGameMeasurements` |
| `MIPStarRE/QPBT/Combining/Defs.lean`, `…/DirectLowDegree/Game.lean`, `…/Combining/ErrorBounds.lean`, `…/Test/Completeness.lean` | import retargeted to the definitions module (breaks the cycle; keeps `Test` from importing the `Combining` stack) |
| `…/DirectLowDegree/SeedIndexedSoundness.lean` | one docstring sentence: the general seed-indexed theorem is no longer described as open |
| `blueprint/src/chapter/ch13_qpbt_test.tex` | prose in the proof of `lem:ld-soundness` and in `rem:ld-soundness-provider` / `rem:ld-soundness-simultaneity`. **No `\leanok` added** — see §4 |
| `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`, `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`, `docs/paper-gaps/qpbt-gap-register.md` | the general-`k` seed-indexed half is recorded as preserved here; both source imports are restated as open under #527 |

Stale tracker pointers in the `exists_ld_soundness` docstring were corrected:
issues #16 and #210 are closed, and #527 is the live tracker.

## 4. Blueprint marking

`lem:ld-soundness` already carried a *statement*-level `\leanok` on `main`,
pointing at `deltaLd` and `exists_ld_soundness`; that is unchanged and stays
accurate, since the statement is unchanged.

PR 542 additionally put a `\leanok` on the **proof** of `lem:ld-soundness`.
That marker is **not** carried over. The blueprint proof block transcribes the
printed tensor-code route, whose two verification obligations are still open;
certifying that block would assert the formalization follows the printed proof,
which it does not. A LaTeX comment at the node records the reason and leaves
the editorial decision to the main session. This is the conservative
direction: the blueprint understates what Lean has, never the reverse.

No other `\leanok` was added or removed anywhere on this branch.

## 5. What is still open under issue #527

1. The tensor-code game correspondence (source assertion 1 above).
2. The auxiliary parameter bound `K ≥ 12 m (d + 1)` for the printed choice
   `K = m^3 d` (source assertion 2 above).
3. The downstream use of the low-degree game at dimension `2m+2`, where
   admissibility gives only `m ∣ q`; the repository's directly indexed carrier
   avoids the obstruction without discharging it.

None of the three is touched by this branch. PR 542 should not be closed by
this publication; the main session decides its disposition.

## 6. Provenance

The mathematics is the PR 542 packet's, authored 2026-09-12 by session
`prover-527-20260912-01`; its own author-side audit is preserved verbatim in
that PR as `audits/2026-09-12-issue-527-ld-soundness.md` and records the
earlier work it reuses (`5c40a3b8`, `14aad87d`, `e1d8eaa2`, `8d593835`) and
about 3 h 40 min of prior prover wall time. No proof was re-authored here and
no new prover was started at the source signature.
