# Global polynomial-pair completion: issue #513

## Result and scope

The public statement and proof hole of `exists_globalPairWitness` are unchanged
from `ae124f8f09ee002444ac5b9711822c0f1daae142`. This packet does not certify
`lem:qld-4-7`. It recovers the algebraic restriction and projective completion
from the saved #119 branch and proves two estimates for the completed
measurement in `Combining/PairCompletion.lean`. The source theorem imports
that module; no neighboring construction obligation is edited.

Write `c(p) = alpha * p_X(x) + beta * p_Z(z)`. For a measurement `T` on
extended polynomials, let `R_p = T_{c(p)}` and let `C` be its completion at
one specified polynomial pair. For any answer map `e`, opposite measurement
`B`, and vector `psi`, the new pointwise estimate is

\[
\sum_{a\ne b}\langle\psi|C_{[e=a]}\otimes B_b|\psi\rangle
\leq \|\psi\|^2-
\sum_p\langle\psi|R_p\otimes B_{e(p)}|\psi\rangle.
\]

There is also a uniformly averaged version for question-dependent `e` and
`B`, stated with `consistencyDefect`. Neither estimate requires projectivity
or normalization. They follow because completion adds positive operators,
so it increases diagonal agreement. Completeness expresses the off-diagonal
overlap as the squared state norm minus diagonal agreement. Thus these
estimates require a retained-overlap lower bound before they can imply the
paper's consistency conclusion; that bound is not assumed as a new input.

## Source and provenance

The paper was read before the Lean construction:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`,
especially `eq:qld-g-non-separable`, `eq:qld-sgg-completeness`,
`eq:qld-sgg-mhat-sandwich`, and the final completion paragraph. The matching
blueprint entry is `lem:qld-4-7`.

Searches of main and all saved Git refs found no discharged version of the
target. The relevant saved proof content is:

- `cb6d86d8947a940da537543b19d95aebd205e35d`: algebraic recovery,
  injectivity, restriction, missing-operator identity, and projective
  completion. These proofs are recovered, not rederived.
- `3de03d0a`: the combined-outcome evaluation identity. The recovered text
  comes from their saved descendant `aaa5cb48ee485ec79cbd7a2ae6d39432fb30937d`.
  Its target theorem still contains the same proof hole.
- `c9de155f`, saved #295 branch: `PolynomialImageBounds.lean` proves
  `nonlinear_mass_le_ordered_error` and preceding scalar-linearity bounds.
  This is useful remaining proof content; it is not copied into this packet.
  The displayed ordered error still needs to be bounded from the strategy.
- Main's `exists_global_pair_error_bound` already proves absorption of the
  established first-route error. Main's `exists_direct_ld_soundness` proves
  the directly indexed soundness theorem. Neither is reimplemented here.

The recovery is limited to the algebraic declarations and their matching
blueprint support node. No branch merge, conditional line-constructor proof,
or source-signature change is imported.

## Remaining mathematical work

The following are construction obligations, not evidence that the source
assertion is false. No non-derivability claim is made by this packet.

1. Obtain the extended-game data from the actual strategy with the
   established error bound and apply direct soundness. Existing helpers
   accepting an `ExtendedLinesWitness` do not construct that witness.
2. Produce the extended-polynomial measurement on the required local
   measurement space with the needed quantitative guarantees. Naimark
   dilation alone changes that space; its use must respect the fixed spaces
   of `GlobalPairWitness`.
3. Derive both ordered correlations `eq:qld-g-42` and `eq:qld-g-43` from
   the soundness measurement and the combined-point witness.
4. Apply the scalar-linearity and wrong-variable-block estimates to derive
   `eq:qld-g-non-separable`. The scalar-linearity lemma on the saved #295
   branch does not establish the other two classes of excluded polynomials.
5. Derive the retained point-overlap estimates from
   `eq:qld-s-good-and-bad` through `eq:qld-sgg-mhat-sandwich` for both Pauli
   bases and both heterogeneous placements. The new averaged completion
   estimate then applies with `e_u = evalAt W u`.
6. Use the existing scalar error bound and preserve the universal quantifier
   order, strict inequalities on the constants, and the source domain.

The source-import discrepancies in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` are unchanged. Proving a
directly indexed alternative does not prove the cited tensor-code game
correspondence or its numerical parameter condition.

## Statement-integrity audit

- Paper assumptions: admissible parameters and a projective Pauli-basis
  strategy succeeding with probability at least `1 - epsilon`, with
  `epsilon > 0`.
- Lean assumptions: exactly the preexisting `AdmissibleParams`, positive
  error, and `ProjectiveSetting`; there is no new witness or residual input.
- Paper conclusion: universal `a > 1` and `0 < b < 1`, projective global
  polynomial-pair measurements on both expanded local spaces, and both
  point-consistency displays for each Pauli basis with the stated error.
- Lean conclusion: unchanged `GlobalPairWitness` with
  `deltaQld a b epsilon m d q` and the same quantifier order.
- Verdict: the target statement is preserved with its faithful finite-space
  encoding; its proof remains open. The new auxiliary statements are valid
  completion estimates with the retained overlap explicit, not a weakened
  replacement of the source theorem.

The blueprint adds `lem:qld-combined-pair-completion` and
`lem:qld-completed-pair-agreement` with proof-level completion tags. The
source-labelled theorem remains `notready`.

## Focused verification

- `lake env lean` succeeds on `PairCompletion.lean` and `Apply.lean`.
- The latter retains its five original direct holes. The new module has no
  `sorry`, `admit`, axiom declaration, or prohibited bypass.
- A fresh local object-file check lists only `propext`, `Classical.choice`,
  and `Quot.sound` for recovery, evaluation, the missing-operator identity,
  the completion effect formula, projectivity, and both new estimates.
- `exists_globalPairWitness` still lists `sorryAx`. In the same check,
  `exists_direct_ld_soundness`, `exists_global_pair_error_bound`, and
  `MIPStarRE.LDT.Test.mainFormal` do not list `sorryAx`.
- `leanblueprint web` succeeds, with missing-bibliography warnings.
- Blueprint synchronization and changed-declaration coverage pass after
  regenerating the declaration inventory following the web build.
- `scripts/install_git_hooks.sh --check` and `git diff --check` succeed.

The runtime axiom-check file is
`~/.cache/mipstarre-dev/sessions/prover-513-20260912-01-axioms.lean`.
Exact-head CI and publication results are recorded in the PR and session
handoff rather than predicted by this source checkpoint.

## Prior attempts and cost accounting

This attempt continues the #119 mathematical work; it does not reset its
history. The committed session registry records three earlier prover sessions:

| Session | Recorded seconds | Input | Cached input | Output |
| --- | ---: | ---: | ---: | ---: |
| `prover-119-20260906-01` | 102 | 268207 | 232448 | 1120 |
| `prover-119-20260906-02` | 1289 | 7386353 | 7237760 | 22646 |
| `prover-119-20260906-03` | 536 | 10817634 | 10618112 | 33073 |
| Total | 1927 | 18472194 | 18088320 | 56839 |

Their reported reasoning count totals 17733 and is a component of output,
not an additional token total. Two later #119 scout records are
`scout-native-01a07d38-20ff-7cb1-85d0-b0af65d873d7` and
`space_sol_point313_comparison_scout`. They report 25850.915 and 4167.951
seconds of session span, respectively, with `usage_scope: unknown` and
explicitly nonadditive cumulative token snapshots. These spans and token
snapshots must not be charged as known active proof time or added to the
prover totals. Their existence and unknown attribution are retained here.

The present session is `prover-513-20260912-01`, started at
`2026-09-12T04:56:37Z`, with a 60-active-minute limit. Its additive final
usage is supplied by the existing dispatcher record; neither that record
nor historical telemetry is edited by this packet.
