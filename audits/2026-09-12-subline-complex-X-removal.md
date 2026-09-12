# Complex X-factor removal under the directly indexed law

Issue #514; author session `prover-514-20260912-01`.
Base: `ae124f8f09ee002444ac5b9711822c0f1daae142`.

## Result and Mathematical Argument

`MIPStarRE.QPBT.subline_remove_X_factor_direct` is proved with its public
signature unchanged. No hypothesis, quantifier, error expression, evaluation
convention, or sampling domain changes. The supporting module
`ComplexOverlapGap.lean` proves the finite-distribution complex deficit estimate.

For a complete measurement with effects A_a and commuting projection families
B_a and C_a, form the difference with factor C_a(1-B_a). Apply Cauchy--Schwarz
to the positive sesquilinear form defined by A_a, with vectors C_a psi and
(1-B_a) psi. Sum the diagonal terms over outcomes. The first sum is at most
one by positivity and completeness. The second equals the deficit
1 - sum_a Re <psi, A_a B_a psi> by projectivity. The triangle inequality and
the existing real weighted Cauchy--Schwarz averaging lemma give the square
root of the averaged deficit. No commutation between B_a and C_a is used.

Specialize A to the placed concrete X-Z-X measurement, B to the completed
X-point projection, and C to the completed Z-point projection. Opposite
placements commute. The existing concrete deficit theorem bounds the deficit
by C_0 m^2 deltaLine; the final universal constant is sqrt(C_0).

## Source-Statement Audit

- Paper assumptions: the normalized expanded projective strategy, the concrete
  X-Z-X line measurement from paper lines 942-949, and the source subline law
  in Claim `claim:17-2`, lines 1168-1201 of
  `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
- Lean assumptions: unchanged `AdmissibleParams`, real epsilon,
  `ProjectiveSetting P epsilon`, and `SubLineWitness P`. The line measurement
  is constructed internally; no deficit or witness-construction premise is added.
- Paper conclusion: complex-modulus X-factor removal with error
  O(m sqrt(deltaLine)), averaged over the source law.
- Lean conclusion: the identical public complex sums and universal bound as
  the base declaration, over the directly indexed law with optional evaluations.
- Verdict: exact preservation of the assigned Lean statement; the existing
  distribution restriction remains. This proves `lem:claim-17-2-direct`, not
  the source entry `lem:claim-17-2`. Its scope and transport markers remain.

## Provenance and Prior Cost

The search covered main and all saved Git refs for the target and overlap
lemmas, including issue #405 and the saved issue #474 remote branch. No saved
proof of the current complex statement was found. The earlier arbitrary-witness
statement is mathematically different and was not reused as the target.

The positive-operator norm estimate and projection quadratic-form identities
come from `OverlapGap.lean`, introduced in the history including
`691b67159f9ead45b9de144df3bd46e015430e70`. The concrete deficit theorem was
introduced at `0131096351e3089d9246cc7c1dd861e71509a73b`. Both are reused by
import; no divergent branch or parallel witness construction is copied.

The checked-in telemetry provides the following prior relevant author records:

| Session | Recorded Wall Seconds | Recorded Usage |
| --- | ---: | --- |
| `fable-mathfix-118-claims-s1-20260905T1437Z` | 6016 | 625979 total tokens |
| `orc-414-20260909-01` | 3880 | unavailable |
| `prover-474-20260909-01` | 2328 | input 10510383, cached input 9952512, output 34369 |
| `prover-474-20260909-02` | 2565 | input 14707903, cached input 14459392, output 38132 |

These four records sum to 14789 wall seconds (4 h 6 min 29 s), before this
session. Cached input is part of input, not an additional cost. The historical
Fable total and Codex usage fields have different reporting conventions and
are not collapsed into a purported billing total. Earlier issue #405 work,
independent review, and other broader issue #118 work are not fully accounted
for by these four records; this is a lower bound, not a reset of the gap budget.
This session's terminal usage and duration are recorded by the existing dispatcher.

## Verification and Remaining Gates

Both Lean files pass focused typechecking without warnings. Fresh compiled
imports report exactly `propext`, `Classical.choice`, and `Quot.sound` for the
two new helpers, the reused concrete deficit theorem, and the target. There is
no `sorryAx` in those closures and no proof hole in either edited Lean file.

`leanblueprint web` succeeds with existing bibliography warnings. The initial
sync check encountered a stale generated, untracked `blueprint/lean_decls`;
the standard regeneration command repairs that local artifact. Publication
and exact-head CI use the primary checkout's workflow scripts. Their terminal
outcome is reported in the session handoff and PR evidence.

Source-law transport, the other source complex comparisons, and the separate
combined-line consistency construction remain open. Independent review is the
next author-separation gate; this session does not launch or perform it.

The first commit attempt was rejected by the unfaithful-marker hook because
the new blueprint proof completion mark conflicted with the retained
source-transport marker. The marker is required by this packet and its
deviation is still open. Both completion marks are therefore withheld on the
direct entry, whose prose explicitly records that its Lean proof is complete.
No hook is bypassed and the source entry remains unchanged.
