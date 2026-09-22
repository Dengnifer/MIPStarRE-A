# Direct Subline Complex Estimates

Issue #689, continuing the scalar component of issue #118. Author session:
`mathfix-689-20260922-01`. Base: `ccba9a6756c58c0efa5cda04747e6a97935d71fb`.
This is an author statement-integrity audit, not independent review.

## Source Defect

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.
The X-Z-X measurement is defined at 942-949. Claims `claim:17-1` (1140-1166),
`claim:17-2` (1168-1201), and `claim:17-3` (1204-1239) compare complex
expectations, under the source subline law, with respective errors
`O(sqrt(deltaQ))`, `O(m sqrt(deltaLine(epsilon)))`, and
`O(sqrt(m) (deltaP^(1/4) + deltaQ^(1/4) + epsilon^(1/4)))`.

The first calculation writes `W^2` for the squared-norm operator of
`W = Q - M_Z M_X`; the correct operator is `W` adjoint times `W`.
The ordered product need not be Hermitian. For example, on C^2 let
`X = diag(1,0)`, let `Z` have all entries `1/2`, and set
`psi = (1,i)/sqrt(2)`. Then `<psi, Z X psi> = (1-i)/4`.
Discarding its imaginary part cannot justify a complex-modulus estimate.
This is an obstruction to the earlier real-part proof, not a counterexample
to the constructed-measurement scalar conclusion.

The earlier enlarged-domain Claim 17-2 has a separate counterexample: the
uniform constant-polynomial POVM `T_(c_a,c_b) = q^(-2) I` gives
`A(T) = q^(-2)` and `B(T) = q^(-1)` at zero strategy error. The difference
is `7/64` at `q=8`, while the proposed error is zero. Its verification and
the distinction from the defined sandwich remain in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. This session does not
replace the sandwich by such arbitrary witnesses in the X-factor estimate.
Indeed, that uniform POVM has X marginal `q^(-1) I`, which is not a projection
when `q>1`, whereas the concrete sandwich's X marginal is a line projector.

## Corrected Statements And Proofs

Write `J`, `A`, and `B` for the directly indexed overlaps of the defined
X-Z-X measurement with the completed joint point measurement, the ordered
Z-X product, and the Z point measurement, respectively. The law and optional
evaluation conventions are exactly the existing ones.

1. `subline_replace_by_ordered_product_direct` proves
   `norm(J - A) <= 2 * deltaQ^(1/2)` for every admissible parameter tuple,
   projective setting, joint point witness, and directly indexed subline witness.
   It has no line-consistency, reality, or transport assumption. Regrouping the
   constructed POVM by the two evaluations produces a complete POVM `E_a`.
   Complex weighted Cauchy-Schwarz bounds the gap by the square root of
   `E sum_a <W_a psi, E_a W_a psi>`. Completeness makes the other factor one.
   Since `0 <= E_a <= I`, this is at most the square root of the state-dependent
   squared distance. Undefined point outcomes contribute zero. The joint uniform
   point marginal and `CombinedPointsWitness.orderedZX_dist_le` give `4 deltaQ`.
   The constant is therefore exactly `2`, with the source's square-root scaling.
2. `subline_Z_overlap_eq_real_direct` proves `B = (Re B : C)`. More generally
   it accepts any line POVM, since no consistency is needed for this identity.
   The placed line effect and placed Z point effect are positive and act on
   opposite registers. Their product is positive by
   `ProjectiveSetting.place_mul_place_nonneg`. Mathlib's
   `Matrix.PosSemidef.dotProduct_mulVec_nonneg` makes its quadratic form a
   nonnegative real complex number. Finite sums and real weights preserve
   reality, including at undefined evaluations with zero point effect.
3. `subline_Z_term_near_one_direct` applies this identity to the existing
   `subline_Z_term_near_one_re_direct` without changing its hypotheses or
   constant. Thus `norm(B-1) = abs(Re B-1)` and the existing fourth-root
   bound holds in complex modulus. The inherited proof chooses constant `2`.
4. `subline_concrete_Z_term_near_one_direct` specializes that estimate to the
   defined sandwich. For each polynomial point-error function `deltaQ`, the
   proved `combined_line_measurement_consistency` supplies a polynomial
   line-error function `deltaP`. The proof constructs the record with
   `T := S.combinedLineMeasurement`; its degree fields and consistency field
   are proved, not assumed as equality or construction inputs.

The first two results are in `Combining/SubLineComplex.lean`, imported by the
nearest existing parent `Combining/Claims.lean`; the quantitative Z results
are in that parent. The general complex distance lemma there reuses
`norm_weighted_sum_inner_le_sqrt_mul_sqrt`, whose positive-operator proof
uses the Mathlib square root and complex inner-product Cauchy-Schwarz.
No mathematical definition or game specification changes.

The already proved `subline_remove_X_factor_direct` is unchanged. On the
same concrete measurement the three results give, by the triangle inequality,

```text
norm(J - 1) <= 2 sqrt(deltaQ) + C_X m sqrt(deltaLine(epsilon))
  + C_Z sqrt(m) (deltaP^(1/4) + deltaQ^(1/4) + epsilon^(1/4)).
```

The first and third real-part theorem signatures and compatibility aliases
are preserved. The new first bound also implies the old real-part conclusion
on the concrete domain by `abs(Re z) <= norm(z)`. The third modulus bound is
exactly the old real-part bound, not a loss in its error parameter.

## Counterexample Audit And Minimality

No realness of an ordered product is assumed. The explicit nonreal example
above therefore satisfies the analytic domain and is covered by the complex
Cauchy-Schwarz bound. Replacing the norm by an absolute real part would be
weaker and insufficient; assuming realness or point-factor commutation would
unnecessarily strengthen the source hypotheses. The first estimate does not
need a paired-line consistency witness and omits it. The Z-reality identity
does not need projectivity or consistency of the line POVM and omits them.
The uniform-POVM Claim 17-2 counterexample cannot replace the fixed sandwich
in the three-claim chain. No stricter sufficient repair was selected.

At zero distance the weighted estimate gives a zero complex gap. At undefined
evaluations the completed point effects are zero; no value is fabricated.
The probability and unit-vector hypotheses exclude empty total mass and
unnormalized states. No positivity hypothesis on the error is added: the
nonnegative squared distance already implies its nonnegativity.

A numerical adversarial check used NumPy seed 689 for 100 cases, each with
five nonuniformly weighted samples (one weight zero), random two-dimensional
projective line/point bases, the actual X-Z-X POVM, and a normalized complex
state on C^2 tensor C^2. Every complex gap was at most the square root of
the directly computed squared distance. The largest ratio was
`0.30201872642584565`; the largest imaginary residual of the Z overlap was
`4.102791083305806e-17`. Z overlaps were in `[0,1]` to tolerance `1e-12`.
The commuting zero-distance case was checked separately. These floating-point
calculations are diagnostics; the proofs above and Lean establish the results.

## Complete Consumer Comparison

In the paper, the only direct quantitative use of Claims 17-1 and 17-3 is
the chaining at 1241-1242 establishing `eq:qld-combined-lines-consistency`
in the proof of `lem:qld-4-13`. Claim 17-3 also refers back to Claim 17-2's
Cauchy-Schwarz calculation at 1212 and 1218. The new direct-law statements
supply exactly that scalar calculation, including its complex modulus, for
the same measurement. They do not identify the source and auxiliary laws.
The subsequent `O(m^2 deltaP)` assertion at 1243-1246 requires a joint law
not supplied by the separate marginals, and is not discharged here.

The only direct source use of `lem:qld-4-13` outside its own proof is the
classical-test construction in `lem:qld-4-7` at 1278-1282. That construction
feeds the marginal/decoded measurements at 1423, `lem:qld-construct-the-paulis`
at 1465 (and its estimates at 1492, 1584), its helper at 1627, and
`lem:qld-unitary` at 1671, hence the Pauli soundness conclusion. This session
changes none of their statements or witnesses. In particular it does not
claim the printed `poly(m^2 epsilon,md/q)` error for `lem:qld-4-13`; that is
the independent issue #598, not a consequence of these scalar estimates.

Scanning active blueprint environments, attaching proofs by `\proves{}` or
to their preceding labelled statement, gives the following complete
`\uses{}` descendant set of `lem:claim-17-1`, `lem:claim-17-2`, `lem:claim-17-3`:

| Descendant | Consumer comparison |
| --- | --- |
| `lem:qld-4-13` | Scalar triangle available on the direct law; source carrier, evaluations, and printed error remain open. |
| `thm:qld-supplied-direct-polynomial-consistency` | Assumes an extended-line witness and consumes only its existing consistency error; unchanged. |
| `lem:qld-supplied-scalar-point-measurement` | Identifies the supplied point readout by outcome postprocessing; unchanged. |
| `thm:qld-supplied-scalar-polynomial-consistency` | Postprocesses the preceding supplied-witness conclusion; unchanged. |

Actual references to the three claims also occur in
`lem:claim-17-1-re-direct`, `lem:claim-17-2-direct`,
`lem:claim-17-3-re-direct`, the proof of `lem:qld-4-13`,
`rem:qld-4-13-source-defects`, the proof of
`lem:paired-subline-overlap-estimates`, and `lem:subline-joint-overlap`.
The unlabelled paragraph before `lem:claim-17-2-direct-real` defines its two
overlaps by these displays. All remain valid: the existing real or complex
auxiliary results are preserved, and the source-law qualifications are still
needed. Editorial references to open source results are not certified by the
new direct-law lemmas. No blueprint completion marks were edited.

The only existing import of `Claims.lean` is `MIPStarRE/QPBT.lean`, which is
imported by `MIPStarRE.lean`. No existing Lean proof calls the new declarations.
The existing downstream real route is independently implemented by
`ExtendedLines/Estimates.lean` and consumed by `Apply.lean`; it retains its
own witness/error domain. The blueprint's supplied-witness descendants are
implemented in `ExtendedLineGame/SuppliedDirectSoundness.lean`,
`ExtendedLineGame/NativePointConsistency.lean`, and
`ExtendedLineGame/SuppliedScalarPolynomialConsistency.lean`. These are the
focused comparison consumers; full CI belongs to main.

## Statement Integrity

Paper assumptions: admissible parameters, a normalized expanded projective
strategy, the constructed X-Z-X line POVM, the combined-point bounds and, for
the quantitative Z estimate, the combined-line bound, all on the source law.
Paper conclusions: the three complex-modulus estimates stated above.

Lean assumptions: the existing projective setting and direct subline law;
the first result additionally takes the established combined-point data.
The Z-reality identity takes only a line POVM. The general quantitative Z
version takes the same point and line witnesses as its real predecessor;
the concrete version instead takes the source's polynomially controlled point
family and derives line data internally. No assumed reality, new bridge input,
undefined-value replacement, or weakened error is introduced.

Verdict: complex scalar conclusion proved, with the original asymptotic
constants and powers; still a scope restriction to the directly indexed law
and completed evaluations. The printed source-law claims remain open.

## Validation And Handoff

The two edited Lean modules type-check; the axiom audit of all five new public
results and the reused Claim 17-2 reports exactly `propext`, `Classical.choice`,
and `Quot.sound`. The source-header audit reports no changed public headers.
The hook installation check, paper-gap style check, and whitespace check pass.
The gap note builds with `latexmk`; its generated files remain under `.lake/`.

The full blueprint synchronization check has an unchanged baseline failure:
1,866 references absent from `blueprint/lean_decls`, zero missing Lean
declarations, zero stale registry entries, four orphan completion marks and
two header/proof-mark warnings. The blueprint tree and checker are byte-for-byte
unchanged from the dispatched base. The registry/mark work is outside this
assignment; this is not reported as a green full-CI result.

Focused checks pass for both re-export consumers, `ExtendedLines/Estimates.lean`,
`Apply.lean`, and all three supplied-witness modules listed above. Normal
commit-hook results are recorded in the session receipt.
Main owns publication, full locked CI, independent review,
the #27 announcement and the event/design-decision records. No source-law
semantic correction is adopted here.

## Budget Provenance

The original gap anchor remains `2026-09-05T19:24:00Z`. Preserve the historical
ten attempts / 19,931 seconds baseline, the later bounded tranches, and the
associated #405, #414, #474/PR #478, #480 and #512 records. The packet reports
13 canonical `mathfix118` rows totaling 26,509 seconds; this is a subset, not
a complete cross-issue total and not an additional amount to add to the
overlapping historical baseline. The aggregate total beyond this subset was
not supplied and is not reconstructed as zero.

Main explicitly authorized this additional 3,600-second Astra tranche in
`/tmp/main-subline-complex-packet-20260922.md` under section 6 of
`local/protocols/issues-prs.md`. This session started at
`2026-09-22T18:18:29+09:00`. Charge its actual elapsed time in addition to the
carried records; the exact receipt gives the finish checkpoint. There is no
self-extension, new gap anchor, publication, child worker, or owner contact.
