# Issue 509: unrestricted supplied point error

Session `prover-509-20260912-01`, based on main
`ae124f8f09ee002444ac5b9711822c0f1daae142`.

The assigned theorem `exists_extendedLinesWitness_ofPointsWitness` cannot be
discharged faithfully with its current quantifiers. Its signature and existing
proof hole are preserved. Two independently proved lemmas verify parts of a
counterexample to this auxiliary domain; neither is a proof of the target.

## Source and Obstruction

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-4-13`, lines 1020--1034. Its points are those constructed by
`lem:qld-4-10` and coarse-grained by `lem:qld-4-12`, lines 993--1018. The
blueprint entry is `lem:qld-4-13`, with its proof discrepancy recorded in
`rem:qld-4-13-source-defects`. Both were read before proving the auxiliary facts.

The target chooses a polynomial error function before quantifying over an
arbitrary scalar `deltaQ` and every point witness at that error. A supplied
witness need not have error controlled by the strategy error. This problem
persists after the extended scalar coarse-graining.

For `m = d = 1`, choose a perfect projective strategy and supply deterministic
point answers `(x^2, 0)` on both sides. Perfect strategies exist by the source's
`lem:pauli-completeness`, at
`08_classical_and_quantum_low_degree_tests.tex:1232-1255`. The supplied family is
projective, and a finite scalar bounds all its witness comparisons. Its extended
point answer is `alpha * x^2`. The direct X-axis question branch has mass `1/8`.
When `alpha` is nonzero, every allowed degree-one line answer agrees with that
quadratic on at most two of the `q` field points. Positivity and completeness
extend the bound to arbitrary POVMs, giving either orientation a defect at least

```
(1/8) * (1 - 1/q) * (1 - 2/q).
```

This tends to `1/8`, whereas `IsPolyErr₂` forces `deltaCombine 0 (1/q)` to tend
to zero. The nonzero axis directions have determined evaluations, so the
completed answer alphabet does not avoid the obstruction. The full argument,
including why the POVM weights are independent of the sampled point along a
fixed line, is in the new extended-line supplied-point subsection of
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.

The complete strategy-level contradiction is mathematical prose, not a Lean
theorem negating the target. In particular this is not a counterexample to the
paper's existentially constructed point family or to its printed error form.

## Saved Work and Costs

The all-ref history of `Combining/Apply.lean` was searched before implementation.
Commit `f6a340c8dc3c12566d9312215c578939efeb8b4a` already records the point-error
omission and changes both supplied-point helpers to fix an `IsPolyErr` function
before choosing their line-error functions. Its audit is
`audits/2026-09-06-issue118-point-error-dependency.md`. This is a different
signature from the assigned target, not a proof of it.

Saved commit `0f4ef05370350f4017439ebd839ef0561f13130f` retains a `sorry` at
the printed-error helper even under that repaired signature. It contains an
established-error construction under the repaired domain. Those declarations
were inspected for provenance, but their divergent branch was not copied and
their dependency closure was not independently revalidated here. No proof at
the assigned signature was found. The existing coefficient-collision API on
main is reused directly by the new scalar lemma.

The related B8 history remains **13 attempts / 26,509 working seconds**, with
the original September 5, 2026, 19:24 UTC anchor. The September 9, 08:51 UTC
event parked that mathematical episode; the present September 12 owner packet
is a bounded successor, not a reset or a restart of the exhausted estimate
search. At the verification checkpoint **05:10:58 UTC**, this session had
elapsed **1,052 seconds** since its dispatcher start at 04:53:26 UTC, making
the recorded prior charge plus this checkpoint **27,561 seconds**. Later
validation and publication time is additional and belongs to this session's
dispatcher record. Unknown token usage and other separately recorded episodes
are not treated as zero or silently included in this subtotal.

## Verification and Integrity

- `CombinedPointsWitness.exists_error_of_projective` proves finite-error
  existence for any supplied projective family, using `Finite.bddAbove_range`.
- `linear_quadratic_agreement_le` proves agreement at most `2 / q` when the
  quadratic coefficient of the candidate is zero and the comparison quadratic
  has nonzero leading coefficient. It reuses `directCoefficientCollision_avg_le`.
- The new module and `Apply.lean` pass focused Lean checking. `Apply.lean`
  retains exactly its five pre-existing proof holes.
- Both new lemmas have axiom closure exactly `propext`, `Classical.choice`,
  and `Quot.sound`. The target still has `sorryAx` in its closure.
- The paper-gap reference and style checks pass. The reference check retains
  the repository's existing missing-verdict-marker warnings.
- The paper-gap note compiles with `latexmk -pdf` to an eleven-page PDF with
  its bibliography; its pre-existing wide displays retain overfull-box warnings.
- The hook installation check passes. No new axiom, hole, bypass, witness field,
  or load-bearing source hypothesis is introduced.

The two new facts are internal counterexample-support lemmas, not paper-labelled
results, so no blueprint completion marker is added. The source and established
extended-line blueprint entries retain their existing status.

Statement-integrity audit: the paper assumes an admissible projective strategy
and its constructed points with polynomial error. Lean instead quantifies an
arbitrary scalar point error and all witnesses at that error. The paper concludes
two field-answer consistency relations with the printed error and axis degree
`d`; Lean concludes the existing directly indexed, completed-answer witness with
that error. Verdict: the assigned header is unchanged, but its unrestricted
point quantifier is an unsupported strengthening, refuted by the calculation
above. The existing carrier, answer, and printed-error discrepancies remain.

The next mathematical gate is a separately scoped domain realignment, retaining
the point-error dependency or constructing the points existentially. After that,
the printed error estimate and the source-game transport still require proofs.
Independent review follows published exact-head CI; this author session neither
reviews nor merges its work and does not launch descendants.
