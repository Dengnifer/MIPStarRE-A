# Supported-reference mass comparison

Issue #261. Base commit: `32a32edee16d3932525e4b1da9f84009e1fbb13b`.

## Mathematical statement

Let \(A=(A_a)_{a\in\Omega}\) and \(B=(B_a)_{a\in\Omega}\) be complete
finite POVMs on possibly different finite-dimensional Hilbert spaces. Let
\(S\subseteq\Omega\), and assume \(B_a=0\) for every \(a\notin S\).
For the same vector \(\psi\) in their tensor product,
\[
  \sum_{a\notin S}\langle\psi,(A_a\otimes I)\psi\rangle
  \leq \sum_{a\ne b}\langle\psi,(A_a\otimes B_b)\psi\rangle.
\]
The expressions are real because the operators are positive semidefinite.
For each \(a\notin S\), completeness of \(B\) expands the marginal into
\(\sum_b\langle\psi,(A_a\otimes B_b)\psi\rangle\); its diagonal term
vanishes by the support assumption. All remaining joint terms are nonnegative,
so enlarging the outer sum proves the inequality.

No projectivity, symmetry, equal local dimensions, or state normalization is
required. Specializing to a unit vector gives the requested probability bound.
Averaging against the nonnegative weights of a finite distribution preserves
the inequality, with no normalization assumption on those weights.

## Lean declarations and API search

`MIPStarRE/QPBT/Games/SupportMass.lean` proves
`MIPStarRE.QPBT.mass_outside_support_le_point_defect` and
`MIPStarRE.QPBT.avg_mass_outside_support_le_consistency_defect`.
The public aggregate `MIPStarRE/QPBT.lean` imports the new module.

The search covered Quantum measurements, QPBT distance and sandwich support,
LDT basic and consistency APIs, and Mathlib finite-sum order lemmas. No existing
supported-reference bound was found. The proofs reuse `stateQForm_nonneg`,
`kronecker_nonneg`, the tensor and quadratic-form finite-sum identities,
`Finset.sum_le_sum_of_subset_of_nonneg`, and
`SandwichProduct.consistencyDefect_placed_eq_avg_point` rather than duplicating
these facts.

## Source relationship and intended use

The source motivation is the consistency calculation in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1498`,
in the proof of `lem:qld-construct-the-paulis`. The repaired non-encoding
calculation is blueprint `eq:qld-nonencoding-mass`, with its separate open
estimate `lem:qld-nonencoding-mass-bound`. Neither new declaration is advertised
as that source theorem or as the completed repair.

For the intended application, let the outcomes be polynomial representatives,
let \(S\) consist of encodings, and let \(A\) be the global marginal and \(B\)
an encoding-supported reference. After expressing them on opposite factors of
the actual bipartition, the first theorem bounds the non-encoding mass by the
full polynomial defect. Its conclusion is exactly the left side of the existing
`SandwichProduct.point_codeword_defect_le_avg_evaluated_add`; transitivity then
bounds the mass by the evaluated defect plus the collision error. This generic
composition was type-checked in runtime scratch, without introducing any
polynomial-specific construction or hypothesis on a paper theorem.

The reference construction, polynomial collision specialization, register
placements, winning implications, and quantitative assembly remain outside this
change. In particular, neither `nonencodingMarginalMass_le` nor
`exists_globalPairWitness` is proved or altered. No blueprint completion tag is
added.

## Statement integrity and evidence

- Mathematical assumptions: two finite complete POVMs, reference support, one
  common bipartite vector; nonnegative averaging weights in the averaged form.
- Lean assumptions: precisely these, with finite-type and decidable-equality
  instances. `Measurement` supplies positivity and completeness; `Distribution`
  supplies nonnegative weights.
- Mathematical and Lean conclusions: unsupported marginal mass is at most the
  off-diagonal defect, pointwise and averaged using explicit tensor placements.
- Verdict: exact on normalized states, also proved for arbitrary vectors. No
  existing paper-labelled statement or proof is changed.
- `lake env lean` succeeds on the new module and the public QPBT aggregate.
- A runtime example composes the pointwise theorem with the existing collision
  comparison on a normalized state and also type-checks.
- The edited Lean files contain no `sorry` or `axiom` matches. Source-based
  `#print axioms` checks for both new theorems report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The full build was not started while the machine-wide lock was held by
  `ci.sh` for PR #254. File-level checks require no lock.
