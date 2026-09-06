# Block specialization: statement-integrity audit

Issue: #283. Source:
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1344-1363`,
between `eq:qld-g-2` and `eq:qld-g-prime-xpt-bound`.
The surrounding blueprint entry is `lem:qld-4-7` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`.

The only Lean addition is `MIPStarRE/QPBT/Combining/BlockSpecialization.lean`.
The global polynomial-pair theorem, its hypotheses, and the blueprint claims
are unchanged. This file proves an auxiliary used in its specialization
argument; it does not assert completion of `lem:qld-4-7`.

## Mathematical statement

Let K be a finite field of cardinality q and let p(z,x) have total degree at
most D, where z ranges over K^m and x ranges over K^k. Assume p does not belong
to the polynomial ring in z alone. There is a nonzero exponent vector mu and
a nonzero coefficient polynomial c_mu(z) such that

- c_mu has total degree at most D;
- Pr_z[c_mu(z) = 0] is at most D/q;
- for every z with c_mu(z) nonzero, simultaneously for every b in K,
  Pr_x[p(z,x) = b] is at most D/q.

For any nonnegative real weights w(z,b) with sum_b w(z,b) = M at every z,
the resulting conclusion is

    E_z sum_b Pr_x[p(z,x) = b] w(z,b) <= (2D/q) M.

The paper takes weights given by expectations of complete measurement
operators and uses D = (2m+2)d. Its separate preceding term M/q then gives
(2(2m+2)d+1)M/q. The scalar auxiliary establishes the 2D/q term itself.

## Proof and existing API

The existing `combinedCoefAlgHom` reads p as a polynomial in x with
polynomial coefficients in z. If every coefficient at a nonzero exponent
were zero, this rereading would be constant in x. Applying its existing
inverse `combinedCoefInv` would express p as a polynomial in z alone,
contradicting the dependence hypothesis. This constructs c_mu.

Splitting each monomial exponent into its two coordinate blocks shows that
coefficient extraction and specialization do not increase total degree.
The proofs use `combinedCoef_eq_sum`, `eval_combinedCoef`, and
`exists_mem_support_of_combinedCoef_ne_zero` with Mathlib's support and
total-degree inequalities.

Schwartz--Zippel applies first to c_mu and zero. For c_mu(z) nonzero,
the same positive-degree coefficient distinguishes p(z,.) from every
constant polynomial b, so Schwartz--Zippel applies again, uniformly in b.
The local `schwartzZippel_totalDegree` theorem reduces these applications
to Mathlib's `MvPolynomial.schwartz_zippel_totalDegree`.

Each answer probability is at most 1_bad(z) + D/q. Nonnegativity permits
multiplication by w(z,b), and the fixed mass identity gives
M(Pr_z[bad] + D/q) after summation and averaging. This proves 2DM/q.
The same exceptional set is used for all answers; no sum of exceptional
probabilities over the answer alphabet occurs.

## Assumptions and boundary cases

Paper assumptions: a polynomial depending nontrivially on the averaged
block, a total-degree bound, uniform sampling of the two field-coordinate
blocks, and nonnegative answer weights of constant total mass.

Lean assumptions: `Field K`, `Fintype K`, `DecidableEq K`, natural block
sizes m and k and degree bound D, `p.totalDegree <= D`, and
`forall r, p != MvPolynomial.rename (combinedPointVar m k) r`.
For the weighted theorem, `w` is any function of z and b with pointwise
nonnegativity and sum M at each z. These are actual polynomial and scalar
hypotheses, with no supplied collision estimate or construction obligation.
The existing API places z first and x second; this only fixes coordinate
order in the notation p(z,x).

Field cardinality positivity follows from the field instances. No positivity
assumption on m, k, D, or M is added. Parameter spaces remain nonempty when
m is zero. Dependence itself excludes k = 0 and, with the degree bound,
D = 0. Nonnegativity of M follows from the weights, including when M = 0.
The weights need not be independent of z.

No hypothesis D < q or bound on individual degrees is used. In particular,
a nonconstant polynomial can induce a constant function when D >= q, as
with x^q - x. The proof requires polynomial nonconstancy only. The numerical
Schwartz--Zippel bound remains valid in this case; it does not infer function
nonconstancy from a nonzero coefficient. Thus the paper's description of
good parameters as giving nonconstant functions is not needed for the
claimed numerical estimate at large degrees.

Paper conclusion: the second term in `eq:qld-g-2` has the indicated
2D/q times mass bound. Lean conclusion: precisely the scalar inequality
above, together with the coefficient and uniform exceptional-set statement.
Verdict: faithful boundary hypotheses for this auxiliary. No extra
assumptions, weakened conclusion, or change to the final source theorem.

## Validation

- `lake env lean MIPStarRE/QPBT/Combining/BlockSpecialization.lean` passed
  without errors or warnings.
- `rg -n "sorry|axiom"` on the file returned no matches. The extended scan
  for forbidden proof-integrity tokens and debugging commands also returned
  no matches. All lines are at most 100 characters.
- `Lean.collectAxioms` was checked for all five new public theorems:
  the two total-degree inequalities, the nonzero-coefficient existence
  theorem, the exceptional-coefficient theorem, and the weighted theorem.
  Each closure contains only `propext`, `Classical.choice`, and `Quot.sound`.
  The executable assertion is in runtime storage at
  `~/.cache/mipstarre-dev/prover-283-20260906-01/BlockSpecializationAxioms.lean`.
- Anti-patterns A1--A6 were checked: no assumed probability estimate,
  default coefficient, exceptional-set input, outcome-cardinality loss,
  or external statement assumption is present.
- Hooks were installed and their installation check passed. Full-project
  validation is assigned to exact-head local CI after publication; another
  build held the machine-wide lock during this file-level audit.

There are no remaining proof holes or internal proof obligations in this
auxiliary. Integration into the global polynomial-pair argument and
independent review belong to subsequent work.
