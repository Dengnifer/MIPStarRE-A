---
title: "Absorption of the extraction error"
date: 2026-09-06
purpose: >
  Records the source comparison, uniform constant absorption, and validation
  of the scalar extraction-error estimate.
issue: "#241"
pr: "#249"
---

# Packet #241: absorption of the extraction error

## Scope and source

The only Lean change is the proof and docstring of
`MIPStarRE.QPBT.deltaExtract_le_deltaQld` in
`MIPStarRE/QPBT/Extraction/Unitary.lean`. Its public statement is unchanged.
The preceding declarations, including
`exists_extractionWitness_ofGlobalPairWitness`, are unchanged. No blueprint
file is modified in this packet.

The source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1855-1858,1868-1876`.
The first passage bounds the extraction error by
\(O(\delta_S^{1/4}+md/q)\); the second asserts that the resulting error belongs
to the robustness family
\(a(md)^a(\epsilon^b+q^{-b}+2^{-bmd})\).
The explicit scalar assertion is blueprint `lem:qld-extraction-error-form`.
The proof uses the merged definitions `deltaConstructPaulis`, `deltaExtract`,
and `deltaQld`, without changing any of them.

## Quantitative argument

Write \(D=md\), and set
\[
  \beta=b/8,\qquad A=4C^2a,\qquad
  H=aD^a,\qquad
  R=\epsilon^\beta+q^{-\beta}+2^{-\beta D}.
\]
Admissibility gives \(D\geq1\) and \(q\geq1\). Consequently \(H\geq1\),
\(D\leq H\), and \(A\geq a>1\). Also \(0<\beta<1\).
No inequality such as \(md\leq q\) is assumed or needed.

For nonnegative terms, the fourth root of a sum is at most the sum of their
fourth roots. Applying this inequality to the three robustness terms, and
using \(b/8\leq b/4\), gives
\[
  \delta_G^{1/4}\leq HR.
\]
Here the factor \(H^{1/4}\) is bounded by \(H\), because \(H\geq1\).
The other terms satisfy
\[
  (\sqrt\epsilon)^{1/4}=\epsilon^{1/8}\leq HR,
  \qquad (D/q)^{1/4}\leq HR,
  \qquad D/q\leq HR.
\]
The first comparison uses \(0\leq\epsilon\leq1\) and \(b<1\).
For the remaining comparisons, use \(D^{1/4}\leq D\leq H\),
\(q^{-1/4}\leq q^{-\beta}\), and \(q^{-1}\leq q^{-\beta}\).
Since \(C^{1/4}\leq C\), it follows that
\[
  \delta_P^{1/4}\leq3CHR,
  \qquad
  \delta_{\mathrm{ext}}
    \leq C(3C+1)HR
    \leq4C^2HR
    =AD^aR
    \leq AD^AR.
\]
These are precisely the required witnesses \(a'=A\), \(b'=\beta\).

The analytic inputs are Mathlib's `Real.rpow_add_le_add_rpow`,
`Real.mul_rpow`, `Real.div_rpow`, `Real.rpow_mul`, and real-power
monotonicity. `Real.rpow_le_rpow_of_exponent_ge'` includes the endpoint
\(\epsilon=0\), so the proof needs no positive-error restriction.
The three-term subadditivity calculation is shared by two local uses inside
the proof; no new public helper or automation is introduced.

## Statement-integrity audit

- **Paper assumptions:** admissible parameters, an error
  \(0\leq\epsilon\leq1\), and universal error constants. The blueprint makes
  the scalar constants explicit as \(C\geq1\), \(a>1\), \(0<b<1\).
- **Lean assumptions:** exactly these scalar inequalities and the existing
  `AdmissibleParams` domain. The proof derives the needed positivity of
  \(md\) and \(q\) from that domain. It takes no strategy, measurement,
  extraction witness, or additional estimate as an input.
- **Paper conclusion:** extraction preserves the stated robustness family
  after adjustment of its universal constants.
- **Lean conclusion:** there exist \(a'\geq1\) and \(0<b'<1\), depending
  only on \(C,a,b\), that bound the exact composed extraction error for all
  admissible parameters and all \(0\leq\epsilon\leq1\).
- **Verdict: exact** for `lem:qld-extraction-error-form`, an explicit scalar
  formulation of the cited paper comparison. The chosen \(a'\) is in fact
  greater than one, as in the source's final robustness statement.

A byte comparison against the starting revision verifies that the entire
public theorem signature and all preceding declarations are unchanged.
The proof introduces none of anti-patterns A1--A6: it derives the estimate
from existing definitions and Mathlib inequalities, uses explicit universal
constants, and assumes no unproved construction or conclusion-shaped input.

## Validation

- `lake env lean MIPStarRE/QPBT/Extraction/Unitary.lean` passes. The sole
  warning is the pre-existing use of `sorry` in
  `exists_extractionWitness_ofGlobalPairWitness` at line 94.
- `rg -n "sorry|axiom" MIPStarRE/QPBT/Extraction/Unitary.lean` reports only
  `105:  sorry`, in that unchanged theorem.
- A fresh `.olean` is compiled into the session's private directory. An
  isolated import of that artifact reports that
  `MIPStarRE.QPBT.deltaExtract_le_deltaQld` depends only on
  `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- `git diff --check` and a 100-character line-width check pass. Repository
  hooks are installed, and `scripts/install_git_hooks.sh --check` passes.
- No full `lake build` is run: this packet changes only one proof body and
  its documentation, and requests private artifacts and targeted checks.
  No shared cache, vendored dependency, import, or public signature changes.

Private validation artifacts and logs are under
`~/.cache/mipstarre-dev/sessions/prover-241-20260906-01-checks/`.

## Integration and remaining obligations

At blueprint `lem:qld-extraction-error-form`, retain the existing link
and add the completion tag during integration:

```tex
\lean{MIPStarRE.QPBT.deltaExtract_le_deltaQld}
\leanok
```

There is no remaining scalar obligation in this packet. The adjacent
`exists_extractionWitness_ofGlobalPairWitness` still contains its original
`sorry`. Its docstring assigns the EPR-projection and measurement-comparison
construction to issue #47 and records the conditional extraction discrepancy
in `docs/paper-gaps/qpbt_extraction-transfer.tex`; issue #123 tracks composition
with `exists_globalPairWitness`. Those constructions are not dependencies of
the scalar theorem proved here and have not been edited or discharged.
In particular, this packet does not justify marking `lem:qld-unitary` or the
full soundness theorem complete.
