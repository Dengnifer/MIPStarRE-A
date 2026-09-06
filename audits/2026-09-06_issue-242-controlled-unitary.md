# Packet #242: finite controlled-unitary algebra

Date: 2026-09-06. Session: `prover-242-20260906-01`.

## Source and scope

The source is the proof of `lem:qld-unitary` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1687-1750`.
Its first calculation, at lines 1687-1700, defines

\[
  V_{\mathrm A}=\sum_{g_X,g_Z}\widehat S_{g_X,g_Z}
    \otimes\bigl(\tau^X(\mathrm{Dec}(g_Z))\tau^Z(\mathrm{Dec}(g_X))\bigr)
\]

and proves that its product with its adjoint is the identity. The blueprint
records this construction at `def:v-swap-unitary` and the two adjoint products
at `lem:v-swap-conjugation`.

The new file `MIPStarRE/Quantum/ControlledUnitary.lean` proves the independent
finite-dimensional calculation. It neither constructs the measurement
\(\widehat S\) nor proves any Pauli identity. It does not claim the state-extraction
or observable-conjugation conclusions of `lem:qld-unitary`. No existing Lean
declaration, re-export, or blueprint entry is changed.

## Mathematical statements

Let \(I,C,T\) be finite index types. Let \((P_i)_{i\in I}\) be the effects of a
complete projective measurement on \(\mathbb C^C\), and let \((A_i)\) and
\((B_i)\) be arbitrary operators on \(\mathbb C^T\). Write
\(\mathcal C(A)=\sum_i P_i\otimes A_i\); this notation is used only in this
audit, not as a new Lean definition. The first theorem proves

\[
  \mathcal C(A)\mathcal C(B)=\sum_i P_i\otimes A_iB_i.
\]

Consequently, if every \(U_iU_i^\dagger=1\), then
\(\mathcal C(U)\mathcal C(U)^\dagger=1\). If instead every
\(U_i^\dagger U_i=1\), the reverse adjoint product is the identity. Finally,
membership of each \(U_i\) in Mathlib's unitary submonoid implies membership of
\(\mathcal C(U)\) in the unitary submonoid of operators on \(\mathbb C^{C\times T}\).
No commutation or self-adjointness of the \(U_i\) is required.

All four declarations are in `MIPStarRE.Quantum`:

- `sum_heteroKron_mul_sum_heteroKron`;
- `sum_heteroKron_mul_conjTranspose`;
- `conjTranspose_mul_sum_heteroKron`;
- `sum_heteroKron_mem_unitary`.

## Proof and existing APIs

The Lean hypotheses use `Quantum.Measurement` and the existing
`QPBT.Measurement.IsProjective` predicate, with `QPBT.heteroKron` for the tensor
product. Completeness and projectivity imply orthogonality; the proof uses
`DistanceCalculus.projective_effect_mul_effect_eq_zero`, rather than adding
orthogonality as another hypothesis or reproving it. Expanding the two finite
sums leaves only the terms with equal outcomes, where idempotence applies.

Mathlib's `Matrix.conjTranspose_kronecker` and `Matrix.conjTranspose_sum` compute
the adjoint. The projectors are self-adjoint. Unitarity of the components then
leaves \(\sum_iP_i\otimes1=1\otimes1=1\), using the existing
`DistanceCalculus.heteroKron_finset_sum_left` and `heteroKron_one_one`.

For finite square matrices, a one-sided inverse is also a two-sided inverse.
The reverse-product theorem uses Mathlib's `mul_eq_one_comm` for this fact,
first for each component and then for the controlled operator. Thus it does
not repeat the double-sum calculation.

The search covered the local `Quantum` and QPBT tensor/measurement APIs and
Mathlib's matrix, star-algebra, and finite-sum APIs. In particular,
`Matrix.kronecker_mem_unitary` concerns a tensor product of two unitary factors;
it does not directly apply to projectors controlled by different unitaries.
No applicable controlled-sum theorem was found. The new multiplication lemma
is the only double-sum calculation introduced.

## Statement-integrity audit

- **Paper assumptions:** the effects of \(\widehat S\) form a complete projective
  measurement; the two Pauli factors are self-adjoint involutions, so their
  ordered product is unitary.
- **Lean assumptions:** a complete matrix-valued `Measurement`, its
  `IsProjective` property, and the displayed adjoint identity for each actual
  component operator (or its membership in `unitary`). The multiplication
  theorem has no component-unitarity assumption.
- **Paper conclusion:** in the cited local calculation,
  \(V_{\mathrm A}V_{\mathrm A}^\dagger=1\), and hence unitarity; the construction
  for Bob is analogous.
- **Lean conclusion:** the same tensor-sum identity and both adjoint products,
  for arbitrary finite projective controls and arbitrary unitary components.
- **Verdict: faithful boundary hypotheses.** The finite index types and
  decidable equality needed for matrix identities encode the finite-matrix
  setting. No nonemptiness or equality of the two dimensions is assumed.
  These are explicitly auxiliary algebraic generalizations of the local
  calculation, not a strengthened statement of the full paper lemma.

There is no conclusion-shaped assumption on the controlled sum, no altered
definition of unitarity, no fallback branch, no existential default witness,
and no external statement assumption. The proofs use the existing measurement
API and Mathlib, and introduce no proof holes or unfaithful dependencies.

## Validation

The pinned toolchain is Lean v4.32.0 with Mathlib v4.32.0.

- `lake env lean MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean`: exit 0.
- `lake env lean MIPStarRE/Quantum/ControlledUnitary.lean`: exit 0, no diagnostics.
- `rg -n 'sorry|axiom' MIPStarRE/Quantum/ControlledUnitary.lean`: no matches.
- The extended forbidden-token scan and the 100-character line check: no matches.
- Private `.olean` compilation of the new module: exit 0.
- A separate importing Lean file checks both adjoint products and
  `Matrix.unitaryGroup` interoperability with control dimension 3 and target
  dimension 5, as well as an empty-outcome, empty-control instance: exit 0.
- `#print axioms` for each of the four new theorems reports exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- Git hooks were installed and `scripts/install_git_hooks.sh --check` succeeded.

The private artifacts and logs are under
`~/.cache/mipstarre-dev/prover-242-controlled-unitary/`. The import check uses
the privately compiled new module and symlinks to the worktree's existing
dependency artifacts; no shared package or hot-main artifact is written.
Full `lake build` is deliberately not run: this packet requests targeted
private validation, and no existing import or re-export is changed. CI,
independent review, publication, and merge are not run in this session.

## Remaining dependencies and handoff

There are no open declarations in the new file. For the later specialization,
`GlobalPairWitness.projective` already supplies projectivity of `w.Smeas side`,
and its `Measurement` supplies completeness. The remaining component-level
input is the proved adjoint/unitarity algebra for
`tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1)`;
packet #240 owns that work. The source-facing theorems
`swapUnitary_mul_conjTranspose` and `conjTranspose_mul_swapUnitary` remain
unchanged and open in `Extraction/Observables.lean` until an authorized
integration uses those results with this helper. The further conjugation and
state-extraction arguments are not proved here.

An independent reviewer should first check the orthogonality reduction, the
one-sided inverse conversion for finite matrices, and the distinction between
this auxiliary calculation and the uncompleted extraction theorem.
