<!-- scout: scout-123-extraction-isometry-20260906-01 2026-09-06 -->
## Mathlib scouting report — 2026-09-06

**Scope:** construction of `MIPStarRE.QPBT.exists_extractionWitness_ofGlobalPairWitness` only. Scalar error absorption and controlled-unitary algebra are excluded.

**Main finding:** auxiliary-state normalization and heterogeneous tensor-isometry norm preservation are already proved. Reuse them after an explicit register permutation. The new mathematical work is the EPR projection identity and its application to the swapped state; the missing interface work is coordinate transport and state-dependent measurement comparison.

### Mathematical source

- *MIP\*=RE*, `lem:qld-unitary`, `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1669`: the concrete local swap unitaries produce a normalized auxiliary state tensored with EPR, and conjugated total-Pauli measurements approximate the canonical projectors **on that ideal state**.
- Auxiliary-state construction: `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1715`, especially the partial EPR inner product at line 1769 and normalization at line 1773.
- Measurement comparison: `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1827`.
- Existing correction note: `docs/paper-gaps/qpbt_extraction-transfer.tex:34`. The source’s reverse-triangle and squared-triangle estimates must not be copied literally.
- Lean target: `MIPStarRE/QPBT/Extraction/Unitary.lean:94`. Its existing global-pair premise makes it a conditional construction helper, not the closed source theorem. This plan adds no premises.

### Relevant Mathlib definitions

- `LinearIsometryEquiv.piLpCongrLeft` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:865` — **exact mathematical match** for coordinate permutation of Euclidean spaces. Identify the project’s reindexing operation with this map to inherit linearity, inverse cancellation, and distance preservation.
- `InnerProductSpace.rankOne` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean:303` — **exact match** for the EPR rank-one operator.
- `NormedSpace.normalize` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Normalize.lean:25` — **near-match** for auxiliary normalization: normalization of zero is zero, so this alone cannot discharge the unit-norm field.

### Relevant Mathlib lemmas and theorems

- `InnerProductSpace.symm_toEuclideanLin_rankOne` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean:1322` — identifies a rank-one Hilbert-space operator with `Matrix.vecMulVec`. No new rank-one formalism is needed.
- `Matrix.vecMulVec_mulVec` — `.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:895` — evaluates the EPR projection as an inner product times the EPR vector.
- `Matrix.submatrix_mul_equiv` — `.lake/packages/mathlib/Mathlib/Data/Matrix/Mul.lean:1179` — supplies multiplication transport for the project’s reindexed operators.
- `Matrix.conjTranspose_reindex` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:444` — transports adjoints.
- `Matrix.conjTranspose_kronecker` — `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:408` — combines with the existing project tensor-multiplication API to preserve two-sided unitarity.
- `norm_sub_sq` — `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:431` — gives the short, valid replacement for the problematic source estimates.
- `NormedSpace.norm_normalize_eq_one_iff` — `.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Normalize.lean:42` — normalization requires a nonzero vector; do not silently omit this condition.

The abstract Hilbert tensor-product API also exists, but introducing a conversion from the project’s coordinate tensors would add unnecessary work here.

### Relevant MIPStarRE declarations

**Proved support, with bodies inspected**

- `MIPStarRE.QPBT.reindexState_norm_eq` — `MIPStarRE/QPBT/State.lean:86` — preserves norm under every finite coordinate equivalence.
- `MIPStarRE.QPBT.vecTensor_norm_eq` — `MIPStarRE/QPBT/State.lean:99` — tensor norm is the product of factor norms.
- `MIPStarRE.QPBT.eprState_norm` — `MIPStarRE/QPBT/Algebra/Pauli.lean:435` — the finite-label EPR vector is normalized.
- `MIPStarRE.QPBT.MagicSquareRigidity.norm_toEuclideanLin_of_conjTranspose_mul_eq_one` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean:96` — a **rectangular** matrix satisfying \(A^\dagger A=I\) preserves Euclidean norm.
- `MIPStarRE.QPBT.MagicSquareRigidity.isometryTensor_eq_toEuclideanLin` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean:321` — identifies the heterogeneous tensor-isometry action with its Kronecker matrix.
- `MIPStarRE.QPBT.MagicSquareRigidity.norm_isometryTensor` — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/GroundSlice.lean:348` — preserves norm without identifying Alice’s and Bob’s carriers.
- **`MIPStarRE.QPBT.MagicSquareRigidity.exists_unit_residual`** — `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/JointState.lean:650` — replaces an arbitrary auxiliary vector by a unit vector at twice the unsquared distance. It already handles the zero-vector branch.
- `MIPStarRE.QPBT.SandwichProduct.avg_diagonal_postprocess_stateQForm_le` — `MIPStarRE/QPBT/Games/Sandwich/Support.lean:135` — **adaptable match** for source equation `eq:qld-unitary-8`: evaluated diagonal overlap is at most full diagonal overlap plus the collision bound.
- `MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_trans_le` — `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:311` — supplies the three-link consistency argument, once the placed families are packaged as measurements.
- `MIPStarRE.QPBT.DistanceCalculus.point_distance_eq_two_defect_of_projective` — `MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean:475` — supplies the final projective-family distance expansion.

**Existing coordinate definitions to retain**

- `MIPStarRE.QPBT.sixRegExtractionEquiv` — `MIPStarRE/QPBT/Extraction/Defs.lean:59`.
- `MIPStarRE.QPBT.extractionIdealShuffle` — `MIPStarRE/QPBT/Extraction/Defs.lean:72`.
- `MIPStarRE.QPBT.ProjectiveSetting.applyBoth` — `MIPStarRE/QPBT/Extraction/Defs.lean:149`.
- `MIPStarRE.QPBT.ProjectiveSetting.idealExpState` — `MIPStarRE/QPBT/Extraction/Defs.lean:161`.

**Not established facts**

- `MIPStarRE.QPBT.tildeObs_selfConsistent` — `MIPStarRE/QPBT/Extraction/Consistency.lean:212` — still `sorry`.
- `MIPStarRE.QPBT.tildeM_consistent_pointMeas` — `MIPStarRE/QPBT/Extraction/Consistency.lean:158` — still `sorry`.
- `MIPStarRE.QPBT.tildeM_consistent_pointMeas'` — `MIPStarRE/QPBT/Extraction/Consistency.lean:185` — still `sorry`.
- The four swap-unitary/conjugation declarations at `MIPStarRE/QPBT/Extraction/Observables.lean:214`, `MIPStarRE/QPBT/Extraction/Observables.lean:228`, `MIPStarRE/QPBT/Extraction/Observables.lean:242`, and `MIPStarRE/QPBT/Extraction/Observables.lean:260` remain unfinished. Their proofs belong to the separate algebra work, not to an assumption inserted into this constructor.

### Suggested approach

#### 1. Fix the carriers and transport direction

Write
\[
V=\mathrm{PauliRegister}(P),\qquad
A_0=\iota_A\times V,\qquad B_0=\iota_B\times V,\qquad
R=A_0\times B_0.
\]

Thus the auxiliary carrier is \(R\), the extraction-block carrier is
\((A_0\times V)\times(B_0\times V)\), and the ideal-factor carrier is
\(R\times(V\times V)\).

Let \(e_B\) be the existing six-register-to-block equivalence and \(e_I\) the existing ideal-factor-to-six-register shuffle.

**Important:** state and operator reindexing have opposite directions. For \(e:I\simeq J\), the required action identity is
\[
\operatorname{apply}(\operatorname{reindexOp}(e,T),\psi)
=
\operatorname{reindexState}\!\left(e^{-1},
  \operatorname{apply}(T,\operatorname{reindexState}(e,\psi))\right).
\]
Prove this once by coordinate extensionality and equivalence reindexing of the matrix sum. Derive quadratic-form and family-distance transport from it; do not separately expand every six-register sum.

There is already a proof pattern for quadratic forms at `MIPStarRE/QPBT/Games/DistanceTheorems.lean:249`, but that theorem is **private**, not an exported API.

#### 2. Normalize the swapped state using the existing heterogeneous API

Set
\[
\vartheta=S.\mathrm{applyBoth}(V_A,V_B,S.\psiHat).
\]

The initial expanded-state norm follows immediately from the three proved tensor/reindex/EPR norm identities and the strategy’s unit-state field.

Once the separate writer proves \(V_s^\dagger V_s=I\), regard each square block map as a linear isometry. In block coordinates, the transformed state is exactly the existing heterogeneous tensor-isometry action. Transport back using \(e_B^{-1}\), obtaining \(\|\vartheta\|=1\).

No new isometry theorem is needed. In particular, this constructor does **not** require the later soundness isometries adjoining EPR pairs or their range-projection argument.

#### 3. Select the auxiliary vector by the source’s partial inner product

Let
\[
E=\mathrm{eprState}(V),\qquad
\xi=\operatorname{reindexState}(e_I^{-1},\vartheta).
\]
Define the unnormalized auxiliary vector by
\[
a_0(r)=\sum_{s,t\in V}\overline{E(s,t)}\,\xi(r,(s,t))
      =\frac1{\sqrt{|V|}}\sum_{t\in V}\xi(r,(t,t)).
\]

This is the source construction, not an arbitrary existential witness.

Let \(\Pi_E=|E\rangle\langle E|\), represented by its ordinary rank-one matrix, and set
\[
\Pi=
\operatorname{reindexOp}\bigl(e_I^{-1},I_R\otimes\Pi_E\bigr).
\]
The essential coordinate lemma is
\[
S.\mathrm{idealExpState}(a_0)=\Pi\vartheta.
\]

Prove it using the finite partial-inner-product sum and the rank-one matrix action. **Do not use the LDT normalized-trace density convention:** this operator is the ordinary rank-one EPR projection.

#### 4. Obtain the raw projection estimate without the source’s invalid inequalities

Define on \(V\times V\)
\[
H_W=\frac1{|V|}\sum_{u\in V}\tau^W(u)\otimes\tau^W(u),
\]
and lift it to six registers using the same ideal shuffle.

The required exact algebraic facts are:

- \(H_W\) is a contraction;
- \(H_XH_Z=\Pi_E\).

For the product identity, use the source’s finite Fourier cancellation calculation. Available proved inputs include:

- `MIPStarRE.QPBT.tauObservable_sq` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:403`;
- `MIPStarRE.QPBT.ffChar_dotProduct_submodule_expect_eq_zero` — `MIPStarRE/QPBT/Algebra/PauliTheorems.lean:452`.

The pulled-observable consistency theorem must first be proved from the existing global-pair premises. Its exact conjugation then gives
\[
\operatorname{Re}\langle\vartheta,H_W\vartheta\rangle\ge1-D/2
\]
at its construction error \(D\). Its statement is pointwise in the basis index: choose one basis element and reindex the uniform register variable by multiplication by that nonzero element. An additional average over basis indices is unnecessary.

Now the following short argument is valid:
\[
\|\vartheta-H_W\vartheta\|^2\le D,
\]
because \(\|\vartheta\|=1\), \(\|H_W\vartheta\|\le1\), and the displayed correlation bound. Consequently,
\[
\begin{aligned}
\|\vartheta-\Pi\vartheta\|
&=\|\vartheta-H_XH_Z\vartheta\|\\
&\le\|\vartheta-H_X\vartheta\|
  +\|H_X(\vartheta-H_Z\vartheta)\|\\
&\le2\sqrt D.
\end{aligned}
\]

This supplies a stronger raw estimate than needed and avoids both problematic source inequalities. It is a projection estimate, not a scalar error-absorption argument.

#### 5. Reuse the proved normalization theorem through one explicit permutation

The existing normalization theorem uses local order
\[
(V\times A_0)\times(V\times B_0).
\]
Use
\[
\chi=e_B\;\text{followed by swapping the two factors within each block}.
\]
Explicitly,
\[
((a,(a',a'')),(b,(b',b'')))
\longmapsto ((a'',(a,a')),(b'',(b,b'))).
\]

Its key transport identity is
\[
\operatorname{reindexState}(\chi,S.\mathrm{idealExpState}(r))
=
\operatorname{reindexState}(\mathrm{prodShuffle},E\otimes r).
\]

Supply the normalization theorem with the following **explicit normalized reference vector**:
\[
a_{\mathrm{ref}}
=\operatorname{reindexState}(\mathrm{prodShuffle},
                   S.\psi\otimes E)\in\mathbb C^R.
\]
Its norm is one by the existing norm lemmas.

Apply `MIPStarRE.QPBT.MagicSquareRigidity.exists_unit_residual` to the transported \(\vartheta\), \(a_0\), and \(a_{\mathrm{ref}}\). Transport its conclusion back. For a raw residual bound \(r_0\), this gives a unit auxiliary state with distance at most \(2r_0\); the bound above therefore yields
\[
\|\vartheta-S.\mathrm{idealExpState}(\mathrm{aux})\|
 \le4\sqrt D,\qquad
\|\vartheta-S.\mathrm{idealExpState}(\mathrm{aux})\|^2\le16D.
\]

The merged proof selects \(a_0/\|a_0\|\) when \(a_0\ne0\). When \(a_0=0\), it uses the supplied reference vector and proves that the raw error is already large enough. Thus there is no unjustified division, arbitrary carrier inhabitant, or extra nonvanishing hypothesis.

#### 6. Transport the measurement estimate to this same ideal state

The necessary placement equalities are:

- original-player placement equals block placement after adjoining identities;
- extracted-register placement equals block placement of \(I\otimes T\);
- simultaneous conjugation of a one-side operator equals conjugation on that side alone.

These follow from coordinate definitions and tensor multiplication. They connect the conjugation writer’s local identities to the **actual fields** at `MIPStarRE/QPBT/Extraction/Unitary.lean:63`.

For the remaining comparison:

1. Prove both orientations of evaluated-total-Pauli versus opposite-side pulled-measurement consistency. Do not treat unfinished factor-interchanged winning-implication companions as proved.
2. Conjugate the comparison and transport it to \(\vartheta\).
3. Transfer the **whole diagonal-overlap operator**, not individual outcomes, from \(\vartheta\) to \(\Delta=S.\mathrm{idealExpState}(\mathrm{aux})\). For a positive contraction \(K\) and unit vectors,
   \[
   |\langle\Delta,K\Delta\rangle-\langle\vartheta,K\vartheta\rangle|
   \le2\|\Delta-\vartheta\|.
   \]
   Bounding outcomes separately would introduce an unacceptable answer-cardinality factor.
4. Apply the existing averaged-diagonal collision theorem in block coordinates.
5. Use the EPR transpose identity to move canonical projectors between extracted registers. The general identity involves \(T^{\mathsf T}\), **not \(T^\dagger\)**; establish that these characteristic-two Pauli projectors are real symmetric before removing the transpose.
6. Expand projective-family distance and populate both side-indexed conclusions.

For the collision input, existing proved encoding support is sufficient: `MIPStarRE.QPBT.decodeFq_lowDegreeEncoding` at `MIPStarRE/QPBT/Algebra/Decoding.lean:159` proves injectivity of encoding representatives; `MIPStarRE.QPBT.lowDegreeEncoding_mem_poly` at `MIPStarRE/QPBT/Algebra/Decoding.lean:75` supplies the degree bound; apply `MIPStarRE.LDT.Preliminaries.schwartzZippel_individualDegree` at `MIPStarRE/LDT/Preliminaries/Polynomials.lean:106`, converting its rational probability to the project’s real average.

Select all universal constants **before** introducing parameters and the strategy. Hand the raw state/measurement bounds to the scalar writer for the common constant required by the target; do not choose a parameter-dependent constant.

### Gaps to fill

The minimal independent obligations for this construction are:

- **Coordinate-action transport:** the reindexed matrix-action equality in Step 1, with norm/distance consequences inherited from the permutation isometry.
- **Extraction placement transport:** the three placement/conjugation identities in Step 6.
- **EPR partial contraction:** the explicit finite-sum construction and \(S.\mathrm{idealExpState}(a_0)=\Pi\vartheta\).
- **Pauli-average EPR identity:** \(H_XH_Z=\Pi_E\), with contraction bounds. Searched EPR/Bell projection names, average–tensor shapes, rank-one products, and partial-inner-product names; no usable exported QPBT theorem was found.
- **Source-derived projection estimate:** prove the currently unfinished observable consistency input, then perform Step 4. It must not become a field or premise of the extraction theorem.
- **Dimension-independent measurement transfer:** the whole-overlap state-change estimate, EPR transpose transport, and the two concrete evaluated-consistency orientations.

The auxiliary normalization estimate, heterogeneous isometry norm theorem, and weighted collision summation **are not missing** and should not be reproved. These obligations fit in extraction support modules imported by the existing constructor; none requires changing its statement.

### Searched

- Read root instructions and the committed-main scout prompts; followed paper → blueprint → Lean order.
- Consulted `docs/api_surface.md`, prior heterogeneous-space scouting, and matrix/orthonormalization scouting notes.
- Searched local Mathlib by normalization statements, rectangular-isometry equations, permutation isometries, rank-one action, tensor-product norms, and projection terminology.
- Searched project state, extraction, Pauli algebra, distance calculus, sandwich support, Magic Square normalization/isometry support, and LDT polynomial APIs.
- Inspected promising proof bodies and scanned relevant files for `sorry|axiom`. Findings are **source-verified, not compiler-validated**.
- GitHub issue retrieval through the prescribed helper failed because network sockets are prohibited; existing issue comments could not be checked.
- Final inspected `main`: `a9122d7`; the intervening commit changed telemetry, not the inspected mathematical files. No files changed, no builds, no subagents, and no issue mutation.