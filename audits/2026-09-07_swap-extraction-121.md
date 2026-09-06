# Exact Swap Identities for Extraction

## Scope and Dependencies

This change proves the four remaining swap identities in
`MIPStarRE/QPBT/Extraction/Observables.lean` for issue #121. The first four
observable targets of that issue were already proved by issue #240 / PR #248
and are retained without modification. All eight named targets now have
proofs, but their required publication, CI, review, and merge gates remain
separate obligations.

The branch `issue-121-swap-extraction` begins at the immutable validated
issue #120 / PR #293 head `4a25272ea7d7e5b5101940e6d9359f725d3d0e38`.
That parent contains PR #250 at `87f034b` and PR #248 at `5838982`.
The explicit additional prerequisite is issue #242 / PR #251 at
`9b5307e0a6facc6058dab1ff2946d7f50275f5eb`, which supplies
`Quantum.ControlledUnitary`. Merge `d6ba8e9b064eacd663032b04a5ad0863a4f33a50`
adds that prerequisite and passed the canonical merge-loss guard. No source
was taken from a moving worktree, and neither prerequisite worktree was edited.

## Source Calculation

The source is the proof of `lem:qld-unitary` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1687-1713`
and its measurement calculation at lines 1805-1822. The corresponding
blueprint node is `lem:v-swap-conjugation`, with equations
`eq:v-swap-obs-conjugation` and `eq:qld-unitary-6`.

Let (S_g), indexed by (g=(g_X,g_Z)), be the complete projective
measurement on one player's expanded local space. Write

\[
U_g=\tau^X(\mathrm{Dec}(g_Z))\tau^Z(\mathrm{Dec}(g_X)),
\qquad V=\sum_g S_g\otimes U_g.
\]

Orthogonality of the (S_g) reduces multiplication of two controlled sums
to multiplication at each common outcome. This is the existing theorem
`sum_heteroKron_mul_sum_heteroKron`, not a new unproved assumption. Each
Pauli observable is Hermitian and self-inverse, so (U_gU_g^*=I).
The existing `sum_heteroKron_mul_conjTranspose` proves (VV^*=I).
For square finite matrices, Mathlib's `mul_eq_one_comm` gives (V^*V=I)
from that right inverse identity.

For either (W=X) or (W=Z), put (d_W=\mathrm{Dec}(g_W)). The
twisted commutation relation gives

\[
U_g\tau^W(u)=(-1)^{\operatorname{tr}(d_W\cdot u)}\tau^W(u)U_g.
\]

In the (X) case, reversing the (XZ) relation uses the square of the
same binary phase, not a discarded sign. Combining this formula with the
product form of the pulled-apart observable yields two identical phases.
Their product is one, giving the required conjugation identity with
(V\widetilde W^j(u)V^*), in that order.

For measurement effects, Fourier inversion expresses a Pauli projector as
a sum of Pauli observables. The preceding phase then translates its label:

\[
U_g\tau_h^WU_g^*=\tau_{h+d_W}^W.
\]

Translating the finite dot-product fiber sends its scalar outcome (a) to
(a+d_W\cdot u). The pulled-apart effect has initial outcome
(d_W\cdot u-a), so the translated outcome is (a), since the field has
characteristic two. The local `CharP` instance used for this cancellation is
derived from the existing algebra over `ZMod 2`; it is not added to a public
theorem signature. Finally, `lowDegreeEnc_eq_dotProduct` identifies the
dot-product fiber at an indicator vector with the encoded-value fiber.
This argument never asserts that an arbitrary polynomial equals the encoding
of its decoder. In particular, it does not use the false unrestricted
interpolation identity documented in `qpbt_decoding-identity.tex`.

## Statement Integrity Audit

- Paper assumptions: the complete projective measurement (S_g), the
  characteristic-two generalized Pauli operators, the fixed field basis,
  and the stated definitions of the pulled-apart effects and swap map.
- Lean assumptions: unchanged `P : AdmissibleParams`,
  `S : ProjectiveSetting P epsilon`, `w : GlobalPairWitness S delta`,
  and the existing player, Pauli-basis, vector, basis-index, and scalar
  arguments of each theorem. Projectivity and completeness are obtained
  from `w.projective` and `(w.Smeas side).sum_eq_one`.
- Paper conclusions: both inverse equations for the swap map; exact
  conjugation of each pulled-apart observable to the corresponding Pauli
  observable; and exact conjugation of each pulled-apart point effect to
  the encoded-value projector fiber, for both players.
- Lean conclusions: unchanged `swapUnitary_mul_conjTranspose`,
  `conjTranspose_mul_swapUnitary`, `swapUnitary_conj_tildeObs`, and
  `swapUnitary_conj_tildeM`. The crossed decoder arguments, binary phases,
  heterogeneous register order, and (VNV^*) orientation are unchanged.
- Verdict: exact statements with the existing faithful finite-field and
  finite-dimensional boundary encoding. No bridge, unitary assumption,
  error relaxation, or support restriction is introduced.

The blueprint change adds proof-level `\leanok` to
`lem:v-swap-conjugation`; its statement and declaration links are unchanged.

## Validation

- Prepared the separate worktree with the primary
  `local/bin/worktree-setup.sh --no-build`; setup telemetry was directed to
  `/tmp/qpbt-pr292-buffered-setup-telemetry` for the single telemetry owner.
- Compiled `ControlledUnitary.lean`, `Extraction/Defs.lean`, and the edited
  `Extraction/Observables.lean` into branch-local artifacts. The edited file
  type-checks without warnings and contains no proof holes or debug commands.
- Fresh-artifact `#print axioms` checks for all eight issue #121 targets and
  the two inherited `tildeM` theorems report only
  `[propext, Classical.choice, Quot.sound]`. The check file is
  `/tmp/qpbt-121-swap-public-axioms.lean`, outside the repository.
- `Extraction/Consistency.lean`, `Extraction/Unitary.lean`, and
  `MIPStarRE/QPBT.lean` type-check. The unchanged consistency and final
  extraction files retain their existing unfinished proofs.
- `leanblueprint web` succeeds with the existing missing-bibliography
  warnings. Blueprint synchronization initially found 231 stale entries in
  the prepared worktree's ignored `blueprint/lean_decls`. Regenerating that
  derived list with `blueprint_lean_sync.py --update-lean-decls --ci` passes;
  `lake exe checkdecls blueprint/lean_decls` then resolves all 1,398 entries.
  No tracked declaration link was changed. Git hook installation and
  `git diff --check` pass.
- No full build, canonical CI, independent review, or publication is claimed
  by this audit. Those gates must use the final immutable head and retain
  every explicit stack prerequisite.
