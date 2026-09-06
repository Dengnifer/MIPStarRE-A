<!-- scout: scout-118-projectivization-20260906-01 2026-09-06 -->
## Mathlib scouting report — 2026-09-06

**No additional Naimark or value-preservation lemma is needed.** Issue #244/PR #254 already proves the required specialization. The next mathematical obligation is a quantitative passing bound for its constructed strategy. This supplements the prior issue118 consumer audit with the exact soundness application and the newly available #273 spectator identities.

### Mathematical source

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278`, proof of `lem:qld-4-7`: construct the extended-line strategy, projectivize while preserving consistency, and apply classical soundness.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413`, `lem:ld-soundness`: a projective strategy passing with positive error produces two polynomial POVMs and three consistency conclusions. The players’ Hilbert spaces need not coincide.
- Checkpoint `0f4ef05` establishes line error `C*m*g(ε,md/q)`. It does not establish the printed stronger error `poly(m²ε,md/q)`. The direct dimension-`2m+2` game avoids the documented divisibility defect.

### Relevant Mathlib definitions

- `CFC.sqrt` — `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:236` — operator square roots underlying the existing Naimark construction.
- `Matrix.kronecker` — `Mathlib/LinearAlgebra/Matrix/Kronecker.lean:274` — tensor products retaining distinct index types.

### Relevant Mathlib lemmas and theorems

- `CFC.sqrt_mul_sqrt_self` — `Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean:265` — reconstructs a positive operator from its square root; already consumed locally.
- `Matrix.submatrix_mulVec_equiv` — `Mathlib/Data/Matrix/Mul.lean:1184` — transports operator action through register permutations.
- `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` — `Mathlib/Algebra/Polynomial/Roots.lean:742` — adaptable to agreement bounds for distinct bounded coefficient lists; no new root theorem is required.

### Relevant MIPStarRE declarations

- **Merged:** `MIPStarRE.QPBT.dilatedMeasurement`, `MIPStarRE.QPBT.dilatedMeasurement_isProjective`, `MIPStarRE.QPBT.dilatedMeasurement_compression` — `MIPStarRE/QPBT/Games/StrategyClasses.lean:278,288,303` — complete projective dilation with exact compression at `none`.
- **Merged:** `MIPStarRE.QPBT.stateQForm_padState`, `MIPStarRE.QPBT.paddedStrategy`, `MIPStarRE.QPBT.paddedStrategy_value` — same file, `:214,360,387` — preserve individual correlations and game value with independent player registers.
- **Merged:** `MIPStarRE.QPBT.exists_direct_ld_soundness_of_k_eq_one` — `MIPStarRE/QPBT/Combining/DirectLowDegree/Soundness.lean:244` — exactly the required soundness theorem; accepts arbitrary heterogeneous projective strategies.
- **Proved, unmerged PR254:** `MIPStarRE.QPBT.ExtendedLineGame.projectiveStrategy`, `MIPStarRE.QPBT.ExtendedLineGame.projectiveStrategy_isProjective`, `MIPStarRE.QPBT.ExtendedLineGame.projectiveStrategy_value` — `MIPStarRE/QPBT/Combining/ExtendedLineGame.lean:437,447,457` — exact requested construction, with no passing premise.
- **Proved, unmerged PR254:** `MIPStarRE.QPBT.ExtendedLineGame.completedLinePointDefect_sums_le`, `MIPStarRE.QPBT.ExtendedLineGame.strategy_value_eq` — same file, `:320,412` — two oriented defect bounds and exact seven-branch rejection accounting.
- **Proved, unmerged #273/PR274:** `MIPStarRE.QPBT.ProjectiveSetting.psiHat_expectation_AA'_BA''`, `MIPStarRE.QPBT.ProjectiveSetting.psiHat_expectation_BB'_AB''` — `MIPStarRE/QPBT/Observables/ExpandedSpectator.lean:170,182` — both spectator-removal identities. Bob’s state is explicitly reordered; no strategy symmetry is assumed.
- **Proved checkpoint content:** `MIPStarRE.QPBT.exists_extendedLinesWitness_established`, `MIPStarRE.QPBT.exists_globalPair_error_bound` — `MIPStarRE/QPBT/Combining/Apply.lean:1636,1660` — actual two-player witness and scalar absorption.
- **Adaptable merged estimates:** `MIPStarRE.QPBT.consistencyDefect_trans_le` — `MIPStarRE/QPBT/Games/DistanceTheorems/Calculus.lean:311`; `MIPStarRE.QPBT.SandwichProduct.consistencyDefect_codewords_le_evaluated_add` — `MIPStarRE/QPBT/Games/Sandwich/Support.lean:324`. Their application still requires the actual line-resampling law and coefficient-evaluation collision bound.

Ancestry checked against main `928328f`: PR254 head `7691c2c`, #273 head `abd2235`, and checkpoint `0f4ef05` are **unmerged**. The #115–#117 implementation heads are also unmerged. PR254’s underlying strategy, witness-type, and soundness APIs match this main snapshot.

### Suggested approach

The following demonstrates application without assuming an unproved passing estimate. For supplied `lines` and source hypothesis `hε : 0 < ε`, let `R` be `MIPStarRE.QPBT.directLdRejectionProbability P.extendedDirectLd (MIPStarRE.QPBT.ExtendedLineGame.strategy lines)` (`DirectLowDegree/GameValue.lean:86`). Obtain `hR0 : 0 ≤ R` by averaging `MIPStarRE.QPBT.directLdBranchRejectionProbability_nonneg` (`:129`), and `hR : R = 1 - ...value` from `MIPStarRE.QPBT.directLdRejectionProbability_eq_one_sub_value` (`:148`). Extract the universal constants before quantifying parameters:

```lean
open MIPStarRE.QPBT
obtain ⟨a, b, ha, hb, hb1, hld⟩ :=
  exists_direct_ld_soundness_of_k_eq_one
have hout := hld P.extendedDirectLd (R + ε) rfl
  (add_pos_of_nonneg_of_pos hR0 hε)
  (ExtendedLineGame.projectiveStrategy lines)
  (ExtendedLineGame.projectiveStrategy_isProjective lines)
  (by rw [ExtendedLineGame.projectiveStrategy_value]; linarith [hR])
```

This yields all three consistency conclusions with error `deltaLd a b (R+ε) P.q (2*P.m+2) P.d 1`. The two output POVMs live respectively on `S.ExpandedLocalSpace .alice × Option (DirectLdAnswer P.extendedDirectLd)` and the corresponding Bob space. Projectivization introduces **zero additional error**.

### Gaps to fill

- **Next construction:** bound the actual `R` quantitatively from the supplied point error and established line error. The identity is `9R = Rpp + Rpa + Rpd + Rap + Raa + Rdp + Rdd`; value preservation alone bounds none of these terms.
- The immediate transport target is `Rap + Rdp + Rpa + Rpd ≤ 4δL`, using PR254’s two `2δL` bounds and #273’s identities. Point agreement and the two same-line coefficient checks must then be controlled. Retain zero directions: successful completed evaluation constrains every presenting parameter; treating `none = none` as a polynomial collision is invalid.
- A small bound on `R` is still essential for the intended error estimate. The application above does not supply it. Returning the resulting POVMs to the original fixed expanded spaces, with projectivity, is a later construction; ordinary compression does not preserve projectivity.

### Searched

Read committed-main scout prompts, available issue/PR records, the prior publication scout, consumer audit, paper, blueprint, checkpoint and branch sources. Searched Mathlib by Naimark/POVM/Stinespring terminology, module paths, square-root and isometry shapes; searched local dilation, compression, resampling, collision and strategy-value APIs. No additional usable finite-POVM Naimark theorem was found in Mathlib; the local implementation already supplies it.

Source and ancestry checks only; the application fragment was not re-elaborated. Relevant PR254 and #273 files have no direct proof holes; the recorded PR254 axiom audit reports only standard axioms. Live GitHub reads/comments were unavailable because the required wrapper was blocked by the sandbox.

No files changed, builds, publication, collaboration, or new B8 attempt. Preserve anchor `2026-09-05T19:24:00Z`, **12 completed attempts, 24,242 seconds**; this scout is separately accounted.