import MIPStarRE.QPBT.Combining.Lines.SubLineExtended

/-!
# Line projections and polynomial combination

Projection inclusion supplies the affine parameters used by the combining
polynomial. The geometric argument includes constant projections and singleton
lines; it does not assume an injective parameterization.

## References

- Blueprint `def:combine-map`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`,
  especially `eq:combine-lines`.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:106-124`,
  where `def:line` explicitly allows zero directions.
- Issue #695 and `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex` for the
  separate question of evaluating coefficient answers on singleton lines.
-/

namespace MIPStarRE.QPBT

/-- Inclusion of one affine line in another gives an affine change of
parameter. Parameters for the first line's points at zero and one determine
the intercept and slope of this change. Neither direction need be nonzero.
This is geometric support for the domain of `eq:combine-lines`, rather than
an assertion that every coefficient answer defines a function on a line. -/
theorem exists_affine_parameters_of_linePoints_subset {K : Type*} [Field K] {m : ℕ}
    (u v u' v' : Fin m → K) (h : linePoints u v ⊆ linePoints u' v') :
    ∃ a b : K, u = u' + a • v' ∧ v = b • v' := by
  obtain ⟨a, ha⟩ := h (show u ∈ linePoints u v from ⟨0, by simp⟩)
  obtain ⟨s, hs⟩ := h (show u + v ∈ linePoints u v from ⟨1, by simp⟩)
  refine ⟨a, s - a, ha, ?_⟩
  calc
    v = (u + v) - u := by abel
    _ = (u' + s • v') - (u' + a • v') := by rw [hs, ha]
    _ = (s - a) • v' := by module

/-- The projection-inclusion hypothesis preceding `eq:combine-lines` supplies
all the affine compatibility data. In particular, no subline witness and no
nonzero-direction hypothesis are needed. This proves the geometric part of
blueprint `def:combine-map` on its full stated domain. -/
theorem exists_isCombineLineCompatible_of_projection_mem {K : Type*} [Field K] {m : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (hproj : ∀ p ∈ linePoints u v,
      projX p ∈ linePoints uX vX ∧ projZ p ∈ linePoints uZ vZ) :
    ∃ aX bX aZ bZ : K,
      IsCombineLineCompatible u v uX vX uZ vZ aX bX aZ bZ
        (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) := by
  have hX : linePoints (projX u) (projX v) ⊆ linePoints uX vX := by
    rintro p ⟨t, rfl⟩
    simpa only [projX_add, projX_smul] using (hproj (u + t • v) ⟨t, rfl⟩).1
  have hZ : linePoints (projZ u) (projZ v) ⊆ linePoints uZ vZ := by
    rintro p ⟨t, rfl⟩
    simpa only [projZ_add, projZ_smul] using (hproj (u + t • v) ⟨t, rfl⟩).2
  obtain ⟨aX, bX, haX, hbX⟩ :=
    exists_affine_parameters_of_linePoints_subset _ _ _ _ hX
  obtain ⟨aZ, bZ, haZ, hbZ⟩ :=
    exists_affine_parameters_of_linePoints_subset _ _ _ _ hZ
  exact ⟨aX, bX, aZ, bZ,
    isCombineLineCompatible_of_blocks u v uX vX uZ vZ aX bX aZ bZ haX hbX haZ hbZ⟩

end MIPStarRE.QPBT
