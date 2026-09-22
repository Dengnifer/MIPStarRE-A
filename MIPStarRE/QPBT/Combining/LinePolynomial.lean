import MIPStarRE.QPBT.Combining.Lines.SubLineExtended

/-!
# Line projections and polynomial combination

Projection inclusion supplies the affine parameters used by the combining
polynomial. The geometric argument includes constant projections and singleton
lines; it does not assume an injective parameterization.
These are formalization-only auxiliary results. The evaluation results also
isolate why a coefficient answer need not define a function on a singleton
line, even after compatible affine parameters have been constructed.

## References

- Blueprint `def:combine-map`, `lem:combine-map-affine-parameters`,
  `lem:combine-map-parameter-polynomial`, and `lem:combine-map-singleton-evaluation`.
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

/-- Projection inclusion gives a combining polynomial of degree at most
`c + 1` with the affine-weighted coefficient evaluation formula, simultaneously
for every pair of degree-`c` coefficient lists. This is the parameter version
of `eq:combine-lines`; its parameters are constructed, not assumed.

**Scope restriction:** coefficient evaluation at a parameter is not evaluation
of an arbitrary answer at a geometric point of a singleton line. The latter
requires the answer to induce a constant function, as recorded in issue #695
and `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. Consequently this
auxiliary alone does not certify blueprint `def:combine-map`. -/
theorem exists_combineLinePoly_of_projection_mem {K : Type*} [Field K] {m c : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (hproj : ∀ p ∈ linePoints u v,
      projX p ∈ linePoints uX vX ∧ projZ p ∈ linePoints uZ vZ) :
    ∃ aX bX aZ bZ : K,
      IsCombineLineCompatible u v uX vX uZ vZ aX bX aZ bZ
        (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m)) ∧
      ∀ f g : Fin (c + 1) → K,
        (combineLinePolynomial aX bX aZ bZ
          (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m))
          f g).natDegree ≤ c + 1 ∧
        ∀ t : K,
          evalCoefficient (combineLinePoly aX bX aZ bZ
            (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m))
            f g) t =
          (u + t • v) (alphaVar m) * evalCoefficient f (aX + bX * t) +
            (u + t • v) (betaVar m) * evalCoefficient g (aZ + bZ * t) := by
  obtain ⟨aX, bX, aZ, bZ, hcompat⟩ :=
    exists_isCombineLineCompatible_of_projection_mem u v uX vX uZ vZ hproj
  refine ⟨aX, bX, aZ, bZ, hcompat, fun f g => ⟨?_, ?_⟩⟩
  · exact combineLinePolynomial_natDegree_le _ _ _ _ _ _ _ _ f g
  · intro t
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      (combineLinePoly_spec u v uX vX uZ vZ aX bX aZ bZ
        (u (alphaVar m)) (v (alphaVar m)) (u (betaVar m)) (v (betaVar m))
        f g hcompat t).2.2

/-- A coefficient answer on a singleton line has value `a` precisely when
its polynomial function on the parameter field is constantly `a`. Formalization
support for the evaluation distinction in `def:combine-map`; see issue #695
and `docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. Constancy of the
function does not assert that its formal polynomial has degree zero. -/
theorem evaluatesTo_zero_direction_iff {L : LdParams} {c : ℕ}
    (line : LineDesc L) (hdir : line.direction = 0) (f : DegPoly L c) (a : ScalarQ L) :
    EvaluatesTo line f line.base a ↔ ∀ t : ScalarQ L, evalCoefficient f t = a := by
  simp [EvaluatesTo, hdir]

/-- The coefficient answer representing `T` has no value at the point of a
zero-direction line, at any degree bound at least one. This certifies the
obstruction to identifying all coefficient answers with the functions on
lines in `eq:combine-lines`, documented in issue #695 and
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`. It is not a
counterexample to the combining identity for actual functions on lines. -/
theorem not_evaluatesTo_parameter_on_zero_direction {L : LdParams} {c : ℕ}
    (hc : 1 ≤ c) (line : LineDesc L) (hdir : line.direction = 0) :
    ¬ ∃ a : ScalarQ L,
      EvaluatesTo line (Pi.single (⟨1, Nat.lt_succ_of_le hc⟩ : Fin (c + 1)) 1)
        line.base a := by
  have heval (t : ScalarQ L) :
      evalCoefficient (Pi.single (⟨1, Nat.lt_succ_of_le hc⟩ : Fin (c + 1)) 1) t = t := by
    simp [evalCoefficient, Pi.single_apply, ite_mul]
  rintro ⟨a, ha⟩
  have h := (evaluatesTo_zero_direction_iff line hdir _ a).mp ha
  have hzero := h 0
  have hone := h 1
  rw [heval] at hzero hone
  exact zero_ne_one (hzero.trans hone.symm)

end MIPStarRE.QPBT
