# Current-module axiom probe for issue 295

Probe SHA256: e3ae8a7bf248a7d0245e55cb97a580b2080ca10d690cf04f5ec6ffeb92b7c88c.
Log SHA256: 85ee1aa52f5870c4e80481dd70263fa086a21b22d79cbef0b76f5ffba52471f1.

```lean
import MIPStarRE.QPBT.Combining.PolynomialImageBounds

open Lean Elab Command

private def targetNames : Array String := #[
  "orderedIndicator",
  "diagonalIndicator",
  "orderedIndicator_gram_of_ne_zero",
  "orderedIndicator_norm_sq_of_ne_zero",
  "diagonalIndicator_bounds",
  "orderedIndicator_zero",
  "orderedIndicator_gram_le_one",
  "abs_orderedIndicator_norm_sq_sub_diagonal_le",
  "avg_abs_orderedIndicator_norm_sq_sub_diagonal_le",
  "avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le",
  "sum_projective_state_norm_sq",
  "avg_sum_abs_projective_orderedIndicator_le",
  "avg_uniform_sum_abs_projective_orderedIndicator_le",
  "orderedIndicator_reverse",
  "exists_nonzero_nonlinear_coeff",
  "specialization_ne_linear_of_coeff",
  "avg_specialization_eq_linear_le_of_coeff",
  "avg_diagonalIndicator_le_of_not_linear",
  "avg_orderedIndicator_norm_sq_le_of_not_linear",
  "avg_sum_orderedIndicator_norm_sq_le_of_not_linear",
  "nonlinear_mass_le_ordered_error"
]

private def suffixMatches (declName : Name) (target : String) : Bool :=
  declName.toString.endsWith ("." ++ target)

elab "audit_polynomial_image_bounds" : command => do
  let env ← getEnv
  for target in targetNames do
    let hits := env.constants.toList.foldl (init := #[]) fun acc entry =>
      if suffixMatches entry.1 target then acc.push entry.1 else acc
    if hits.size != 1 then
      logError m!"TARGET|{target}|MATCH_COUNT|{hits.size}|MATCHES|{hits.toList}"
    else
      let declName := hits[0]!
      let axioms := (← liftCoreM <| Lean.collectAxioms declName).qsort Name.lt
      let ci ← match env.find? declName with
        | some ci => pure ci
        | none => throwError m!"missing constant info for {declName}"
      logInfo m!"TARGET|{target}|ACTUAL|{declName}|AXIOMS|{axioms.toList}|TYPE|{ci.type}"

audit_polynomial_image_bounds
```

```text
TARGET|orderedIndicator|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|{F : Type u_1} →
  {ι : Type u_2} →
    [Field F] →
      [inst : Fintype F] →
        [DecidableEq F] →
          [inst_2 : Fintype ι] →
            [inst_3 : DecidableEq ι] →
              MIPStarRE.Quantum.Measurement F ι → MIPStarRE.Quantum.Measurement F ι → F → F → F → MIPStarRE.Quantum.Op ι
TARGET|diagonalIndicator|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|{F : Type u_1} →
  {ι : Type u_2} →
    [Field F] →
      [inst : Fintype F] →
        [DecidableEq F] →
          [inst_2 : Fintype ι] →
            [inst_3 : DecidableEq ι] →
              MIPStarRE.Quantum.Measurement F ι → MIPStarRE.Quantum.Measurement F ι → F → F → F → MIPStarRE.Quantum.Op ι
TARGET|orderedIndicator_gram_of_ne_zero|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_of_ne_zero|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective X →
    ∀ (α β a : F),
      β ≠ 0 →
        Matrix.conjTranspose (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) *
            MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a =
          MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a
TARGET|orderedIndicator_norm_sq_of_ne_zero|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_norm_sq_of_ne_zero|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective X →
    ∀ (α β a : F),
      β ≠ 0 →
        ∀ (ψ : EuclideanSpace ℂ ι),
          ‖MIPStarRE.QPBT.applyOperatorToState (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) ψ‖ ^
              2 =
            MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
              (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a)
TARGET|diagonalIndicator_bounds|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator_bounds|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective Z →
    ∀ (α β a : F),
      0 ≤ MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a ∧
        MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a ≤ 1
TARGET|orderedIndicator_zero|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_zero|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι) (α a : F),
  MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α 0 a = (X.postprocess fun b => α * b).effect a
TARGET|orderedIndicator_gram_le_one|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_gram_le_one|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective X →
    MIPStarRE.QPBT.Measurement.IsProjective Z →
      ∀ (α β a : F),
        Matrix.conjTranspose (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) *
            MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a ≤
          1
TARGET|abs_orderedIndicator_norm_sq_sub_diagonal_le|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.abs_orderedIndicator_norm_sq_sub_diagonal_le|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective X →
    MIPStarRE.QPBT.Measurement.IsProjective Z →
      ∀ (α β a : F) (ψ : EuclideanSpace ℂ ι),
        |‖MIPStarRE.QPBT.applyOperatorToState (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β a) ψ‖ ^ 2 -
              MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
                (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β a)| ≤
          if β = 0 then ‖ψ‖ ^ 2 else 0
TARGET|avg_abs_orderedIndicator_norm_sq_sub_diagonal_le|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.avg_abs_orderedIndicator_norm_sq_sub_diagonal_le|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective X →
    MIPStarRE.QPBT.Measurement.IsProjective Z →
      ∀ (α : F) (a : F → F) (ψ : EuclideanSpace ℂ ι),
        (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution F) fun β =>
            |‖MIPStarRE.QPBT.applyOperatorToState (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β (a β))
                      ψ‖ ^
                  2 -
                MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
                  (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β (a β))|) ≤
          (↑(Fintype.card F))⁻¹ * ‖ψ‖ ^ 2
TARGET|avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_abs_orderedIndicator_norm_sq_sub_diagonal_le|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {Γ : Type u_3} [inst_5 : Fintype Γ]
  (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective X →
    MIPStarRE.QPBT.Measurement.IsProjective Z →
      ∀ (α : F) (a : Γ → F → F) (ψ : Γ → EuclideanSpace ℂ ι),
        (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution F) fun β =>
            ∑ g,
              |‖MIPStarRE.QPBT.applyOperatorToState
                        (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β (a g β)) (ψ g)‖ ^
                    2 -
                  MIPStarRE.QPBT.DistanceCalculus.stateQForm (ψ g)
                    (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β (a g β))|) ≤
          (↑(Fintype.card F))⁻¹ * ∑ g, ‖ψ g‖ ^ 2
TARGET|sum_projective_state_norm_sq|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.sum_projective_state_norm_sq|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {ι : Type u_2} [inst : Fintype ι] [inst_1 : DecidableEq ι] {Γ : Type u_3} [inst_2 : Fintype Γ]
  (S : MIPStarRE.Quantum.Measurement Γ ι),
  MIPStarRE.QPBT.Measurement.IsProjective S →
    ∀ (ψ : EuclideanSpace ℂ ι), ∑ g, ‖MIPStarRE.QPBT.applyOperatorToState (S.effect g) ψ‖ ^ 2 = ‖ψ‖ ^ 2
TARGET|avg_sum_abs_projective_orderedIndicator_le|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_abs_projective_orderedIndicator_le|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {Γ : Type u_3} [inst_5 : Fintype Γ]
  (S : MIPStarRE.Quantum.Measurement Γ ι) (X Z : MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective S →
    MIPStarRE.QPBT.Measurement.IsProjective X →
      MIPStarRE.QPBT.Measurement.IsProjective Z →
        ∀ (α : F) (a : Γ → F → F) (ψ : EuclideanSpace ℂ ι),
          (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution F) fun β =>
              ∑ g,
                |‖MIPStarRE.QPBT.applyOperatorToState
                          (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator X Z α β (a g β))
                          (MIPStarRE.QPBT.applyOperatorToState (S.effect g) ψ)‖ ^
                      2 -
                    MIPStarRE.QPBT.DistanceCalculus.stateQForm (MIPStarRE.QPBT.applyOperatorToState (S.effect g) ψ)
                      (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator X Z α β (a g β))|) ≤
            (↑(Fintype.card F))⁻¹ * ‖ψ‖ ^ 2
TARGET|avg_uniform_sum_abs_projective_orderedIndicator_le|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.avg_uniform_sum_abs_projective_orderedIndicator_le|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {T : Type u_3} {Γ : Type u_4} [inst_5 : Fintype T]
  [inst_6 : DecidableEq T] [inst_7 : Nonempty T] [inst_8 : Fintype Γ] (S : MIPStarRE.Quantum.Measurement Γ ι)
  (X Z : T → MIPStarRE.Quantum.Measurement F ι),
  MIPStarRE.QPBT.Measurement.IsProjective S →
    (∀ (t : T), MIPStarRE.QPBT.Measurement.IsProjective (X t)) →
      (∀ (t : T), MIPStarRE.QPBT.Measurement.IsProjective (Z t)) →
        ∀ (a : Γ → T → F → F → F) (ψ : EuclideanSpace ℂ ι),
          (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (T × F × F)) fun tαβ =>
              ∑ g,
                |‖MIPStarRE.QPBT.applyOperatorToState
                          (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X tαβ.1) (Z tαβ.1) tαβ.2.1 tαβ.2.2
                            (a g tαβ.1 tαβ.2.1 tαβ.2.2))
                          (MIPStarRE.QPBT.applyOperatorToState (S.effect g) ψ)‖ ^
                      2 -
                    MIPStarRE.QPBT.DistanceCalculus.stateQForm (MIPStarRE.QPBT.applyOperatorToState (S.effect g) ψ)
                      (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X tαβ.1) (Z tαβ.1) tαβ.2.1 tαβ.2.2
                        (a g tαβ.1 tαβ.2.1 tαβ.2.2))|) ≤
            (↑(Fintype.card F))⁻¹ * ‖ψ‖ ^ 2
TARGET|orderedIndicator_reverse|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator_reverse|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] (X Z : MIPStarRE.Quantum.Measurement F ι) (α β a : F),
  (∑ bc, if α * bc.1 + β * bc.2 = a then Z.effect bc.2 * X.effect bc.1 else 0) =
    MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator Z X β α a
TARGET|exists_nonzero_nonlinear_coeff|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.exists_nonzero_nonlinear_coeff|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {R : Type u_3} [inst : CommRing R] (p : MvPolynomial (Fin 2) R),
  (¬∃ u v, p = MvPolynomial.C u * MvPolynomial.X 0 + MvPolynomial.C v * MvPolynomial.X 1) →
    ∃ e, (e ≠ fun₀ | 0 => 1) ∧ (e ≠ fun₀ | 1 => 1) ∧ MvPolynomial.coeff e p ≠ 0
TARGET|specialization_ne_linear_of_coeff|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.specialization_ne_linear_of_coeff|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} [inst : Field F] {n : ℕ} (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F))
  (e : Fin 2 →₀ ℕ),
  (e ≠ fun₀ | 0 => 1) →
    (e ≠ fun₀ | 1 => 1) →
      ∀ (u : Fin n → F),
        (MvPolynomial.eval u) (MvPolynomial.coeff e p) ≠ 0 →
          ∀ (b c : F),
            (MvPolynomial.map (MvPolynomial.eval u)) p ≠
              MvPolynomial.C b * MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1
TARGET|avg_specialization_eq_linear_le_of_coeff|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_specialization_eq_linear_le_of_coeff|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F] {n : ℕ}
  (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)) (e : Fin 2 →₀ ℕ),
  (e ≠ fun₀ | 0 => 1) →
    (e ≠ fun₀ | 1 => 1) →
      ∀ (u : Fin n → F),
        (MvPolynomial.eval u) (MvPolynomial.coeff e p) ≠ 0 →
          ∀ (b c : F),
            (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) fun v =>
                if (MvPolynomial.eval v) ((MvPolynomial.map (MvPolynomial.eval u)) p) = v 0 * b + v 1 * c then 1
                else 0) ≤
              ↑(max 1 p.totalDegree) / ↑(Fintype.card F)
TARGET|avg_diagonalIndicator_le_of_not_linear|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_diagonalIndicator_le_of_not_linear|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {n : ℕ} (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)),
  (¬∃ r s, p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1) →
    ∀ (X Z : (Fin n → F) → MIPStarRE.Quantum.Measurement F ι),
      (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (Z u)) →
        ∀ (ψ : EuclideanSpace ℂ ι),
          (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin n → F)) fun u =>
              MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) fun v =>
                MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
                  (MIPStarRE.QPBT.PolynomialImageBounds.diagonalIndicator (X u) (Z u) (v 0) (v 1)
                    ((MvPolynomial.eval v) ((MvPolynomial.map (MvPolynomial.eval u)) p)))) ≤
            ↑((p.support.sup fun e => (MvPolynomial.coeff e p).totalDegree) + max 1 p.totalDegree) / ↑(Fintype.card F) *
              ‖ψ‖ ^ 2
TARGET|avg_orderedIndicator_norm_sq_le_of_not_linear|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_orderedIndicator_norm_sq_le_of_not_linear|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {n : ℕ} (p : MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)),
  (¬∃ r s, p = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1) →
    ∀ (X Z : (Fin n → F) → MIPStarRE.Quantum.Measurement F ι),
      (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (X u)) →
        (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (Z u)) →
          ∀ (ψ : EuclideanSpace ℂ ι),
            (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin n → F)) fun u =>
                MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) fun v =>
                  ‖MIPStarRE.QPBT.applyOperatorToState
                        (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
                          ((MvPolynomial.eval v) ((MvPolynomial.map (MvPolynomial.eval u)) p)))
                        ψ‖ ^
                    2) ≤
              ↑((p.support.sup fun e => (MvPolynomial.coeff e p).totalDegree) + max 1 p.totalDegree + 1) /
                  ↑(Fintype.card F) *
                ‖ψ‖ ^ 2
TARGET|avg_sum_orderedIndicator_norm_sq_le_of_not_linear|ACTUAL|_private.MIPStarRE.QPBT.Combining.PolynomialImageBounds.0.MIPStarRE.QPBT.PolynomialImageBounds.avg_sum_orderedIndicator_norm_sq_le_of_not_linear|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {n : ℕ} {Γ : Type u_3} (s : Finset Γ)
  (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)),
  (∀ g ∈ s, ¬∃ r t, p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1) →
    ∀ (X Z : (Fin n → F) → MIPStarRE.Quantum.Measurement F ι),
      (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (X u)) →
        (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (Z u)) →
          ∀ (ψ : Γ → EuclideanSpace ℂ ι),
            (MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin n → F)) fun u =>
                MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) fun v =>
                  ∑ g ∈ s,
                    ‖MIPStarRE.QPBT.applyOperatorToState
                          (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
                            ((MvPolynomial.eval v) ((MvPolynomial.map (MvPolynomial.eval u)) (p g))))
                          (ψ g)‖ ^
                      2) ≤
              ∑ g ∈ s,
                ↑(((p g).support.sup fun e => (MvPolynomial.coeff e (p g)).totalDegree) + max 1 (p g).totalDegree + 1) /
                    ↑(Fintype.card F) *
                  ‖ψ g‖ ^ 2
TARGET|nonlinear_mass_le_ordered_error|ACTUAL|MIPStarRE.QPBT.PolynomialImageBounds.nonlinear_mass_le_ordered_error|AXIOMS|[propext,
 Classical.choice,
 Quot.sound]|TYPE|∀ {F : Type u_1} {ι : Type u_2} [inst : Field F] [inst_1 : Fintype F] [inst_2 : DecidableEq F]
  [inst_3 : Fintype ι] [inst_4 : DecidableEq ι] {n : ℕ} {Γ : Type u_3} (s : Finset Γ)
  (p : Γ → MvPolynomial (Fin 2) (MvPolynomial (Fin n) F)),
  (∀ g ∈ s, ¬∃ r t, p g = MvPolynomial.C r * MvPolynomial.X 0 + MvPolynomial.C t * MvPolynomial.X 1) →
    ∀ (X Z : (Fin n → F) → MIPStarRE.Quantum.Measurement F ι),
      (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (X u)) →
        (∀ (u : Fin n → F), MIPStarRE.QPBT.Measurement.IsProjective (Z u)) →
          ∀ (ψ : Γ → EuclideanSpace ℂ ι),
            ∑ g ∈ s, ‖ψ g‖ ^ 2 ≤
              (2 *
                  MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin n → F)) fun u =>
                    MIPStarRE.LDT.avgOver (MIPStarRE.LDT.uniformDistribution (Fin 2 → F)) fun v =>
                      ∑ g ∈ s,
                        ‖ψ g -
                              MIPStarRE.QPBT.applyOperatorToState
                                (MIPStarRE.QPBT.PolynomialImageBounds.orderedIndicator (X u) (Z u) (v 0) (v 1)
                                  ((MvPolynomial.eval v) ((MvPolynomial.map (MvPolynomial.eval u)) (p g))))
                                (ψ g)‖ ^
                          2) +
                2 *
                  ∑ g ∈ s,
                    ↑(((p g).support.sup fun e => (MvPolynomial.coeff e (p g)).totalDegree) + max 1 (p g).totalDegree +
                            1) /
                        ↑(Fintype.card F) *
                      ‖ψ g‖ ^ 2
```
