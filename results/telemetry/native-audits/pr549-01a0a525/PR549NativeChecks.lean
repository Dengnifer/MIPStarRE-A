import Lean
import MIPStarRE.QPBT.Combining.Apply
import MIPStarRE.QPBT.Combining.Lines.DiscardedMass

/-!
# PR 549 bounded signature and axiom checks

## References

The five former sampling signatures are from commit 438a816c, and the ten
sub-line declarations are linked by blueprint lem:direct-subline-law-construction.
This untracked harness is local evidence, not a project proof module.
-/

open MIPStarRE.LDT MIPStarRE.QPBT

example (L : LdParams) :
    avgOver (dLinePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) <=
      1 / Fintype.card (ScalarQ L) :=
  dLinePointDist_zero_direction_mass_le L

example (L : LdParams) :
    avgOver (linePointDist L) (fun sample =>
      if sample.1.direction = 0 then 1 else 0) <=
      1 / (2 * Fintype.card (ScalarQ L)) :=
  linePointDist_zero_direction_mass_le L

example (L : LdParams) :
    avgOver (Distribution.prod (linePointDist L) (linePointDist L))
      (fun samples => if samples.1.1.direction = 0 then 1 else 0) <=
      1 / (2 * Fintype.card (ScalarQ L)) :=
  prod_linePointDist_zero_X_direction_mass_le L

example {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {dimension : Nat} (direction : Fin dimension -> K)
    (value : (Fin dimension -> K) -> (Fin dimension -> K) -> Real) :
    avgOver (uniformDistribution (Fin dimension -> K))
      (fun point => value (lineRepMap direction point) point) =
    avgOver (uniformDistribution (Fin dimension -> K)) (fun point =>
      avgOver (uniformDistribution K) (fun param =>
        value (lineRepMap direction point)
          (lineRepMap direction point + SMul.smul param direction))) :=
  avgOver_uniform_lineRepMap_resample_parameter direction value

example (L : LdParams) :
    (3 / 4 : Real) <= ((linePointDist L).support.filter
      (fun sample => Not (sample.1.direction = 0))).sum (linePointDist L).weight :=
  linePointDist_nondegenerate_mass_ge L

#check @subLineDist
#check @subLineDist_isProbability
#check @subLineDist_map_fst
#check @subLineDist_map_subLineXProjection
#check @subLineDist_map_subLineZProjection
#check @subLineDist_source_mixture
#check @exists_raw_of_mem_subLineDist_support
#check @subLineTripleOf_incidence
#check @subLineTripleOf_compatibility
#check @subLineTripleOf_axis_closure
#check @SubLineWitness.extended_consistencyDefect_le
#check @exists_extendedLinesWitness_established

open Lean Elab Command

elab "pr549_axioms " id:ident : command => do
  let declName <- liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let axioms := (<- Lean.collectAxioms declName).qsort Name.lt
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (fun ax => allowed.contains ax) do
    throwError m!"Unexpected axiom closure for {declName}: {axioms.toList}"
  logInfo m!"{declName}: {axioms.toList}"

pr549_axioms dLinePointDist_zero_direction_mass_le
pr549_axioms linePointDist_zero_direction_mass_le
pr549_axioms prod_linePointDist_zero_X_direction_mass_le
pr549_axioms avgOver_uniform_lineRepMap_resample_parameter
pr549_axioms linePointDist_nondegenerate_mass_ge
pr549_axioms subLineDist
pr549_axioms subLineDist_isProbability
pr549_axioms subLineDist_map_fst
pr549_axioms subLineDist_map_subLineXProjection
pr549_axioms subLineDist_map_subLineZProjection
pr549_axioms subLineDist_source_mixture
pr549_axioms exists_raw_of_mem_subLineDist_support
pr549_axioms subLineTripleOf_incidence
pr549_axioms subLineTripleOf_compatibility
pr549_axioms subLineTripleOf_axis_closure
pr549_axioms exists_subLineWitness
pr549_axioms SubLineWitness.extended_consistencyDefect_le
pr549_axioms SubLineWitness.extendedMeasurement_axis_degree
pr549_axioms combined_line_measurement_consistency
pr549_axioms exists_extendedLinesWitness_established
pr549_axioms exists_globalPairWitness
