# Issue 464: consistency defect under restriction

## Scope

Add the generic theorem
`consistencyDefect_le_restrict_add_discarded_mass` for complete measurement
families on opposite expanded placements. The theorem restores the original
defect from a positive-mass conditional defect and the discarded probability
mass.

## Source boundary

This is a formalization-only finite-conditioning estimate supporting
`lem:qld-xz-lines` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963`.
It is not a new paper premise and does not assume a global unit bound on the
defect.

## Dependencies

- PR #458, exact commit `a47b5661052192f739d5c6d12b14d9a7338b9e82`,
  supplies `consistencyDefect_integrand_le_one`.
- PR #433, exact commit `73ebd92633cba9d579692cac1c8da3dfcf057b9c`,
  supplies `avgOver_le_restrict_add_discarded_mass`.

## Exclusions

No inverse conditional-defect estimate, concrete zero-mass case, collision
bound, heterogeneous pasting result, global-pair construction, or B8 work is
included.
