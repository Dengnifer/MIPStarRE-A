<!-- mipstarre-review pr=137 head=e19f699d6f9d08cd43c0e0600d2f8607d3d5a440 -->
# Review — PR 137 @ e19f699d6f9d
VERDICT: CHANGES_REQUESTED (code=CHANGES_REQUESTED, prose=n/a)
Posted by `local/bin/review.sh` at 2026-09-04T08:39:32Z — the local replacement for the `code-review` and `prose-review` jobs of `.github/workflows/pr-review.yml`.
Branch `issue-101-ms-value-to-parity` onto `main`; merge base `97fb467c55997807aa10a90dcabdf1b0b845cfa2`; head `e19f699d6f9d08cd43c0e0600d2f8607d3d5a440`.
## Findings
Checkbox states: `[ ]` unresolved (blocks the merge), `[x]` resolved.
Resolve a finding by ticking its box in this review body.
<!-- findings:begin -->
- [ ] F1 (changes) `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean:114` — The Magic-Square-specific probability layer duplicates the generic Born-weight implementation and reusable event lemmas.  <!-- lane=code -->
- [ ] F2 (changes) `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean:45` — New theorem identifiers systematically violate the required `snake_case` naming convention.  <!-- lane=code -->
- [ ] F3 (changes) `MIPStarRE/QPBT/Test/MagicSquareTheorems/Rigidity/Relations.lean:2` — The new public facade unnecessarily imports the larger LDT tensor-placement stack.  <!-- lane=code -->
<!-- findings:end -->
## Code review
F1: `outcomeMass` duplicates the private generic `outcomeWeight` at `MIPStarRE/QPBT/Games/Defs.lean:124`, including its exact formula. Consequently, `strategy_value_eq_acceptanceMass` at line 327 is `rfl` only because two independent implementations happen to remain syntactically identical. Moreover, positivity, normalization, marginalization, and event monotonicity through line 295 use no Magic Square structure. Expose one generic strategy outcome-weight definition, make `Strategy.value` use it, and place the generic lemmas in the games layer; this file should retain only the Magic Square support, malformed-answer, mismatch, and parity specializations.
F2: Examples include `ms_support_subset_directedIncidences`, `outcomeMass_nonneg`, `sum_outcomeMass_right`, `totalRejectionMass_eq_one_sub_value`, and `aliceParityFailureMass_le`, along with similarly mixed private helper names. `AGENTS.md` requires `snake_case` for theorem and proof declarations. Rename all new theorem/lemma identifiers while the API has no downstream users.
F3: The only declarations obtained from `TensorPlacement.lean` are `opTensor_sum_left_univ` and `opTensor_sum_right_univ`; both are declared directly in `MIPStarRE/LDT/Basic/QuantumState.lean:554` and `:563`. Importing `TensorPlacement` also pulls in unused submeasurement and operator-expectation layers. Use the declaring module directly, unless the F1 refactor removes this dependency.
Mathematically, the new bounds agree with `def:ms-game`: the paper samples a constraint, one of its three incident variables, and a random player orientation at `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:563-579`; the blueprint states the same distribution and acceptance rule at `blueprint/src/chapter/ch13_qpbt_test.tex:219-221`. The support-weight argument, rejection decomposition, mismatch inclusions, and sign-parity identity are sound. No new bridge hypotheses or source-statement drift were found.
`Relations.lean` type-checks cleanly, `git diff --check` passes, and representative final theorems report only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The `exists_ms_rigidity` `sorry` in the facade predates this PR and is explicitly inventoried at `local/briefs/42-residual-brief.md:186`; it remains known baseline proof debt rather than a new finding here.
