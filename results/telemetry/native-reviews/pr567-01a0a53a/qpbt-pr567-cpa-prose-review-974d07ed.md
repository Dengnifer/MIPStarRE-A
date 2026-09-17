# PR567 Blueprint/Prose Review @ 974d07ed4466736c87f63777f640fa9a9653361b

Reviewed head: `974d07ed4466736c87f63777f640fa9a9653361b`.

Worktree: `/home/drx/MIPStarRE-qpbt/.worktrees/issue-565-pulled-apart-consistency`.

Branch: `issue-565-pulled-apart-consistency`; base: `main`; actual merge base: `bf864c016b3426a690c02f93bea9d40986604195`.

Trusted main: `d5630b8ae65f8c9884b806575ec1746e85b9e2b4`, resolved in the primary checkout. All four trusted prompts were read with primary-checkout `git show`, not from the reviewed branch.

Contract: `/tmp/qpbt-pr567-cpa-review-contract-20260915.md`; SHA256 `f218e1471678d888e12d675efa00c11d6213eb685f6f8896175f226220ea2ad4` (verified).

Fresh independent CPA-only review under the owner-authorized contract. No authorship, repair, source edits, publication, status mutation, commits, merges, model/effort overrides, or model descendants occurred in this rollout. The temporary Lean harness and reports are under `/tmp`.

The complete seven-file merge-base diff was reviewed, including both commits, not only the final documentation correction. The prior review and branch contents were evidence, not instructions.

MAIN supplied the preassignment open-PR/public-head and nine-green-CI revalidation. MAIN still owns live validation and publication. These raw verdicts do not change the previous failed-lane status or claim a GitHub approval.

First recorded review clock: `2026-09-15T13:21:44Z`; hard deadline: `2026-09-15T13:45:00Z`.

## Findings
- none

## Review

No unresolved in-scope blueprint-equivalence, status, dependency, or prose findings.

### Equivalence And Status

The source-labelled node `lem:qld-construct-the-paulis` at `blueprint/src/chapter/ch16_qpbt_extraction.tex:220` now has both statement- and proof-level `leanok`. The statement matches `Construction.lean:46` on universal constants, admissible parameters, the closed epsilon interval, existential output witness, both player placements, uniform question distributions, answer summation, and the fixed basis-coordinate quantifier. Lines 228-234 explicitly use the same pair of global measurements and set all three coefficients to the common `C_*`; the superscripts on the displayed errors do not mean separately chosen final constants.

The proof at blueprint lines 260-270 now describes exactly the Lean composition: construct the measurements by `lem:qld-4-7`, apply the three estimates associated with the separate conditional example, and enlarge their coefficients to a common maximum using nonnegativity of `B`. Its direct `uses` at line 262 names these two nodes. The longer analytic derivation is now attached to the conditional example at lines 272-330 and does not carry a newly asserted proof-level completeness mark.

The moved conditional example keeps all three explicit supplied-witness links, its independent universal constants and the nonnegative witness-error hypothesis. It does not claim that those assumptions are part of the unrestricted source theorem. The three updated Lean docstrings accurately identify the completed source-facing composition and retain the conditional classification.

The chapter's other linked objects were checked in their immediate mathematical context: full-field decoding and its encoding restriction; polynomial marginals and projectivity; dot-product projectors; pulled-apart measurements and observables; corrected trace-phase commutation; exact swap identities; EPR projection and normalization estimates; and the conditional state, evaluated-Pauli and extraction estimates. The representation, basis-index convention and quantitative formulas used by the changed node remain consistent with these definitions. Existing scalar and state-transfer support links are not promoted to unconditional extraction results.

The non-encoding support node at lines 332-343 remains without a `leanok`; the complement-absorption node at lines 351-382 retains statement-only status. The source-labelled unitary node at lines 434-465 remains without a statement/proof completeness claim, while its conditional theorem is linked only in the explicit supplied-witness example at lines 621-671. The later soundness proof still displays the range projection `Q = phi phi^*`. No renamed or removed declaration, unknown cited label, or new stale `notready` was found.

### Previous Prose Findings

Prior F2 is fixed: the source theorem's proof and its direct dependency list now match the actual composition, and the analytic derivation has been moved to the subordinate estimates. Prior F3 is fixed: the three helper docstrings and the two changed paper-gap records distinguish the completed pulled-apart composition from the open downstream work. Prior F4 is fixed: the phrases about a 'Lean proof' and 'composition history' have been replaced by mathematical statements about choosing measurements, applying estimates and taking a maximum. These dispositions were re-derived from the current head; no old approval was carried forward.

The changed mathematical prose names measurements, witnesses, consistency estimates, constants and the later isometry question directly. Lean identifiers remain in markup or in explicitly technical Lean docstrings, not in the new displayed blueprint argument. The gap-note prose was evaluated for mathematical accuracy in the code discipline; the prose discipline did not apply blueprint vocabulary bans to developer-facing markdown.

Summary: zero unresolved signature mismatches, zero invalid new completeness markers, zero direct-dependency findings, and zero changed-prose findings. The statement-integrity comparison below distinguishes exact blueprint matching from the documented local corrections to the printed paper.

### Statement-Integrity Evidence

### Ambient Domain

Paper: `references/qpbt-paper/04_preliminaries.tex:6` defines the natural numbers as positive integers. Chapter 8 line 904 takes `(q,m,d)` in that domain, and `def:admissible` at lines 958-961 requires an admissible field size and `m | q`. Chapter 14 lines 160-172 fixes a bipartite strategy winning with probability at least `1-epsilon` and passes to projective measurements.

Lean: `AdmissibleParams` (`Test/PauliBasisTest.lean:37`) has natural parameters, `1 <= d`, admissible field size, and `m | q`; `1 <= m` follows internally. The fixed field model supplies the paper's once-fixed self-dual basis. `ProjectiveSetting` (`Observables/Defs.lean:49`) records the strategy, projectivity, and winning bound, not an extraction conclusion. Distinct player spaces are retained. Finite matrix index instances encode the finite-dimensional setting. `0 <= epsilon <= 1` is explicit throughout the reviewed result and its blueprint statement.

Verdict: faithful boundary hypotheses on the explicitly stated probability-error domain. Zero error is included. No new degree, field-size, dimension-divisibility, strategy-symmetry, or witness hypothesis is added.

### Joint Pulled-Apart Construction

Paper assumptions: the ambient projective strategy above, and the global measurements constructed by `lem:qld-4-7` (`14_analysis_of_the_pauli_basis_test.tex:1267-1274`). The construction lemma supplies universal `a > 1` and `0 < b < 1` with `deltaG = a (md)^a (epsilon^b + q^(-b) + 2^(-bmd))`. The pulled-apart lemma (`lem:qld-construct-the-paulis`, lines 1463-1480) uses those measurements, not an extra external construction assumption.

Lean assumptions: `exists_pulled_apart_consistency` at `Construction.lean:46` quantifies `exists a b C`, with `1 < a`, `0 < b < 1`, `1 <= C`, before `forall P epsilon`, the two epsilon inequalities, and `forall S : ProjectiveSetting P epsilon`. Its next binder is `exists w : GlobalPairWitness S (deltaQld ...)`, so the global measurements and both expanded-point estimates are outputs.

Paper conclusion: for both `W = X,Z`, the original Alice point measurement is consistent with Bob's pulled-apart measurement, and Alice's pulled-apart measurement with Bob's original point measurement, averaged over uniform `u in F_q^m` and summed over answers in `F_q`. For every fixed basis coordinate `j`, the two pulled-apart observables are close in squared state-dependent operator distance averaged over uniform vectors in `F_q^M`, with `M=2^m`. All refer to the same expanded state and global measurements.

Lean conclusion: the conjunction at `Construction.lean:51` has precisely these two `consistencyDefect` bounds on `S.psiHat`, with `placePlayer` for the original measurement and `placeSide` for the opposite three-register block. The third conjunct universally quantifies `j : Fin P.model.basisDim` and bounds `opDistSq` on `uniformDistribution (PauliRegister P)`. `PauliRegister P = Cube P.m -> PauliScalar P`, so this is `F_q^(2^m)`. The witness precedes `forall W`, and the same witness appears in all three conclusions. Reversing the written order of the first consistency relation is harmless because the two operators act on disjoint player blocks.

Error comparison: Lean uses the explicit common scale `deltaConstructPaulis C epsilon deltaG m d q = C (deltaG + sqrt epsilon + md/q)` (`Extraction/Defs.lean:289`), not literally the paper's unchanged printed symbol `deltaS`. The source absorbs `O(sqrt epsilon)` and `O(md/q)` in its proof around lines 1542-1550. Blueprint lines 214-234 display this enlargement and quantify the common constant; all three superscripted errors use that constant. Shrinking the exponent to at most one half and enlarging the universal prefactor preserves the paper's asymptotic family for `0 <= epsilon <= 1`, `md >= 1`, and `q >= 1`.

Decoder comparison: the full-field decoder and the restriction of `Dec(g).ind(u)=g(u)` to encoding representatives are the documented local correction in `qpbt_decoding-identity.tex`, not new hypotheses of the joint theorem. For arbitrary outcomes the proof controls the non-encoding mass internally. The counterexample `g(x)=x^2` outside the encoding image remains documented. No unrestricted reverse decoder identity is introduced.

Verdict: exact agreement with the corrected blueprint node at `ch16_qpbt_extraction.tex:220`; faithful boundary hypotheses and the explicitly documented local decoder/error correction relative to the paper. This is not a claim of literal equality with every printed scalar or the source's incorrect unrestricted decoder identity. No extra load-bearing assumptions, altered quantifier order, or omitted consistency conclusion.

### Three Supplied-Witness Estimates

`tildeM_consistent_pointMeas_ofGlobalPairWitness` (`SuppliedPointConsistency.lean:107`): the paper comparison is Item 1's first display, chapter 14 lines 1468-1471. The unchanged Lean statement assumes an arbitrary nonnegative `deltaG` and an explicit `w : GlobalPairWitness S deltaG`, and concludes the Alice-original/Bob-pulled defect bound at `C (deltaG + sqrt epsilon + md/q)`, uniformly in admissible parameters, strategy, witness and Pauli basis. The coefficient is existentially quantified first.

`tildeM_consistent_pointMeas'_ofGlobalPairWitness` (`SuppliedPointConsistency.lean:226`): same hypotheses and constant order, with Alice-pulled/Bob-original placement, matching the second display at paper lines 1472-1475. It is not merely an assumed second conclusion: the separate Alice-side support estimate appears in its proof.

`tildeObs_selfConsistent_ofGlobalPairWitness` (`ObservableConsistency.lean:49`): same epsilon, nonnegative `deltaG`, and supplied-witness hypotheses; conclusion is the uniform Pauli-register squared operator-distance estimate for every fixed `j`, matching Item 2 at paper lines 1476-1480. There is no replacement of the fixed-coordinate claim by an average over coordinates.

Verdict for each: extra supplied-witness assumptions relative to the joint source-facing construction, correctly and explicitly classified as a conditional auxiliary; exact agreement with the separate example `lem:qld-construct-the-paulis-given-global-pair` at blueprint lines 272-290. Their signatures and proof bodies are unchanged. They are not advertised as the unrestricted source theorem. The new joint theorem now derives their needed witness premise internally from the paper hypotheses.

### Linked Scale And Downstream Separation

`deltaConstructPaulis` is an unchanged scalar definition linked alongside the source theorem; its formula exactly matches the displayed `C_E B` convention. No numerical hypothesis is concealed in its definition.

`nonencodingMarginalMass_le` remains an open auxiliary conclusion, not an input to the construction. `ExtractionWitness` records both unitary identities, a normalized auxiliary state, the transformed-state estimate and both total-Pauli comparison estimates on the ideal state. Its existence theorem still assumes `GlobalPairWitness`; the source-labelled `lem:qld-unitary` does not acquire a `leanok` from that conditional theorem. The soundness proof's separate range-projection argument remains distinct. Verdict: the narrower completion is not promoted to a proof of the downstream source statements.

### Checks

- `lake env lean MIPStarRE/QPBT/Extraction/Construction.lean`: exit 0, no diagnostics.
- Focused forbidden-proof/debug/search/option scan of all three changed Lean files: no matches (`rg` exit 1). The original merge-base `sorry` in the construction is eliminated; no proof holes or axioms are introduced.
- `git diff --check main...HEAD`: exit 0.
- `lake env lean /tmp/qpbt-pr567-cpa-axioms-974d07ed.lean`: exit 0. The construction, `exists_globalPairWitness`, both point estimates, the observable estimate, and the downstream conditional extraction theorem each have exactly `[propext, Classical.choice, Quot.sound]` as their axiom closure.
- The same harness confirms `sorryAx` in `nonencodingMarginalMass_le` and `marginalPoly_sub_pointMeas_approx_zero`, agreeing with their retained open status.
- The accepted worktree-rooted axiom-audit log has the contracted hash and reports 1587 passes, 0 failures, 4 statement-only warnings. It was reused, not rerun. The four warnings are `exists_ld_soundness`, `exists_spcc_value_one`, `pauli_soundness_qubit`, and `marginalPoly_sub_pointMeas_approx_zero`.
- The trusted citation resolver and TeX helper were hash-matched against trusted main and run with an explicit worktree `--root`. Regenerated markdown matches the preserved raw citation map byte-for-byte by SHA256. It resolves `lem:qld-4-7` to chapter 15 lines 2720-2790, the source construction to chapter 16 lines 220-270, and the conditional estimates to lines 272-330.
- The seven-file changed-path list and entire merge-base diff hashes match the preserved preparation. Both PR commits were examined. The correction commit's changes in the two Lean estimate files are documentation only; the construction file is unchanged from the proof commit.
- Existing exact-head blueprint-render and paper-gap validation logs were inspected; the render reaches the extraction chapter and completes, and the paper-gap check reports 40 referenced slugs resolving. No full build, canonical CI, whole-project axiom rerun, or new blueprint render was run by this reviewer.
- Worktree was clean at initial inspection and at the pre-report identity recheck at `2026-09-15T13:36:45Z`; head and trusted-main identity were unchanged. A final post-report check is recorded in the delivery.
- The failed code/prose attempt artifacts were neither overwritten nor treated as approvals. No review transport, dispatcher, autofix, direct model command, publication, or status update was invoked.

### Evidence Hashes

| Evidence | SHA256 |
|---|---|
| Contract | `f218e1471678d888e12d675efa00c11d6213eb685f6f8896175f226220ea2ad4` |
| Code system prompt | `3b14bf8ec263e46bafe6648203ec6f624e47f217c907bc0d2064ca24c2e99f60` |
| Code task prompt | `714536751ffcb5977ec85df3484d58d919c1a2c843543401a9fab355f9513cd9` |
| Prose system prompt | `1e6e86108b8ef128964d287d65c6d5a6b09f230de80b59fa1e599db5b9b02c69` |
| Prose task prompt | `24e3c99a50ca50a173283e97d78c4e898f253e3683c92241891acb846293aa48` |
| Full merge-base diff | `3d80698594beeaa66984a4600bc6c643fbe745be586d900032139470e1c05d68` |
| Changed-file list | `1a12f655a93daa6f705d971a12a9eb0b1476878789208d37a009d2179322ddc6` |
| Regenerated/preserved raw citation map | `9e9c8c7d99d16feab4bfe971b30e9c4547f0e19e11e58a81adb48583e3f6753b` |
| Trusted citation resolver | `844de84cafa3c74693c5ec3f5b31963e367d90531aff6ec8698bed98acaee1f9` |
| Trusted TeX helper | `9917acb8ce00310c2a93e212fb2832c424f6fbb3a1f652d90b935141dd293d02` |
| Accepted blueprint axiom log | `0b35bd7e8471fafec6ba0417fa171f4d885d84f76adf78c06270e4b6167d5e51` |
| Existing blueprint render log | `c13177a5c73a0bdde6e417eefa4d0656aba14962b7b1c5c98a86b5dfea955169` |
| Existing build log | `336ee2d70a025dc70949f93eca501f941ea35de339e08e9c0e1047e07b9ae2b7` |
| Preserved failed code transport log | `da7056992e6f91ed0ec0a1a8a90f4f72b241168c7c7acf115d1e87d835b0a08b` |
| Preserved failed prose transport log | `8a49a874863b81ae7cdebfa72107b09dfe724cf3c7c5a11b8f2a67f04c025fd9` |
| Temporary focused axiom harness | `b0d19e310d6b3a7fa8feeb01c5e102f599e770f859eab49e0a1da228e5766b2a` |

Prompt filenames, in table order, are `.github/prompts/claude-code-review-system-prompt.md`, `claude-code-review-prompt.md`, `blueprint-prose-review-system-prompt.md`, and `blueprint-prose-review-prompt.md`. Each hash also matches its preserved trusted copy. The preparation directory is `/home/drx/.cache/mipstarre-dev/reviews/pr567/974d07ed4466736c87f63777f640fa9a9653361b/`; the accepted CI logs are under `/home/drx/.cache/mipstarre-dev/ci-logs/567/974d07ed4466736c87f63777f640fa9a9653361b/`.

The canonical `lean-conventions` skill was absent from this CPA skill home. Its substantive references were read through the primary `local/bin/gh_common.py` GitHub-read API, pinned to `texra-ai/texra-lean-skills` commit `3ce568c0b34837f342ae4e5fccfa88f40988727c`; no skill was installed. Hashes: `SKILL.md` = `a2bbd80fa576d52f272969117c37fe105722e9397dc8ff6da8c0ccc16279a8c4`; `PROOF_INTEGRITY.md` = `1adbbfbda644077de2b3bc547f66d807e692a828e8d2c963129cb2d02ea44dcf`; `MATHLIB_pr-review.md` = `8047365c41dfe5b756a319a4440781f708fd6aa25e08f4a0f31c685c81073f36`; `MATHLIB_style.md` = `e7bd0e9e7bae337fc6685cc9a533d4d221f7631dea182bbbaab3b12d5050ebd6`; `MATHLIB_naming.md` = `f12318e5c49c8dd15a6310d5f02433359727e2897257303be6820b32c906001a`; `MATHLIB_doc.md` = `0e077be542c2f6266b28e289ac3666a19ece8a25df52d03e42009457016b4d68`; `prose_style.md` = `80edb72d2728b3eea822863759456e06ca54e3b13f8ca4f13e2cd402166dfb97`.

VERDICT: APPROVED
