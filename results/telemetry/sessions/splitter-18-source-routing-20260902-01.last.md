## Routing Result
Audited at exact HEAD `b5da371de32dbaf487d140e389be1d8d317709a4`. No files were edited and no commit was created.
### Attachment Slices
All slices are inclusive, below 600 lines, and balanced for theorem, lemma, definition, claim, remark, and proof environments.
| ID | File and slice | Lines | Contents |
|---|---|---:|---|
| P1 | [paper 680-881](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:680) | 202 | Combining intro, `qld-4-10`, linearity theorem, point proof |
| P2 | [paper 882-1019](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:882) | 138 | Combined lines, combining map, `qld-4-12` |
| P3 | [paper 1020-1264](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020) | 245 | `qld-4-13`, restricted laws, sub-lines, claims, proof |
| P4 | [paper 1265-1414](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1265) | 150 | `qld-4-7` statement and proof |
| B1 | [blueprint 1-342](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/blueprint/src/chapter/ch15_qpbt_combining.tex:1) | 342 | Chapter context, linearity, combined points |
| B2 | [blueprint 343-646](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/blueprint/src/chapter/ch15_qpbt_combining.tex:343) | 304 | Combined lines through restricted-line estimates |
| B3 | [blueprint 647-1126](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/blueprint/src/chapter/ch15_qpbt_combining.tex:647) | 480 | Sub-lines, claims, `qld-4-13` proof and defect remark |
| B4 | [blueprint 1127-1308](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/blueprint/src/chapter/ch15_qpbt_combining.tex:1127) | 182 | Global pair measurement and final remarks |
## Label Map
Ranges include the associated proof where one occurs. Semicolon-separated ranges are intentionally noncontiguous.
| Chapter-15 label | Paper slice | Blueprint slice |
|---|---|---|
| `chap:qpbt-combining` | 680-1414; no paper chapter label | 1-1308 |
| `sec:combining` | 680-967 | 8-426 |
| `thm:linearity` | 713-725 | 98-144 |
| `rem:linearity-import` | evidence 713-725; no paper remark | 146-189 |
| `lem:qld-4-10` | 689-709; 729-879 | 191-341 |
| `lem:qld-xz-lines` | 882-965 | 345-425 |
| `sec:apply-ldt` | 968-1414 | 427-1308 |
| `def:combine-map` | unlabeled prose 978-987 | 445-475 |
| `lem:qld-4-12` | 993-1018 | 477-529 |
| `lem:qld-4-13` | 1020-1034; 1118-1264 | 531-570; 1032-1097 |
| `def:ith-restricted-line` | 1038-1048 | 578-592 |
| `lem:restricted-line-mixture-bounds` | unlabeled prose 1049-1061 | 594-645 |
| `lem:qld-sublines` | 1063-1116 | 647-840 |
| `rem:qld-sublines-property-three` | evidence 1063-1069; 1132 | 842-850 |
| `lem:claim-17-1` | `claim:17-1`, 1140-1166 | 860-905 |
| `lem:claim-17-2` | `claim:17-2`, 1168-1202 | 907-972 |
| `lem:claim-17-3` | `claim:17-3`, 1204-1239 | 974-1030 |
| `rem:qld-4-13-source-defects` | evidence 1134-1138; 1183-1201; 1221-1246 | 1099-1126 |
| `lem:qld-4-7` | 1267-1413 | 1133-1255 |
| `rem:qld-4-7-divisibility` | evidence 1071-1075; 1277-1288 | 1259-1293 |
| `rem:qld-4-7-constants` | evidence 1267-1268; 1287-1288; 1402 | 1295-1308 |
Equation labels map as follows:
| Labels | Paper | Blueprint |
|---|---:|---:|
| `eq:qld-q-self-cons` | 694-697 | 203-208 |
| `eq:qld-q-cons-m-hat-xz`, `eq:qld-q-cons-m-hat-zx` | 700-705 | 211-223 |
| `eq:combine-lines` | 985-987 | 465-471 |
| `eq:qld-4-12-self-cons` | 997-1000 | 490-495 |
| `eq:qld-4-12-cons-m-hat`, `eq:qld-4-12-cons-m-hat2` | 1002-1007 | 498-513 |
| `eq:qld-4-13` | 1028-1032 | 553-567 |
| `eq:qld-xz-lines-restricted` | 1059-1061 | 616-628 |
| `eq:qld-combined-lines-consistency` | 1135-1137 | 1061-1072 |
| `eq:qld-s-point-con-alice`, `eq:qld-s-point-con-bob` | 1269-1272 | 1153-1166 |
## Existing Lean Inputs
The declarations presently available to the proposed targets are:
| Target | Existing declarations at HEAD |
|---|---|
| `Games/ErrorFunctions` | No project-specific prerequisite beyond Mathlib real arithmetic |
| `Games/DistributionAux` | `Distribution`, `Distribution.IsProbability`, `Distribution.map`, `avgOver`, `uniformDistribution`, `Distribution.uniformOnFinset` |
| `Games/Consistency` | `Distribution`, `avgOver`, `Quantum.Op`, `applyOperatorToState`, `opFamilyDistSq` |
| `Test/LinePointDist` | `LdParams`, `ScalarQ`, `LdSpace.point`, `.seed`, `.direction`, `chiIndex`, `prefixProjection`, `ldPointCL`, `ldALineCL`, `ldDLineCL`, `clDistribution`, `Distribution.map`, `linePoints`, `lineRepMap` |
| `Combining/Defs` | `AdmissibleParams`, `AdmissibleParams.toLdParams`, `PauliScalar`, `polyFunc`, `linePoints`, Mathlib `MvPolynomial`/`Polynomial` |
| `Combining/Linearity` | `Quantum.Op`, `heteroKron`, `applyOperatorToState`; Mathlib matrix trace, adjoint, PSD |
| `Combining/Witnesses` | `Measurement`, `Measurement.postprocess`, `Measurement.IsProjective`, `opFamilyDistSq`, `uniformDistribution`, `AdmissibleParams`, `PauliScalar`, `PauliRegister`, `PauliKind`, `polyFunc` |
| `Combining/Points` | Witness API plus `Measurement.postprocess` |
| `Combining/Lines` | Witness/Defs API plus `avgOver`, `linePoints`, `IsAxisParallel` |
| `Combining/Claims` | Witness/Lines API plus `avgOver`, `applyOperatorToState` |
| `Combining/Apply` | Witness/Defs API plus `Measurement`, `Measurement.postprocess`, `polyFunc`, `ldGame`, `deltaQld` |
| `Test/Soundness` append | `deltaQld` |
These are defined primarily in [Distribution.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/MIPStarRE/LDT/Basic/Distribution.lean:23), [Measurement.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/MIPStarRE/Quantum/Measurement.lean:45), [Games/Defs.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/MIPStarRE/QPBT/Games/Defs.lean:79), [LowDegreeGame.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/MIPStarRE/QPBT/Test/LowDegreeGame.lean:37), and [Lines.lean](/home/drx/MIPStarRE-qpbt/.worktrees/issue-0018-qpbt-combining-skeleton/MIPStarRE/QPBT/Algebra/Lines.lean:29).
## Missing Prerequisites
Both `issue-0016-qpbt-residual-skeleton` and `issue-0017-qpbt-observables-skeleton` still point to `b5da371`; neither contributes a commit at this HEAD.
Issue 16 prerequisites absent:
- `IsPolyErr`, `IsPolyErr₂`, `consistencyDefect`, `IsConsistentWithin`, `opDistSq`
- `Strategy.IsProjective`
- `Distribution.mix`; there is also no general `Distribution.prod` or `Distribution.restrict`
- Proof-provider API: agreement/add-projector/data-processing lemmas, `pastedMeasurement`, `exists_pasting_error`, `deltaLd`, and `exists_ld_soundness`
Issue 17 prerequisites absent:
- `LineKind`, `LineDesc`, `DegPoly`, `degPolyEval`, `DegPoly.padTo`, `EvaluatesTo`, `evalOpt`
- Dimension-generic `aLinePointDist`, `dLinePointDist`, `linePointDist`
- `ProjectiveSetting`, `SixReg`, `Placement`
- `ProjectiveSetting.psiHat`, `.place`, `.pointMeasExp`, `.expPointTrace`, `.lineMeasExp`, `.expLineOp`
- `deltaAnticom`, `deltaLine`, and the chapter-14 consistency theorem interfaces
The verified issue-17 contract names the ambient bundle `ProjectiveSetting`, not `ExpandedSetting`, and exposes `deltaLine ε` as a top-level function, not `S.deltaLine`.
## Attach-With
- `Linearity`, `Points`: P1 + B1
- `Lines`: P1 + P2 + B1 + B2
- `Defs`: P2 + P3 + B2
- `Claims`: P3 + B3
- `Apply`: P3 + P4 + B2 + B3 + B4
- `Witnesses`: P1 + P2 + P3 + P4 + B1 + B2 + B3 + B4
- Upstream distribution/line-point reconciliation: P2 + P3 + B2
- Every downstream Lean session additionally needs the implemented issue-16 and issue-17 modules listed above.
## Verification
Environment counts were balanced independently for all eight slices. The worktree remained clean. No TeX or Lean build was run because this was a read-only routing audit with no source changes.
