---
pr: 0003
kind: code
branch: issue-0006-qpbt-minimal-skeleton
base: main
merge_base: ec46d58b7497f349a5136232b80c0b49d7dbaa61
head_sha: db4327a7c8f6eb5e5dbd3dc234267bd76cabaa97
verdict: CHANGES_REQUESTED
review_state: CHANGES_REQUESTED
session: reviewer-pr0003-20260831-06
model: (dispatcher default)
generated: 2026-08-31T08:32:30Z
---

# Code review — PR 0003 @ db4327a7c8f6

Local replacement for the `code-review` job of `.github/workflows/pr-review.yml`.

## Findings

Checkbox states: `[ ]` unresolved (blocks the merge), `[x]` resolved,
`[-]` outdated (the cited lines were rewritten; does not block).

<!-- findings:begin -->
- [ ] F1 (blocker) `MIPStarRE/QPBT/Algebra/FieldBasis.lean:40` — `FixedFieldModel` does not encode the claimed self-dual normal basis.
- [ ] F2 (blocker) `MIPStarRE/QPBT/Algebra/Pauli.lean:90` — `tauObservable` is defined as the expansion it is supposed to prove.
- [ ] F3 (blocker) `MIPStarRE/QPBT/Games/CondLinear.lean:126` — CL concatenation selects `R u` instead of `R (L u)`.
- [ ] F4 (blocker) `MIPStarRE/QPBT/Games/CondLinear.lean:152` — `graphDistribution` silently maps an empty graph to a zero subprobability.
- [ ] F5 (blocker) `MIPStarRE/QPBT/Test/PauliBasisTest.lean:553` — Point/Pair consistency reads the Point-side content, erasing `γ` and `r_W`.
- [ ] F6 (blocker) `MIPStarRE/QPBT/Test/PauliBasisTest.lean:556` — Magic Square edges fall through to unconditional acceptance and self-loops are incorrectly gated.
- [ ] F7 (blocker) `MIPStarRE/QPBT/Test/Soundness.lean:209` — operator closeness uses the function-space supremum norm instead of the Hilbert `ℓ²` norm.
- [ ] F8 (blocker) `MIPStarRE/QPBT/Test/Soundness.lean:237` — `pauli_soundness` excludes the source theorem's `ε = 0` case.
- [ ] F9 (changes) `MIPStarRE/QPBT/Algebra/Pauli.lean:99` — `eprState` admits the empty carrier, where it is not a normalized state.
- [ ] F10 (changes) `MIPStarRE/QPBT/Test/LowDegreeGame.lean:198` — `ldEdges` is an unused, incomplete representation of the source type distribution.
- [ ] F11 (changes) `MIPStarRE/QPBT/Games/Distance.lean:35` — matrix action is duplicated instead of using one Euclidean-space helper.
- [ ] F12 (changes) `MIPStarRE/QPBT/Algebra/FieldBasis.lean:37` — algebra docstrings systematically cite later use-sites instead of the defining paper passages.
- [ ] F13 (changes) `MIPStarRE/QPBT/Test/LowDegreeGame.lean:20` — test-module paper citations repeatedly point to unrelated sections.
- [ ] F14 (changes) `MIPStarRE/QPBT/Games/Distance.lean:28` — the distance definitions cite the wrong source.
- [ ] F15 (changes) `MIPStarRE/QPBT/Algebra/Subspaces.lean:64` — several new private definitions lack the required docstrings.
- [ ] F16 (changes) `-` — the local PR record leaves Motivation, Description, Testing, and statement integrity blank.
- [ ] F17 (advisory) `-` — none of the new source-facing QPBT declarations has been linked from the blueprint.
<!-- findings:end -->

## Review

Changes are required. The local build is green, but eight semantic blockers mean the skeleton does not yet state the cited game and theorem faithfully.

F1: `binaryEquiv` is an arbitrary equivalence and `selfDualNormal : Prop` merely stores a proposition, not evidence about a stored basis. The source fixes a self-dual normal basis and derives coordinates and multiplication tables from it (`references/qpbt-paper/04_preliminaries.tex:669-724`; blueprint `ch11_qpbt_algebra.tex:298-315`). Either retain the brief’s deferred plain `FieldModel` encoding without claiming basis fidelity, or store an actual basis with its properties.

F2 is definitional sleight-of-hand: paper `04_preliminaries.tex:1141-1160` defines the multi-qudit observable independently as a tensor product, then proves its spectral expansion. Define `tauObservable` from `tauShift`/`tauPhase`; leave the expansion as the tracked proof obligation.

F3 makes `IsCondLinearOn.concat` false. Paper `05_conditionally_linear_functions.tex:282-292`, label `lem:cl-concat`, and blueprint lines 498-505 define the right component as `R_{L(u)}(v)`. Line 126 must use `R (L u) v`.

F4 violates `def:graph-distribution`: the normalization in paper `07_types.tex:65-82` is undefined for no edges, and blueprint lines 550-563 explicitly require nonemptiness. Carry `E.Nonempty` in the source-facing API, or separate and clearly name a raw total helper.

F5 must use `xB` in the Point/Pair-W orientation and `xA` in the reverse orientation. Paper lines 1208-1210 and blueprint line 362 compute both `γ` and `tr(a_w r_W)` from the Pair-side shared content.

F6 needs mixed `msTriple`/`bit` branches in both orientations. Those are the supported Constraint/Variable edges and must enforce paper lines 1212-1215. The same-type rule at lines 1173-1175 must separately require unconditional answer equality; it cannot be gated by `γ`.

F7 weakens `thm:pauli`: `Matrix.mulVec` returns a plain function, so the displayed norm is `ℓ∞`. Paper `06_nonlocal_games_and_mipstar.tex:258-270` requires the Hilbert norm. Apply the matrix through `Matrix.toEuclideanLin` or convert through `EuclideanSpace.equiv.symm`.

F8 is source-statement drift. Paper `thm:pauli` at `08:1433-1445` has no strict-positive premise, and the paper explicitly permits `ε ≥ 0` at `06:94-98`. Since `deltaQld` is defined at zero, `0 < ε` is not a necessary boundary hypothesis.

F9-F11 require API cleanup: restrict `eprState` to a nonempty carrier and expose normalization; delete or complete `ldEdges`; and use one shared `Matrix.toEuclideanLin`-based action helper.

F12-F14 require source-anchor correction. The relevant primary ranges are: field material `04:433-502,653-728`; subspaces `04:231-384`; low-degree encoding `04:832-897`; lines `08:102-174`; EPR/Pauli `04:946-955,1052-1161`; low-degree game `08:31-391`; Magic Square `08:512-610`; Pauli decider `08:1126-1225`; state/POVM distances `06:219-230,258-271`.

F15 covers `prefixMap`, `prefixRank`, `phaseSign`, `singlePauliVec`, `applyOperator`, `outcomeWeight`, and `applyOperatorToState`. In particular, `phaseSign` also appears in public theorem types despite being private.

F16: the PR record at `prs/0003-feat-qpbt-minimal-skeleton-thm-pauli-statement-and/pr.md:19` still contains only template comments. It must document the source comparison, deliberate encodings, and validation.

The 16 `sorry` sites are explicitly tracked by issue #0006 and its stage-4.1 brief (“with all proofs sorry”), so they are not separate findings. They do leave `pauli_soundness` with `sorryAx`; this PR supplies no completed formal proof. F17 is advisory because the PR lacks the enforcement label, although the issue brief explicitly calls for links for the 37 new source-facing nodes.

Statement-integrity verdict: `pauli_soundness` has an extra strict `ε` assumption, a weakened operator-distance conclusion, and quantifies over a game whose current win predicate differs from `def:pauli-win-predicate`. It is therefore not yet a faithful statement of paper `thm:pauli`.

## Verdict

VERDICT: CHANGES_REQUESTED
