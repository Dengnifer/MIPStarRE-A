# Stage 4.3 launch plan — 2026-09-04 (owner session, Fable 5.1 planning subagent)

Snapshot: main `26bf8d8`. Packets not yet started: #66, #69, #70, #71, #73, #74, #76, #77.

## Launch list

START NOW
- #66 self-dual coordinate identities — `Algebra/SelfDualBasisTheorems.lean` only; no prerequisites; no shared file (PR 90 leaves that file untouched). Unblocks #69 soonest.
- #73 orthogonal-complement identities — `Algebra/SubspacesTheorems.lean`; targets 1–2 free, target 3 + axiom audit after PR 80 (#72) merges.

AFTER PR MERGES
- #70 binary-coordinate multiplication — after PR 90 (#65): shares `Algebra/SelfDualBasis.lean`.
- #71 direct low-degree sampling geometry — after PR 82 (#67): owns `DirectLowDegree/Geometry.lean` (created by PR 82).
- #74 direct low-degree rejection calculus — after PR 82 (#67): new `DirectLowDegree/GameValue.lean`; NOTE nothing imports it, so `lake build` does not compile it — the worker must add the import to the `DirectLowDegree.lean` facade (operator exception).
- #76 perfect Magic Square strategy — after PR 87 (#75) and #64: owns `MagicSquareTheorems/PerfectStrategy.lean`.

AFTER ISSUE MERGES
- #69 qudit-to-qubit Pauli isometry — after #68 (shares `PauliTheorems.lean`), #64, #66. Issue body is truncated on GitHub (acceptance list incomplete) — complete it at launch.
- #77 Magic Square rigidity — after PR 87 (#75), PR 83 (#49), #64, #68; longest lane; concurrent with #76.

## Conflict matrix
#69↔#68 (`PauliTheorems.lean`); #70↔#65 (`SelfDualBasis.lean`); #71↔#67 (`Geometry.lean`); #76/#77↔#75 (`PerfectStrategy.lean` / `MagicSquareTheorems.lean`). #66, #73, #74 conflict with nothing.

## Findings that change the queue
1. **PR #46 (issue #19) gates PR #88 (#63).** PR 88 was built without PR 46: it re-adds `Algebra/Decoding.lean` (add/add conflict) and cites `docs/paper-gaps/qpbt_decoding-identity.tex`, which exists only on PR 46's branch (hence PR 88's paper-gaps CI failure). Nothing on PR 88 imports `Decoding.lean`, so its "build success" never compiled it. Order: merge PR 46 first, then rebase PR 88 taking the #63 (proved) version of `Decoding.lean`.
2. #64 and #68 have no PR yet (worktrees with local edits/commit), so #69/#76/#77 cannot be tied to PR numbers today.
3. #49 excludes two `DistanceTheorems.lean` lemmas "for separate packets" that are not filed; any such packet must follow PR 83. PR 83 also edits four files outside its stated ownership (`Combining/Points.lean`, `Combining/Witnesses.lean`, `Games/Sandwich.lean`, `Observables/WinImplications.lean`, +2/−1 each) — no collision with unstarted packets.
4. #47 names further lanes (projective rounding, conditional linearity, chapters 14–16) that are not filed yet.
