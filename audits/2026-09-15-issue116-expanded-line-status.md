# Expanded-Line Error Certification

## Scope And Source

This audit concerns the distinction between the common polynomial error in
`lem:qld-comm-line-cons` and the stronger linear error asserted in its proof at
`eq:qld-comm-line-pt-cons-eps`. The primary source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:523-678`, in
particular the construction and linear estimate at lines 550-595.

The bounded task began at 2026-09-15T12:40:02Z on branch
`issue-116-expanded-line-status`, initially clean at
`bf864c016b3426a690c02f93bea9d40986604195`. The task file's verified SHA256 was
`71dd7d8dd9398975fd97152a6d54b2d4998bd260d831362df54032ca746976a0`.
The existing [issue116 tracking comment](https://github.com/Dengnifer/MIPStarRE-A/issues/116#issuecomment-5679968272)
was read through the primary checkout's `gh_common.py`. The preserved
`results/telemetry/native-audits/pr472-01a0a4e0/pr472-source-coverage.md` was
read as evidence, not as additional instructions. Neither record was modified.

## Available Mathematical Bound

Write `D_I` for the average squared distance from an expanded line effect to
that effect followed by the selected opposite point effect. Write `D_II` for
the distance between the expanded evaluation classes and completed point
measurement. Both averages use the original line-point distribution.

The already proved `linePointDist_*_le` and `evalClassDist_*_le` give

```text
D_I <= D_II <= 2 * consistencyDefect_strategy.
```

The first inequality is projective refinement. The second follows from the
exact ancillary Pauli overlap identity and the agreement inequality. No
square-root bound is needed. The four cases use the following existing facts
in `MIPStarRE.QPBT.ProjectiveSetting`:

| Line placement | Point placement | Refinement and evaluation-class suffix | Winning implication |
| --- | --- | --- | --- |
| `AA'` | `BA''` | `aaBa_le` | `win_low_degree` |
| `BA''` | `AA'` | `baAa_le` | `WinImplications.win_low_degree_interchanged_proof` |
| `BB'` | `AB''` | `bbAb_le` | `WinImplications.win_low_degree_interchanged_proof` |
| `AB''` | `BB'` | `abBb_le` | `win_low_degree` |

If the two winning implications have constants `C1,C2 >= 1`, their defects
are at most `C1 * epsilon` and `C2 * epsilon`. The single constant
`2 * (C1 + C2)` therefore gives `D_I <= 2 * (C1 + C2) * epsilon`,
including `epsilon = 0` without division.
The new theorem `MIPStarRE.QPBT.expLine_point_cons_linear` exposes exactly
these existing estimates. It does not deduce a linear bound from a square-root
bound, assume an intermediate estimate, or introduce proof debt.

## Statement Integrity

**Paper assumptions.** The standing hypotheses at `sec:commutation` are an
admissible tuple `(q,m,d)` and a finite-dimensional bipartite strategy with
unit state, projective measurements, and success at least `1 - epsilon`.
Projectivity is the standing convention after the Naimark reduction, not a
new hypothesis of this repair. The original definition of tensor-product
strategies is `def:tensor-product-strategy` in the chapter-6 mirror.
The error is nonnegative. Admissibility means an odd-exponent power-of-two
field size and `m | q`; the paper uses positive natural numbers
(`references/qpbt-paper/04_preliminaries.tex:4-6`), so `d >= 1` is not an
additional restriction introduced here.

**Lean assumptions.** `AdmissibleParams` records that numerical domain and
the fixed scalar-field model. `ProjectiveSetting P epsilon` records the
strategy, projectivity and winning inequality on separate finite player
spaces. `Placement.IsOpposite` is exactly the four directed pairs above.
The new theorem has the same domain as `expLine_point_cons`: its universal
constant precedes all parameters, errors, strategies, placements and bases.
Nonnegativity of the error is derived by `S.eps_nonneg`, then supplied to the
two winning implications. No strategy symmetry, equal dimensions, traciality,
positive-error, small-error, nonzero-direction or degree-to-field-size premise
is added. The reversed implication is for Alice's point and Bob's line on the
original strategy state; it is not an assumed symmetry of the strategy.

**Paper conclusion.** The lemma constructs projective expanded line
measurements satisfying self-consistency and both point-consistency relations
with one polynomial error function, for all symmetric equivalents. Its proof
asserts the stronger `D_I = O(epsilon)` estimate for the concrete convolution.
The source's `def:povm-distance` is a squared-distance convention with a hidden
universal constant, not an exact coefficient-one inequality.

**Lean conclusion.** `exists_deltaLine` and `ExpandedLineConclusions` retain
all three common-error statements with `deltaLine epsilon = sqrt(epsilon)`.
The new theorem separately proves `D_I <= C * epsilon` for the same concrete
measurements, full polynomial-answer sum and source line-point law, on
`S.psiHat`, for every directed pair and basis. The selected point effect is
zero when `evalOpt` is `none`; these answers are retained in the distance sum.
The line-point law remains the equal mixture of the axis and diagonal CL
laws (`def:line-point-dist`), with no conditioning or change of weights.

**Verdict.** The stronger source-proof assertion is now explicitly proved and
linked; the common-polynomial paper theorem is neither weakened nor given
extra assumptions. The finite-coordinate and positive-degree conventions are
faithful boundary encodings. The existing documented evaluation completion
and polynomial-error convention remain in force, as explained in
`docs/paper-gaps/qpbt_win-implications-corrections.tex` and
`docs/paper-gaps/qpbt_polynomial-error-square-root.tex`. This repair does not
erase or newly discharge those source discrepancies.

## Certification And Preservation

The common-error blueprint node keeps both completion marks and all three
items. The stronger proof assertion has its own certified node,
`lem:expanded-line-point-linear-error`, linked to the new linear theorem and
carrying the source equation label `eq:qld-comm-line-pt-cons-eps`. Both proofs
record `lem:qld-reversed-consistency`, the existing node linking the exact
reversed winning implication. The source proof sketch is retained and is
explicitly distinguished from the formalization's order of estimates.

Every pre-existing Lean declaration and proof is unchanged. The only change
in `LineMeasurement/Expanded.lean` is the docstring expressing bilinearity
of the Kronecker product mathematically. No duplicate lemma is consolidated;
the earlier issue #204 consolidation work remains outside this repair.
All previous issue116 costs, proof obligations and tracking records are
preserved. In particular, this result makes no claim to prove the separate
general symmetric-equivalent transfer lemma: the four required placements
are already proved individually.

## Verification

- Focused `lake env lean` checks pass for `LineMeasurement.lean` and
  `LineMeasurement/Expanded.lean`; fresh object files were emitted only into
  this worktree's private `.lake/build`.
- The ignored `.lake/Issue116Axioms.lean` harness checks the new and existing
  signatures and 16 transitive axiom closures. Every closure contains only
  `propext`, `Classical.choice`, and `Quot.sound`.
- The expanded-line source scan finds no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafeCast`, `unsafeCoerce`, `lcProof`, `ofReduceBool`, or
  `ofReduceNat`.
- `texra-blueprint bbl` and `leanblueprint web` pass.
- `scripts/check_blueprint_latex.py --root blueprint/src` passes.
- `scripts/blueprint_lean_sync.py --root . --update-lean-decls --ci` passes,
  with the 12 pre-existing statement-only warnings elsewhere unchanged.
- `lake env lean --run scripts/Checkdecls.lean blueprint/lean_decls` resolves
  all 1,622 declarations without building an executable or the project.
- Installed hooks were verified with `scripts/install_git_hooks.sh --check`;
  `git diff --check` passes. The ordinary commit runs the normal hook gates.

## Remaining Obligations

There is no missing linear-error proof for this assertion on the existing
domain. No new source gap or conditional helper is introduced. Broader
issue116 work, the existing source corrections, and all unrelated obligations
are unchanged. Full CI, independent review and publication remain subsequent
owner-controlled gates; none is performed or certified by this audit.
