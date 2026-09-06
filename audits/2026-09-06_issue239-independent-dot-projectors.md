# Issue #239: independent Pauli dot-product projectors

## Scope and source

Starting revision: `a61ee557b33a2d8a4721e92b08b6d06dcb69ed57`.
This packet proves `MIPStarRE.QPBT.tauDotProj_isProj` and
`MIPStarRE.QPBT.sum_tauDotProj_eq_one` in
`MIPStarRE/QPBT/Extraction/Defs.lean`. Their signatures, the definitions
`tauDotProj` and `bracketOp`, and the imports are unchanged.

The source is Equation `eq:def-tauwu` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429`.
The corresponding blueprint entries are `def:tau-dot-product-projector` and
`lem:tau-dot-product-projective`. The latter already contains both Lean links
and its completion tag, so no blueprint edit is needed.

## Mathematical argument

Fix a basis kind $W$, a vector $u\in\mathbb F_q^M$, and an outcome
$a\in\mathbb F_q$. Write $v_h$ for the Pauli basis vector with label $h$.
The existing definition of the fine-grained operator is
$\tau_h^W=v_hv_h^*$, and `sum_pauliProj_eq_one` proves
$\sum_h v_hv_h^*=I$.

Let $U$ be the square matrix whose column indexed by $h$ is $v_h$.
Completeness gives $UU^*=I$. For a square matrix over $\mathbb C$, a right
inverse is also a left inverse; consequently $U^*U=I$, so the columns are
orthonormal. Mathlib's `Matrix.mem_unitaryGroup_iff` supplies precisely this
finite-dimensional implication. This recovers the orthogonality needed here
from the already-proved completeness identity, without requiring a separate
Pauli-projectivity theorem or repeating the Fourier calculation.

Let $D$ be diagonal, with entry $1$ at $h$ when $h\cdot u=a$ and entry $0$
otherwise. Then $D^2=D=D^*$, and entrywise expansion gives
$\tau_a^W(u)=UDU^*$. Unitary conjugation preserves multiplication and adjoints;
the proof applies `IsStarProjection.map` to `Unitary.conjStarAlgAut`.
This proves projectivity, including empty fibers and $u=0$.

For completeness, the fibers of $h\mapsto h\cdot u$ partition the finite
outcome set. `Finset.sum_fiberwise` therefore identifies
$\sum_a\tau_a^W(u)$ with $\sum_h\tau_h^W=I$.

## Statement integrity

- **Paper assumptions:** the fixed admissible QPBT parameters and their finite
  field; $W\in\{X,Z\}$, $u\in\mathbb F_q^M$, and, for projectivity,
  $a\in\mathbb F_q$. No nonzero-vector condition is imposed.
- **Lean assumptions:** the unchanged `{P : AdmissibleParams}`,
  `(W : PauliKind)`, `(u : PauliRegister P)`, and, for projectivity,
  `(a : PauliScalar P)`. The existing parameter model supplies the finite-field
  and finite-index instances. There is no strategy or `GlobalPairWitness` input.
- **Paper conclusion:** each dot-product coarse-graining is a projector, and
  their sum over all scalar outcomes is the identity.
- **Lean conclusion:** `IsProj (tauDotProj W u a)` and
  `∑ a : PauliScalar P, tauDotProj W u a = 1`, respectively.
- **Verdict:** faithful boundary hypotheses. Within the existing admissible
  parameter domain the conclusions and quantifiers are exact. No public header,
  error parameter, definition, or hypothesis is changed.

The A1–A6 checks introduce no additional proof assumptions, alternative
definitions, default witnesses, or external-result inputs. The diagonal
indicator records the actual fiber, not a fallback for an unstated precondition.

## Validation and axiom dependencies

- `lake env lean MIPStarRE/QPBT/Extraction/Defs.lean`: passes without warnings.
- `rg -n "sorry|axiom" MIPStarRE/QPBT/Extraction/Defs.lean`: no output; the file's
  two previous proof holes are removed. The extended bypass/debug-token scan
  also has no matches.
- `check_source_statement_changes.py`, against the starting revision and
  restricted to the edited Lean file: no changed public headers.
- The installed normal pre-commit checks pass; `git diff --check` is clean.
- Both targets, and their input `sum_pauliProj_eq_one`, have exactly the axiom
  closure `[propext, Classical.choice, Quot.sound]`. A private `Lean.collectAxioms`
  check rejects any other axiom for either target. In particular, neither proof
  depends on `sorryAx`. These are checks of the actual transitive proof
  dependencies, not an inference from whether other imported declarations are
  finished. The definition `tauDotProj` has the same standard axiom closure.

The copied `Algebra/Pauli.olean` initially lacked the existing source declaration
`sum_pauliProj_eq_one`. Rechecking the unchanged `Algebra/Pauli.lean` with output
under this worktree's private `.lake/build/lib/lean/` resolved that artifact
mismatch. The edited `Extraction/Defs.lean` was likewise compiled there before
the axiom check. No shared cache was written and no `lake update` was run.
Scratch checks and logs are under
`~/.cache/mipstarre-dev/sessions/prover-239-20260906-01/`.

The optional repository-wide blueprint synchronization check reports 1,387
references missing from `blueprint/lean_decls`, and no references missing from
Lean. Both the blueprint sources and that declaration list are unchanged from
the starting revision; this packet adds no declarations. The unrelated list
mismatch is not repaired here. The report also records 19 existing
statement/proof completion-tag warnings, none for the dot-product projector
lemma. The JSON and full output are retained with the private logs.

No full `lake build` is needed for these proof-only changes: imports and public
signatures are unchanged. No CI, independent review, publication, or merge was
run in this session.

## Remaining obligations and handoff

No proof obligation remains in the edited file. Neither target requires issue
#119's global-pair construction, and this packet constructs no global witness.
It supplies only these two targets of #120; that issue's other extraction
obligations and its #119 dependency are unchanged. Independent review and the
normal publication gates remain necessary. The principal proof step to inspect
is the identification of the filtered sum with $UDU^*$.
