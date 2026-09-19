# Independent Review - PR 493 @ 57c75f541dd24a69ea8f08eb4a2c5946f4d08b5d

Fresh substantive review of the unique current-main-relative patch: the new
`NondegeneratePastingResampling` module and its `Lines.lean` re-export. I did not
review unrelated files inherited through the branch's merge history.

## Findings

- [x] F1 (resolved) `-` - Review 5254383928's only finding was stale red CI and
  main integration at `bd36ff5d`. At this exact head, the PR base is `main`, the
  branch is mergeable, and the exact-head manifest plus all nine published
  `local-ci/*` contexts are green. That review supplied no substantive proof
  approval, so none was carried here.
- [x] F2 (verified) `MIPStarRE/QPBT/Combining/Lines/NondegeneratePastingResampling.lean:49`
  - No open substantive finding. The theorem proves the stated exact law for
  every real-valued test function, without an invariance, bridge, residual, or
  conclusion-shaped hypothesis.

## Paper And Lean Statement Integrity Audit

The cited source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`:
line 955 invokes Schwartz-Zippel after instantiating the pasting lemma. The
underlying line-point law is `def:line-point-dist` at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:276-287`.
The paper does not state a separate conditioned-resampling theorem. The Lean
declaration is therefore correctly presented as a formalization-only auxiliary,
not as `lem:qld-xz-lines` itself.

- Paper assumptions: low-degree parameters, two independent line-point samples,
  and the uniform point-on-line sampling used in the Schwartz-Zippel step.
- Lean assumptions: only `L : LdParams` and an arbitrary scalar test function
  `value`. Positivity is internal to the already-defined conditioned law; there
  is no added mathematical or proof-obligation hypothesis.
- Paper use/conclusion: the sampled point on the relevant line may be treated as
  a fresh uniform affine parameter when applying Schwartz-Zippel.
- Lean conclusion: an exact equality of averages under
  `nondegenerateLinePastingDist L`, universally quantified over `value`, after
  independently resampling the first/X line's point while retaining its line
  descriptor.
- Verdict: faithful formalization-only support, with exact hypotheses and a
  stronger extensional formulation of the needed sampling fact. It neither
  weakens nor conditionally restates a paper-labelled theorem.

The tuple normalization is correct. By
`NondegeneratePastingDistribution.lean:39-42`, a product sample
`(first, second)` is relabelled as `(((first.line, second.line), second), first)`.
Thus `sample.2` is precisely the first/X line-point sample and `sample.2.1` is
its descriptor. The right side keeps that descriptor and replaces only its
point by `base + param * direction`. The conditioning event depends only on the
same retained descriptor's nonzero direction, so resampling preserves it.

The proof is substantive rather than headline matching. The private helper
derives normalized restriction from `avgOver_restrict_mul_mass`; after both
sides are expanded, `congr 1` removes only the syntactically identical positive
retained-mass denominator. The remaining numerator identity applies
`avgOver_linePointDist_resample_parameter` to the indicator-weighted test
function and then uses finite Fubini (`avgOver_comm`) to exchange the fresh
parameter with the independent second-line sample. The zero-direction branch
is discharged as a zero average, not used to prove the nondegenerate case.
No anti-pattern A1-A6 applies.

The existing blueprint prose is truthful: `thm:line-parameter-resampling` and
`cor:line-point-parameter-resampling` explicitly call the unconditional facts
auxiliary, while `def:nondegenerate-line-pasting-dist` explicitly calls the
conditioned law proof-only and records restoration to the unconditioned source
law. The new declaration's docstring makes the same scope distinction, so a
new paper-facing `\leanok` node is not warranted. The later
`nondegenerateLinePastingDist_collision_bound` on `main` is an upper bound for a
specific collision predicate; it does not supersede this exact equality for all
test functions.

## Verification And Limits

- Confirmed clean worktree and exact local head
  `57c75f541dd24a69ea8f08eb4a2c5946f4d08b5d`.
- `lake env lean MIPStarRE/QPBT/Combining/Lines/NondegeneratePastingResampling.lean`
  exited 0 with no diagnostics.
- The changed file has no `sorry`, `admit`, `axiom`, forbidden kernel bypass,
  placeholder tactic, debug command, or over-100-character line; `git diff
  --check` is clean.
- A focused `#print axioms` probe reports only `propext`, `Classical.choice`, and
  `Quot.sound` for the new theorem and its two load-bearing dependencies.
- Exact-head CI manifest: full build passed in 22 seconds; blueprint sync,
  proof-debt, proof-evasion, file-length, and paper-gap gates passed; the two
  inapplicable gates were explicitly skipped. `local-ci/summary` is success.
- I did not rerun full CI or a second full build, modify source files, or assess
  unrelated current-main changes. Source gaps #524, #598, and #527 are outside
  this patch and unchanged.

VERDICT: APPROVED (code=APPROVED, prose=APPROVED)
