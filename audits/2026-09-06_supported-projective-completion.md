# Supported Projective Completion

Issue #279; session `prover-279-20260906-01`.

## Mathematical Statement

Let `(P_a)` be a complete finite projective measurement, let `G` be a
nonempty subset of its outcomes, and specify `a_0` in `G`. Put

\[
 R=\sum_{a\notin G}P_a=I-\sum_{a\in G}P_a.
\]

The construction in `MIPStarRE/QPBT/Games/SupportedCompletion.lean` has
outcomes in the subtype `G` and effects

\[
 C_a=P_a+\mathbf{1}_{a=a_0}R.
\]

`complete` is the postprocessing of `P` that retains good outcomes and sends
bad outcomes to `a_0`. Its type includes positivity and completeness.
`complete_effect` proves the displayed effect formula,
`badEffect_eq_one_sub` identifies the complementary effect,
`badEffect_isStarProjection` proves that it is a projection, and
`complete_isProjective` proves projectivity of `C`.

Let `N_x` be any complete measurement on the other player space, let `mu` be
a probability distribution on questions, and let `psi` be any state vector.
No equality of the two player spaces or normalization of `psi` is assumed.
Write `D` for the QPBT `consistencyDefect`, with the completed measurement
as its first argument. For question-dependent outcome maps `f_x` on all
outcomes and `g_x` on good outcomes, agreeing on `G`, the new theorems give

\[
 |D(C^{g},N)-D(P^{f},N)|\leq\langle\psi,(R\otimes I)\psi\rangle
\]

in the Alice-first orientation. In the Bob-first orientation the bound is
`<psi, (I tensor R) psi>`, and the completed measurement is still the first
consistency argument. These are `abs_complete_consistency_left_sub_le` and
`abs_complete_consistency_right_sub_le`. The intermediate
`abs_postprocess_consistency_left_sub_le` and its right counterpart prove
the same bound for any two full outcome maps agreeing on `G`.

For the actual restricted submeasurement `P|G`, the direct source-step
estimates are `complete_restrict_consistency_left_le` and
`complete_restrict_consistency_right_le`:

\[
 D(C^g,N)\leq D((P|G)^g,N)+\langle\psi,(R\otimes I)\psi\rangle,
\]

with `I tensor R` in the other orientation. The proof identifies the added
defect with the average of
`<psi, (R tensor (I - N_x[g_x(a_0)])) psi>`. Positivity of the subtracted
overlap gives the coefficient 1. The consistency bounds themselves hold
for complete POVMs; projectivity is needed only for the projection claims.

## Existing API

The search covered `LDT/Preliminaries/Completion.lean`,
`Quantum/Measurement.lean`, and the QPBT consistency and postprocessing APIs.
`completeAtOutcomeProj` already proves projectivity of completing an LDT
projective submeasurement. The present construction instead uses
`Quantum.Measurement.postprocess` and
`SandwichProduct.postprocess_isProjective` directly on the QPBT measurement
type. No second proof of projective completion is introduced.

The existing
`LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le` gives
a related heterogeneous, right-completion bound for the density-state/LDT
API. It does not give the absolute comparison between arbitrary outcome
maps agreeing on the good set. The new adapter supplies that comparison
and the direct restriction comparison in the QPBT vector-state API, with
both orientations and question-dependent postprocessing explicit.

## Source And Remaining Obligation

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
lines 1364-1402, especially `eq:qld-g-non-separable`,
`eq:qld-sgg-completeness`, and the completion paragraph after
`eq:qld-sgg-mhat-sandwich`. Blueprint `lem:qld-4-7` remains a separate,
unfinished source theorem. No blueprint tag or shared import was changed.

For its eventual application, take `G` to be the image of the polynomial
combining map, and identify its subtype with polynomial pairs using the
injectivity of that map. Choose the image of the zero polynomial pair as
`a_0`. Transport `complete` to the pair alphabet by that identification;
postprocessing preserves projectivity. For basis `W` and question `u`, take
`g_u` to be `evalAt W u` after the identification, and take `N_u` to be
the opposite player's expanded point measurement, or the joint sandwich
measurement before taking its point marginal. The two estimates retain the
first-argument order of `GlobalPairWitness.point_consistent_alice` and
`GlobalPairWitness.point_consistent_bob`. Applying them to `S.place` also
requires the register permutations and spectator identities of that interface;
no source-specific six-register transport is asserted in this auxiliary.

The named, **unimplemented** proof target `global_polynomial_bad_mass_le`
is to derive, for the projective polynomial measurement produced by the
preceding low-degree argument,

\[
 \sum_{g\notin\mathcal G}\|\hat S_g\hat\psi\|^2
 \leq C(\delta_{\mathrm{ld}}+\delta_Q+md/q)
\]

for a universal constant `C`, from the source hypotheses and preceding
estimates. Both player placements are required. This name denotes a target
specified here, not a Lean declaration with an unproved body. Issue #279
separates this estimate from the completion adapter. The existing
`exists_globalPairWitness` proof remains open in `Combining/Apply.lean`;
its other recorded source-import obligations remain in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`. No generic assumptions
bundle or additional hypothesis was added to that source theorem.

## Statement Integrity

| Item | Paper completion step | Lean auxiliary |
| --- | --- | --- |
| Input | Projective measurement restricted to a good set | Complete finite measurement, explicit good predicate, actual good default |
| Projectivity | Orthogonal complementary projection is added to one effect | Constructed postprocessing; existing postprocessing-projectivity theorem |
| Consistency | Increase bounded by omitted state mass | Coefficient-1 direct bound; absolute comparison for maps agreeing on good outcomes |
| Registers | Both heterogeneous player orientations | Explicit `iotaA`, `iotaB`; completed measurement first in both relations |
| Domain | Finite outcome averages | Finite types, decidability, probability distribution; arbitrary vector state |

Verdict: **faithful boundary hypotheses** for the isolated auxiliary.
The supplied good default enforces the nonemptiness needed by the paper's
choice of an arbitrary retained effect. The absolute comparison and absence
of a state-normalization requirement are proved auxiliary generalizations.
This is not a formalization of the entire source lemma. No paper-labelled
public theorem was modified, and no source theorem was marked complete.

The A1-A6 integrity check found no conclusion-shaped hypothesis, unrelated
witness, hidden precondition, duplicate projectivity proof, or ungrounded
external statement. The default branch is exactly the specified completion
operation and is accounted for by the bad-effect mass.

## Validation Checkpoint

- Lean/Mathlib: `v4.32.0`, as specified by this checkout's toolchain files.
- `lake env lean MIPStarRE/QPBT/Games/SupportedCompletion.lean`: passed,
  no warnings.
- The file scan for `sorry|axiom` and all forbidden proof-integrity/debug
  tokens returned no matches.
- A compiled-module `Lean.collectAxioms` check covered all 26 exported
  namespace declarations, including generated declarations. Every axiom
  dependency belongs to `propext`, `Classical.choice`, `Quot.sound`.
- No line exceeds 100 characters.
- Hook installation command
  `/home/drx/MIPStarRE-qpbt/scripts/install_git_hooks.sh` was refused:
  `could not lock config file /home/drx/MIPStarRE-qpbt/.git/config: Read-only file system`.
  The separate normal `--check` passed with `core.hooksPath=.githooks`.

The validated mathematical checkpoint was reached before 10:22 UTC, within
the 2400-second session bound starting at 10:00:08 UTC. Provider token usage
is not exposed to this session; the dispatcher owns the usage telemetry.
This independent auxiliary is not a reset of the B8 correction budget.

## Publication Blocker

The exact staging action was refused with exit 128:

```sh
git add MIPStarRE/QPBT/Games/SupportedCompletion.lean \
  audits/2026-09-06_supported-projective-completion.md
```

Git reported that it could not create
`/home/drx/MIPStarRE-qpbt/.git/worktrees/issue-279-projective-completion/index.lock`:
`Read-only file system`. This session's approval policy is `never`; no
supported elevation is available. No alternate Git index, checkout, hook
bypass, or publication route was used.

The two files remain untracked on `issue-279-projective-completion`, based
at `ba299326ebde0d9f94fc9b4e9b557ce776e8f1cf`. No commit or PR was created,
so checked publication and exact-head CI could not proceed. No full build
was run: the module was validated directly, shared imports were not changed,
and no unlocked full build was attempted. Main must stage and commit these
files with the normal hooks, publish through the primary checkout's
`pr_open.py`/`checked-push.sh`, and run `ci.sh` for that exact published head.
Suggested commit subject:
`feat(QPBT/Games): Add supported projective completion`.
Independent review and merging remain main's responsibility.

Final validation checkpoint: **2026-09-06 10:26:59 UTC**, 1611 seconds after
the dispatched start, with 789 seconds remaining in the 2400-second bound.
The final source passed the single-file check without warnings, and its
freshly compiled module again passed the 26-declaration axiom-closure check.
Provider token totals remain unavailable to this session; no estimate is
substituted for the dispatcher's measured usage.
