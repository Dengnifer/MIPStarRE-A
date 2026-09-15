---
title: "Universal absorption of the actual rounded polynomial-pair error"
date: 2026-09-14
purpose: >
  Record the recovery of the established direct-line construction, the new
  eighth-root absorption, and the unchanged source theorem's final closure.
issue: "#513"
status: complete
start_head: d0ddff11ac5987a8cc4c1647a9dc3a8ac2d8003f
effort_requested: MAX
authorization: "Owner's explicit hard-mathematical-gap exception"
---

# Scope

The target is the original `exists_globalPairWitness`, with universal
constants before all admissible parameters, positive strategy errors, and
projective settings. No hypothesis, conclusion, or quantifier is changed.
The construction uses the actual rounded measurements from the preceding
retained-pair-completion audit. Their four consistency defects are capped
using completeness and normalization of those same measurements.

# Source of Truth

The full retained-pair-completion audit, prover persona, AGENTS.md, local
README and DESIGN, and the proof-evasion policy were read. The mathematical
sources are `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
`lem:qld-4-7` and its proof (1267--1404), `lem:qld-xz-lines` (882--963), and
the first extended-line construction (1020--1034, 1118--1246).

The full immutable PR549 application signature, section, and proof were
read at `aeaca3aee589ff666c5ab6feb2681e2cb06e8b1d`. Its established
constructor supplies both the point witness and the directly indexed
completed-answer line witness. It assumes neither a line constructor nor a
global witness. Its universal error functions precede every parameter and
strategy. The relevant dependency proofs were recovered with provenance.

# Findings

Write rho = md/q, Q = p(epsilon), and L = C m g(epsilon,rho), where p and g
are the polynomially bounded functions supplied by the recovered established
line constructor. Both Q and L occur in

$$
 v=3(\sqrt{Q+L}+\rho),\qquad
 \delta=\delta_{\rm ld}(a,b,v,q,2m+2,d,1).
$$

The already-proved pair construction has

$$
 \eta=\delta+\sqrt{220\delta^{1/4}}+2\sqrt{2\delta},\quad
 E=4\eta+8Q,\quad
 D=8E+\frac{12md+4d+14}{q}.
$$

The new estimate does not identify D with the older scalar expression.
Instead set

$$
 t=\delta_{\rm ld}(a,b,v+\epsilon,q,2m+2,d,1)+\sqrt Q+\rho.
$$

The recovered PR545 theorem supplies universal A0 > 1 and 0 < B0 < 1 such
that `min(1,t) <= deltaQld A0 B0 epsilon m d q`, for every nonnegative
epsilon. Its proof retains both errors in v and handles large passing
errors using the lower bound on low-degree soundness. It is not applied
to D directly.

Monotonicity in the nonnegative soundness input proves delta <= t.
When t <= 1, the nonnegative summands of t give sqrt(Q) <= t and rho <= t;
in particular Q <= t. On this interval,

$$
 \delta\leq t^{1/8},\quad
 \sqrt{220\delta^{1/4}}\leq15t^{1/8},\quad
 \sqrt{2\delta}\leq2t^{1/8}.
$$

Admissibility gives m,d >= 1, so the rational remainder is at most 30 rho.
Consequently D <= 734 t^(1/8) <= 1024 t^(1/8). For t >= 1 the unit cap
alone gives the corresponding inequality. Thus, on the entire domain,

$$
 \min(1,D)\leq1024\sqrt{\sqrt{\sqrt{\min(1,t)}}}
 \leq1024\delta_{\rm qld}(A_0,B_0/8,\epsilon,m,d,q)
 \leq\delta_{\rm qld}(1024A_0,B_0/8,\epsilon,m,d,q).
$$

The middle step applies the recovered square-root closure three times.
The last step increases only the positive prefactor exponent; its proof
holds for every nonnegative epsilon and does not assume epsilon <= 1.
The chosen constants are therefore A = 1024 A0 and B = B0/8, before P,
epsilon, or S. This is the bound proved by
`exists_actual_rounded_global_pair_error_bound`.

For each of the two bases on each player side, the completed measurement's
defect is at most one by the normalized POVM integrand estimate. Taking
the minimum with its proved D bound and applying the scalar theorem leaves
the actual constructed measurement unchanged. No constant-measurement
fallback is used in the final assembly.

# Required Action

The original source theorem is fully closed. There is no remaining
mathematical obligation in its proof. The three preexisting unproved
line assertions in Apply.lean remain separate and are not dependencies.
The separate source-labelled extended-line and seed-bearing game routes
remain governed by `qpbt_combined-lines-error-term.tex` and
`qpbt_ld-dimension-divisibility.tex`. The public pair conclusion mentions
neither auxiliary game and does not require their equivalence as a premise.

# Validation

The private focused dependency checker emits only necessary objects inside
this worktree. No full build, CI, reviewer, dispatcher, publication, push,
PR mutation, descendant agent, or runtime control is used. Installed normal
hooks pass their installation check. Focused checks pass for the recovered
dependency chain, the actual scalar bound, and Apply.lean. The latter has
only its three preexisting unrelated line holes. The existing complex
Claim 17-2 hole also remains separate from the recovered real-part route.

The full explicit signature queries and GlobalPairWitness field expansion
are retained in `.lake/Issue513FinalAxioms.log`, with their query source.
All thirteen queried closure roots contain exactly `propext`,
`Classical.choice`, and `Quot.sound`, including the original source theorem,
the full recovered established constructor, the point and line constructors,
the subline law, the actual pair constructor, and every new scalar theorem.
No hidden section, typeclass, supplied-line, or supplied-global premise appears
in the complete source or recovered constructor signatures.
The source-header guard passes against d0ddff11, and the new proof modules
contain no sorry, axioms, unsafe bypasses, placeholder tactics, or debug commands.

The QPBT aggregate import passes a focused Lean check. `leanblueprint web`
succeeds with existing bibliography warnings. Blueprint synchronization passes,
and the declaration checker resolves all 1766 inventory entries after its
regeneration. The generated inventory remains ignored, as configured by the
repository. Both completion markers are added only to the exact proved source
pair statement and the matching proved auxiliary entries. The other source
auxiliary routes retain their previous status. Audit YAML, the eight required
sections, staged whitespace, and the 100-column Lean scan are checked.

# Statement Integrity

Paper assumptions: admissible parameters and a projective Pauli strategy
passing with positive error epsilon. Lean assumptions: the identical
`AdmissibleParams`, positive epsilon, and `ProjectiveSetting` domain.
Paper conclusion: universal A > 1, 0 < B < 1 and complete projective
polynomial-pair measurements on both expanded local spaces, with both
point-consistency displays for X and Z. Lean conclusion: the unchanged
`GlobalPairWitness` at `deltaQld`, with exactly those four fields.
Verdict: faithful boundary encoding; no new assumption or changed quantifier.

The complete public target signature is unchanged:

```lean
theorem exists_globalPairWitness :
    ∃ a b : ℝ, 1 < a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 < ε →
        ∀ S : ProjectiveSetting P ε,
          Nonempty (GlobalPairWitness S (deltaQld a b ε P.m P.d P.q))
```

The recovered combined-line consistency statement is also unchanged.
Its original hypotheses explicitly fix a polynomial point-error family;
its conclusion bounds the actual X-Z-X measurement on every directed
opposite placement. The established extended-line theorem retains its
directly indexed law, completed answers, degree support, existentially
supplied points, and `C*m*poly(epsilon,md/q)` bound. It is an auxiliary
statement, not the stronger printed source extended-line theorem.

# Review Use

The new mathematical contributions are exactly
`actual_rounding_error_le_root`, `scale_deltaQld_le`,
`exists_actual_rounded_global_pair_error_bound`, and the composition closing
the original source theorem. Inspect the unit cap and the t <= 1 argument
first, then the universal quantifier order and all four consistency fields.

Recovered proof content, with no new-proof attribution:

- PR549 `aeaca3aee589ff666c5ab6feb2681e2cb06e8b1d`: point-to-line comparisons,
  conditioning, heterogeneous pasting and the actual line consistency,
  X deficits, extended-line measurement and real-part estimates, and the
  full established constructor. Its prior provenance through
  `6e8d67ef8ba22de69a0c166adcdf23ba6e7a33aa` is preserved.
- PR545 `2f8f5cc4631db2db23f76513a2f7f56dffc8fa4f`:
  `DirectPassingErrorBounds.lean`, retaining the full actual passing error.
- Issue529 `a7a52e4c0d7bad95d471036accedd33b358694fb`:
  `Test/Soundness/ErrorBounds.lean`, recovered as `RootErrorBounds.lean`.
- The preceding issue513 constructor at d0ddff11 is reused without changing
  or reproving its operator estimates, concentration, or completion.

Existing split sampling, collision, retained-mass, positivity, and placement
APIs are reused. Only the needed zero-direction estimates from PR549's
larger sampling file are recovered. The old sampling helper name is replaced
by the existing equivalent uniform-resampling theorem. One recovered
conditioning proof has a local 800000-heartbeat allowance.

The scalar theorem includes epsilon = 0. The same point, line, and pair
constructors also allow that endpoint; recording a separate strengthened
public theorem is deferred so the original positive-error target stays the
sole source theorem changed here.

# History And Costs

The first recorded clock is 2026-09-14T11:50:59Z; the 25-minute limit includes
validation, audit, and a normal commit, with the last three minutes reserved
for finalization. MAIN records the owner's MAX-effort mathematical-gap
exception and the authoritative terminal native completion span and usage.

Prior elapsed spans remain separate: 9760 seconds; 1311.339 seconds;
1262.781 seconds; 827.06 seconds; 1367.512 seconds; 1277.712 seconds.
Their elapsed-span sum is 15806.404 seconds before this continuation.
Native token snapshots are cumulative and nonadditive; current native token
usage is unavailable to this worker and is not reported as zero. The
separate issue278/B8 and recovered issue512 histories are not reset or added
again as new proof effort.

All writes are confined to
`/home/drx/MIPStarRE-qpbt/.worktrees/issue-513-independent-attempt3-20260912`.
The frozen PR552 index, all other worktrees, runtime/accounts/caps, and secret
material are untouched. No history reset is performed.
