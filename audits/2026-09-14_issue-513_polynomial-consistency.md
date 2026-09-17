---
title: "Polynomial consistency from the direct soundness point conclusions"
date: 2026-09-14
purpose: >
  Record the proved cross-player estimate for compressed extended-polynomial
  POVMs, its application to direct soundness and projective rounding, and the
  remaining construction estimates for the global polynomial-pair witness.
issue: "#513"
status: partial
---

# Result

The point-derived cross-player estimate requested in obligation 2 of
`audits/2026-09-12_issue-513_composition-compatibility.md` is proved.
No polynomial-consistency bound is assumed. The public theorem
`exists_globalPairWitness` and its proof hole are unchanged. Neither the
new auxiliary statements nor their blueprint entries certify `lem:qld-4-7`.

Let A and B be complete polynomial-tuple POVMs on possibly different local
spaces. Let Q_A and Q_B be point POVMs, and normalize the bipartite state.
All point averages below are uniform. If

    Cons(A evaluated, Q_B) <= etaA,
    Cons(Q_A, B evaluated) <= etaB,
    Cons(Q_A, Q_B) <= deltaQ,

then the new estimate is

    Cons(A, B) <= etaA + 2 sqrt(deltaQ + etaB) + n*d/q.

First apply the existing consistency comparison along A, Q_B, Q_A, B.
Distinct polynomial tuples differ in some component, so Schwartz--Zippel
for that component bounds their collision probability by n*d/q. Summation
against the nonnegative joint outcome weights converts evaluated consistency
to full polynomial consistency. There is no factor for the tuple length.
The result applies to POVMs without any projectivity assumption.

For the actual extended strategy, disagreement after the total point readout
forces rejection in the point/point branch. Wrong-format answers also reject,
so this implication requires no support hypothesis. The existing branch
estimate gives Cons(Q_A,Q_B) <= deltaQ from the supplied joint point
measurements' self-consistency. Ground compression at the two distinguished
Naimark coordinates preserves each evaluated comparison exactly. Consequently
`ExtendedLineGame.compressed_polynomial_consistency_le` proves the displayed
bound for the compressed soundness POVMs on the original expanded spaces,
with n = 2m+2. Its only quantitative assumptions are the two soundness point
conclusions, with their orientations displayed explicitly.

# Actual errors and rounding

For the direct soundness application the retained errors are

    e = 3 (sqrt(deltaQ + deltaL) + m*d/q),
    eta = deltaLd(a,b,e,q,2m+2,d,1),
    delta = eta + 2 sqrt(deltaQ + eta) + (2m+2)*d/q.

Both the actual point error deltaQ and line error deltaL occur in e.
The passing-value theorem supplies this e; it is positive because admissibility
gives positive m, d, and q. The two soundness point conclusions give
etaA = etaB = eta. The third, polynomial-consistency conclusion is deliberately
unused in this verification.

The private runtime theorem `issue513_checked_soundness_rounding` calls
`exists_direct_ld_soundness` on the actual projectivized extended strategy,
applies the new compressed estimate, and invokes
`projective_rounding_preserves_postprocessed_consistency` on the original
expanded spaces. It obtains both projective polynomial POVMs and verifies
the Alice polynomial/Bob point consistency estimate with error

    R(delta,eta) = delta + sqrt(220 delta^(1/4)) + 2 sqrt(delta + eta).

The existing rounding API also supplies the opposite orientation and all
question-dependent postprocessings. The runtime theorem checks the displayed
orientation, rather than restating that universal API. It is validation of
the new operator estimate, not a committed conditional source constructor.
Its file is `.lake/Issue513Check.lean` in this worktree; SHA-256 is
`1245236b0ea369b065f60b2593382e3286ee3fa2c36aceb6c831bb8b465484b6`.

# Source and reuse

The paper passage read before proving was
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1267-1404`,
including `lem:qld-4-7`, both ordered correlations, separated-polynomial
concentration, and completion overlaps. The existing gap note remains
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.

The previous third-attempt audit and PR535's
`audits/2026-09-12_issue-513_pair-completion.md` were read. PR535 at
`1744bd9533055b9b43af9a8d46906cbafb69afdd` remains read-only; its completion
and previously verified compatibility were not reimplemented.

Issue520 at `df21901ec428ac22ebebb56466ab568fc383c554` was inspected read-only.
The relevant actual files are `Extraction/PolynomialCollision.lean`,
`Extraction/PullingMeasurement.lean`, and `Extraction/PullingDefect.lean`.
They confirm the collision reduction and a comparison through point
self-consistency. Their projective difference-polynomial distance argument
does not directly apply to compressed POVMs. The new proof instead uses the
existing general POVM consistency comparison and reuses main's
`directPolynomialAgreement_avg_le_mdq` and
`SandwichProduct.point_codeword_defect_le_avg_evaluated_add`.
No GlobalPairWitness from issue520 is imported or assumed.

PR361's published snapshot `caed322198326da6cec265a3925cfd9fea095add` and local
descendant `4b8e6b76e9c662ff51279da771ba5570e2f5d8ca` were inspected.
`exists_direct_ld_soundness_of_k_eq_one_any_strategy` already preserves all
three soundness conclusions through compression, including the stronger
polynomial bound eta. Thus compression itself is not an unresolved
mathematical obstruction. The present result establishes the requested
alternative using only the two evaluated conclusions and point self-consistency;
the existing stronger route should be preferred when all three conclusions
are available. No copy of that soundness proof was added.

PR549 at `aeaca3aee589ff666c5ab6feb2681e2cb06e8b1d` was inspected read-only.
Its actual `exists_extendedLinesWitness_established` proof constructs the
point and line witnesses with the established C*m*poly(epsilon,m*d/q) error
on the directly indexed completed-answer domain. This is useful construction
content, with its stated source-domain caveat; it is not merely a supplied
witness helper. Its patch is not duplicated here.

# Remaining estimates

The next operator estimates are both `eq:qld-g-42` and `eq:qld-g-43` for the
rounded polynomial measurement R. On the expanded state, one must bound the
average over (x,z,alpha,beta) of

    sum_g || R_g [I - sum_{alpha*r+beta*s=g(x,z,alpha,beta)}
                           M_X(x,r) M_Z(z,s)] psiHat ||^2,

and the corresponding expression with M_Z M_X in the opposite order.
The tensor placements are AA' and BA'', and then BB' and AB''. These bounds
must follow from the rounded point comparison and CombinedPointsWitness
approximation estimates, with all losses explicit.

Afterward, the nonlinear-scalar and wrong-variable-block estimates must give
`eq:qld-g-non-separable`. The saved polynomial-image estimates cited by PR535
cover scalar nonlinearity; the two variable-separation classes and their
operator inputs must still be checked. Retained point overlaps through
`eq:qld-sgg-mhat-sandwich` are required for both Pauli bases and placements
before PR535's completion estimate can close the desired point defects.
Finally, absorb the actual R(delta,eta), including its eighth-root term,
into the universal deltaQld constants. No such absorption is asserted here.

# Verification and statement integrity

Both new Lean modules and the QPBT and project root import files typecheck.
GroundCompression and RoundingTransport were compiled only as required private
dependencies. All five new lemmas, the actual soundness/rounding runtime
theorem, and `exists_direct_ld_soundness` have axiom closure exactly
`propext`, `Classical.choice`, and `Quot.sound`. The public target still lists
`sorryAx`. The new production files contain no proof holes, axioms, bypasses,
placeholder tactics, or debug commands. Whitespace and 100-column scans pass.
The blueprint web build succeeds with the existing missing-bibliography
warnings. Declaration inventory is regenerated after the web build, because
the latter also emits legacy references. Blueprint synchronization and
changed-declaration coverage are checked against that regenerated inventory.
The declaration checker resolves the imported names. No full lake build,
CI, review, publication, PR operation, or descendant was run.

- Paper assumptions: admissible parameters, positive strategy error, and a
  projective Pauli strategy passing with that error.
- Lean assumptions of the public theorem: unchanged AdmissibleParams,
  positive error, and ProjectiveSetting. No additional input is introduced.
- Paper conclusion: universal a>1 and 0<b<1, projective polynomial-pair
  measurements on the required expanded spaces, and all four point
  consistency requirements with the source deltaQld error.
- Lean conclusion: unchanged GlobalPairWitness and error function, with
  the original quantifier order.
- Verdict: faithful boundary encoding preserved; the public proof remains
  incomplete. The new blueprint completion tags apply only to the explicit
  auxiliary estimates, and the source theorem remains `notready`.

# History and costs

This native continuation began at 2026-09-14T07:53:23Z in thread
`01a09ee8-0e25-71f1-bc88-7c97e130d6cd`, with a 25-minute elapsed limit and
no descendants. Main records its final end time and native telemetry from
the terminal report. No protected watchdog claim was modified.

The initial clean checkpoint was `4dc07019b345382749ee9be4dc64ba042e087b35`.
The authorized normal merge of main snapshot
`b48d60aded3a` produced `a8f43d6e`. Telemetry histories were merged with their
union rules; only the three conflicted generated GitHub snapshots were
resolved to the newer incoming snapshot. The merge-loss guard passed.
Only the authorized issue513 third-attempt worktree was written.

Preserved earlier elapsed costs are: issue119 prover sessions 1927 seconds;
issue513 first attempt 3602 seconds, second attempt 2001 seconds, and third
attempt 2230 seconds. Their subtotal is 9760 session-seconds before this
continuation. They are session spans, not a new active-time attribution.
The earlier audit's known additive token totals remain 31,555,490 input,
30,806,016 cached input, and 87,658 output, including 28,404 reasoning tokens.
The second attempt's unknown usage and cumulative native snapshots remain
unknown/nonadditive. Neither this continuation nor issue520 resets or
duplicates those historical charges. The broader issue278/B8 history of
twelve attempts and 24242 seconds is preserved separately without adding
it to this narrower subtotal.
