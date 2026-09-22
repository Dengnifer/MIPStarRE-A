---
title: "Nonempty games refute universal attainment"
date: 2026-09-22
purpose: >
  Specify a source-domain counterexample using a verified external theorem,
  distinguish that mathematical argument from the existing Lean evidence,
  and return the remaining C3 and consumer obligations to main.
issue: "#703"
---

# Nonempty Attainment Audit

The printed `lem:symmetric-strat` is false even for nonempty finite
alphabets. An explicit symmetric game below has 419 questions, 16 answers,
value one, and no optimal finite-dimensional strategy. This is a mathematical
consequence of Slofstra's theorem with its actual game construction checked.
It is **not a kernel-checked nonempty refutation**. The existing Lean proofs
and exact unasserted printed proposition are unchanged. The gap row stays
`open`; this packet does not meet the assignment's terminal adoption criterion.

Base: `429de7f0fa6ca621e4d42ac48f192e984eea49bb`. Session:
`mathfix-703-20260922-01`. Authorization is the 3600-second additional task in
`/tmp/main-attainment-packet-20260922.md`, also recorded in issue #703, whose
body was read as context. No other session was dispatched and no publication,
runtime change, full build, or independent review was performed.

## Source and Statement Integrity

Read in canonical order: `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex`
definitions at 10-57 and 74-92, printed lemma at 94-99 and proof at 101-130;
the four symmetrization blueprint nodes in `ch12_qpbt_games.tex`; then
`Games/Defs.lean`, `Games/StrategyClasses.lean`, and `Games/Symmetrization.lean`.
The existing paper-gap note and the September 12, 18, and 19 audits were read
before extending the investigation.

| Component | Printed statement | Lean and current evidence |
| --- | --- | --- |
| Domain | Symmetric finite game, finite-dimensional pure-state POVM strategies | `SymmetricGame` also admits empty answers; the new mathematical witness has nonempty alphabets |
| Hypotheses | Real `eps >= 0`, `val*(G) = 1 - eps` | Identical antecedents in `PrintedSymmetricProjectiveAttainmentClaim` |
| Conclusion | One symmetric projective strategy of value at least `1 - eps` | Recorded exactly as an unasserted `Prop`; not proved |
| Given strategy | Construction in source proof | Existing theorem preserves the supplied value exactly |
| Supremum | Source proof chooses separately for every `eps' > eps` | Existing approximate and positive-slack forms are proved, with nonempty answers |
| Verdict | Universal attainment | False on the nonempty domain by external mathematics; its positive-slack replacement has a weaker conclusion |

No public Lean statement, hypothesis, quantifier order, constant, game
definition, or source mirror changed. No new Lean declaration needs a claim.
The empty-answer proof is preserved as evidence about its original domain.

## External Theorem and Concrete Game

Primary source, verified on 2026-09-22:
[William Slofstra, *The set of quantum correlations is not closed*,
arXiv:1703.08618v2](https://arxiv.org/pdf/1703.08618v2), June 29, 2017.
Version 2 is important for the theorem numbers below.

| Locator | Actual assertion used | Comparison with this project |
| --- | --- | --- |
| pp. 1-3, Theorem 1.1 | A specific finite game has perfect play in `Cqa` but none in `Cqs` | More than non-closure: the game and its zero-one predicate are part of the result |
| pp. 8-11, Section 3 and Theorem 3.2 | For a binary linear-system game, perfect spatial play, perfect finite-dimensional play, and a finite-dimensional representation detecting `J` are equivalent | Finite pure projective strategies match a subclass of the project's POVM strategies; finite Naimark dilation supplies the converse needed here |
| p. 11, Proposition 3.4; p. 15, proof | Approximate representations detecting `J` give finite-dimensional strategies with success tending to one on every question pair | This gives a sequence of allowed finite strategies, not an infinite-dimensional substitute strategy |
| pp. 20-21, Proposition 4.8; pp. 17-19, Lemma 4.4 and (4.1) | Explicit finite transformations of presentations into a binary solution group | The exact transformations below specify the matrix, without an unspecified missing correlation or separating hyperplane |
| pp. 22-25, Proposition 5.1 and proof of Theorem 1.1 | For that solution group, `J` is undetected by every finite-dimensional representation and detected approximately | The two properties supply the exclusion of perfect play and the approximating sequence, respectively |

The construction begins with

```text
K = <x,y,a,b | a^2=b^2=1, [a,b]=1,
               yay^-1=a, yby^-1=ab, xyx^-1=y^2>.
```

The source establishes that `K` is sofic and `a` is nontrivial, hence detected
by approximate representations (Lemma 5.3 and the stated sofic properties).
In finite quotients the image of `y` has odd order, since it is conjugate to
its square. Conjugation by `y` exchanges `b` and `ab`, so `a` vanishes in
every such quotient. Residual finiteness of finitely generated linear groups
then makes `a` trivial in every finite-dimensional representation (Lemma 5.4).
Proposition 4.8 preserves approximate detection while retaining `a` as a
generator. Adjoin `t` with `tat=Ja`, split this into `tat=Z`, `Za=J`, and
apply Lemma 4.4 and Proposition 4.2. Lemma 5.2 preserves approximate
detection of `J`. Every finite representation of the resulting group restricts
to one of the preceding group, where `a=1` forces `J=1`. This is the cited
proof mechanism, not a new axiom or a proposed Lean assumption.

The accompanying file
`audits/2026-09-22_issue-703-slofstra-system.py` enumerates the entire
184-by-235 binary system. The paper-gap note gives the fourteen generators,
ten conjugacy triples, two initial linear relations, and both finite
transformations. In the first application of Proposition 4.8, `y=zw` and
`xzx^-1=z` change `xyx^-1=y^2` into `xwx^-1=wzw`. In the second,
`x=z2*w2`. This fixes the otherwise arbitrary generator names and choices
of order. The final stage has 67 old variables and 24 sets of seven new
variables, with 40 old rows and 24 sets of six new rows.

The finite script checks 235 distinct columns, 184 rows, row sizes two once
and three 183 times, exactly one nonzero right-hand side, and the required
commuting pairs before applying (4.1). Its computed ranks over `GF(2)` are
180 for `A` and 181 for `[A|b]`. This rules out a classical solution but is
**not** the proof excluding a perfect quantum strategy.

For row support `V_i` in increasing column order, Alice answers a triple of
bits `alpha`, and Bob answers a bit `beta`. With uniform questions `(i,j)`,
accept iff the first `|V_i|` bits have the row parity, unused bits are zero,
and either `j` is absent from the row or its assigned bit equals `beta`.
The fixed answer sets have sizes 8 and 2. The law is `1/(184*235)` at every
pair. The explicit acceptance functional is its weighted sum of the
accepted correlation coordinates. It is bounded by one; full support makes
value one equivalent to perfect play on every pair. The fixed-output
encoding preserves Slofstra's perfect and approximate-perfect strategies:
extend valid assignments by zero; for a perfect strategy discard invalid
answers, which have zero marginal probability, by classical postprocessing.

To obtain the source's symmetry, use questions `L i` and `R j` in a disjoint
union, common answers `(alpha,beta)`, and mass `1/86480` on each of
`(L i,R j)` and `(R j,L i)`. All equal-role pairs have mass zero. The
predicate reads Alice's first coordinate and Bob's second on the first
orientation and reverses them on the second; on equal-role pairs it rejects.
This is a normalized symmetric Boolean game with 419 questions and 16 answers.

Every strategy has value equal to the mean of two original-game strategies
obtained by taking marginals (and exchanging parties). Conversely, if the
original state's coefficients are `psi_ij`, the state with coefficients
`Phi_((i,l),(k,j)) = psi_ij * psi_kl` on common local spaces `HA tensor HB`
has norm one and is invariant under exchange. Each party measures `A` on
its first register for a left question and `B` on its second for a right
question, returning fixed unused answer coordinates. This reproduces the
original correlations in both orientations and preserves projectivity.
Thus the symmetric game has value one, while a value-one strategy would
restrict to a forbidden perfect strategy of the original game. This proves
the nonempty mathematical refutation at `eps=0` without using the defective
QPBT attainment assertion.

## Candidate and Edge Audit

The exact valid content of the source construction is equality of the two
sets of attainable values: arbitrary finite strategies versus symmetric
projective finite strategies. Forgetting structure proves one inclusion;
the already proved given-strategy construction proves the other. This
preserves every attainable value and entails equality of suprema, but does
not make a missing supremum a member of either set.

For every `delta>0`, the supremum property supplies a value strictly above
`val*(G)-delta`, and the construction preserves it. The existing weak
inequality for every positive slack is equivalent to this strict form by
using `delta/2`. It needs no fixed numerical loss. This proves the existing
approximate form from all its explicit hypotheses.

| Candidate or edge case | Result |
| --- | --- |
| Exclude empty answers only | Still false at the constructed nonempty game |
| Require positive error or value strictly below one | Still false: give old pairs weight `c` and a fresh always-rejecting diagonal pair weight `1-c`, for `0<c<1`; the value is `c` and remains unattained |
| Value zero on the nonempty domain | Attained: strategies exist and every value is nonnegative and at most zero |
| One answer | Attained by the unique deterministic answer behavior |
| Empty questions | Incompatible with a normalized question law |
| Assume an optimal strategy | Reintroduces exactly the disputed conclusion as an input; rejected |
| Fix a dimension or change to an infinite-dimensional model | Changes the source semantics; not implemented or proposed as an adopted repair |
| Give a fixed positive slack | Weaker than the all-positive-slack result; any fixed loss can be halved |
| Arbitrary positive slack plus exact value preservation | Valid for the two direct value uses, but strictly weaker than universal attainment and not terminal under unchanged C3 |

No candidate here establishes all four adoption conditions. In particular,
there is no claim that being sufficient for later value estimates makes a
weaker statement admissible under C3. With the original hypotheses and
endpoint conclusion both unchanged, the counterexample rules out a true
universal statement. Main must dispose of that incompatibility; this worker
does not relax C3, redefine strategies, or introduce an attainment hypothesis.

## Complete Consumer Inventory

An exact-label search of the entire primary paper mirror has two invocations
besides the declaration itself.

1. `10_oracularization.tex:317-321`, proof of `thm:oracle-soundness`.
   It starts with an actual strategy of value `1-eps` and only requests
   projective measurements. Use Naimark dilation alone, preserving all
   correlations and Schmidt rank; the product ancilla is explicit in
   `04_preliminaries.tex:1007-1033`. The remaining proof retains distinct
   `A,B`, constructs `C,D` on the same state, and concludes both the value
   estimate and the Schmidt-rank bound at 401-405. Full symmetrization is
   unnecessary and would unnecessarily double rank. No attainment is used.
2. `11_answer_reduction.tex:2322-2334`, proof of soundness in `thm:ar`.
   From `val*(G)>1-eps`, take `eps0=1-val*(G)` and the midpoint
   `eps'=(eps+eps0)/2`. The approximate form gives a symmetric projective
   strategy strictly above `1-eps`. This is exactly the starting input for
   `claim:ar-1` through `claim:ar-5`, `lem:ar-ar`, and `lem:ar-ora`, then
   `thm:oracle-soundness` at 2951-2953. Their error estimates use an upper
   bound on the strategy's failure probability, so no constants or error
   parameter changes are needed. The downstream value uses of `thm:ar` in
   `13_gap_preserving_compression.tex:287-326` retain the same soundness
   statement, and completeness starts from an actual perfect PCC strategy.

The second theorem also prints an **entanglement** conclusion at
`11_answer_reduction.tex:2110-2115`. Its closing justification at 2995-2999
preserves the state *after* symmetrization. A rank-`r` original state becomes
rank `2r`: the two orthogonal role blocks have the same nonzero Schmidt
coefficients divided by `sqrt(2)`. Value preservation therefore does not
establish the printed rank-`r` conclusion for an arbitrary given input.
This audit identifies a missing derivation, not a counterexample to the
entanglement theorem. A proof for the original two measurement families or
another rank-preserving transfer remains necessary. Consequently the earlier
note's blanket assertion that every source conclusion is covered is withdrawn.
No claim is made that transitive consumers of that entanglement assertion are
settled. No theorem or game in those chapters has been edited.

A general rank-preserving symmetric-strategy replacement cannot resolve this:
in the symmetric one-question game accepting unequal binary answers, distinct
deterministic answers give a perfect rank-one strategy. A symmetric pure
rank-one strategy has identical local states up to phase and identical local
measurements, so its success is `2*p*(1-p) <= 1/2`. A valid repair must use
the particular downstream construction, not strengthen general symmetrization
by an impossible rank guarantee.

Blueprint inventory, including all `uses` descendants and ordinary references:

| Node | Dependency or reference |
| --- | --- |
| `lem:symmetric-strat-given-strategy` | Proved exact value preservation; its sole proper `uses` descendant is `lem:symmetric-strat` |
| `lem:symmetric-strat` | Proved approximate statement; no proper `uses` descendants |
| `rem:symmetric-strat-limit` | Records the printed claim and evidence; no proper `uses` descendants |
| `lem:symmetric-strat-printed-claim` | Preserved Prop and empty-answer refutation; no proper `uses` descendants |
| `rem:naimark-for-games` | Ordinary prose references to `lem:symmetric-strat`; no mathematical reliance on attainment |

All ordinary references to these labels in `blueprint/src/chapter/` lie in
those nodes in `ch12_qpbt_games.tex`. The given-strategy node's title and proof
refer back to the source label; that prose does not add a reverse proof
dependency. There are no blueprint nodes or Lean declarations for
`thm:oracle-soundness`, `thm:ar`, or their above local claims and lemmas.

Actual Lean calls, excluding docstrings:

- `exists_symmetric_projective_strategy_of_strategy` is called only by
  `exists_symmetric_projective_strategy_of_lt_value`.
- That slack theorem is called only by
  `exists_symmetric_projective_strategy_approx`.
- The approximate theorem is referenced by the standard axiom audit in
  `MIPStarRE/QPBT/Test/AxiomAudit.lean`.
- The unasserted printed Prop occurs in the empty-answer refutation; no
  downstream theorem assumes or proves its nonempty universal form.
- `MIPStarRE/QPBT.lean` imports the two support modules and
  `MIPStarRE.lean` imports the QPBT umbrella. Other modules import
  `StrategyClasses` for independent infrastructure, without calling this
  symmetrization family.

There are no changed Lean consumers because no Lean source changed. Focused
checks below validate the preserved support modules and their direct audit
and umbrella consumers; they do not amount to a new full build.

## Missing Kernel Obligations

To refute the printed Prop on the nonempty domain in Lean, prove the following
concrete facts, with no assumed external `Statement` or new axiom:

1. For the explicitly enumerated system, its solution group's central `J`
   maps to the identity in every finite-dimensional unitary representation.
2. There is a fixed positive separation of `J` from the identity in normalized
   Hilbert-Schmidt norm achievable by representations satisfying the finite
   presentation relators to arbitrarily small positive error.
3. Exact perfect finite-dimensional play implies a representation detecting
   `J`; the approximate representations yield strategies whose rejection
   probabilities tend to zero. These are the needed directions of Slofstra's
   Theorem 3.2 and Proposition 3.4 for this system.
4. Encode the displayed uniform game in `Game`, justify padding and removal
   of invalid answers, and verify the symmetric two-copy and marginal
   transfers in the existing finite-matrix API.

Items 1-3 are substantial independent mathematics absent from the imported
library. Item 4 is a finite encoding and transfer task. No generic conditional
helper was added to conceal any of these missing conclusions.

## Budget Reconciliation

Both committed ledgers were read at the base head:
`results/telemetry/sessions.jsonl` and `results/telemetry/owner-sessions.jsonl`.
The following are grouped recorded costs, **not an exclusive cumulative
attainment total**. Source audits and construction sessions cover other work;
reviews are session-wall costs, including concurrent reviewers.

| Ledger and family | Distinct recorded work and seconds |
| --- | --- |
| Canonical #98 construction | Three continuations: 1943, 7107, 969; 10019 seconds, on the same resumed thread |
| Canonical PR158 review | Six rows: 715, 804, 1009, 1160, 588, 755; 5031 seconds |
| Owner #98 repairs | Three rows: 650, 483, 2709; 3842 seconds |
| Canonical #173 audit | Two continuations: 1853, 1086; 2939 seconds on one thread, shared across gaps |
| Canonical PR184 review | Eight rows: 534, 1020, 544, 1100, 1072, 1832, 1101, 1832; 9035 seconds |
| Owner #173/PR184 repair | Three completed rows: 2328, 1632, 2271; 6231 seconds; the earlier unfinished record of the first named session is superseded, not an extra attempt |
| Canonical #524 proof attempts | `prover-524-20260912-01`: 865 seconds; `-02`: 2199 seconds, **failed**; both retained |
| Canonical PR540 review and metadata | Reviewer: 3178 seconds; native metadata task: 188.378 seconds; its admission row is superseded by its terminal row |
| Owner PR601 realignment and review | 3518 and 633 seconds; repeated copies of the same named records are not new attempts |
| Owner PR540 publication/repair and review | 3390 and 620 seconds; repeated copies are not new attempts |
| Owner PR609 cleanup and review | 3852 and 714 seconds; duplicated cleanup record counted once |
| Owner PR634 build and review | Build duration field unknown; recorded interval 09:36:25Z-10:21:07Z on September 19 is 2682 calendar seconds, not substituted for an unrecorded work duration; review 1040 seconds |
| Owner #524/#598 truthfulness audit | 615 seconds, shared across the two gaps |
| Canonical #667 follow-up | 1760, 1359, 600, 600 seconds; the last two failed/time-out tasks have unknown usage, not zero cost; this is shared source-adoption work |

The September 12 audit also records an unsuccessful initial reservation with
unknown cost; no duration is invented. Resumed-thread token counters from #98
and #173 are not added as independent per-task usage. All existing reports,
including failed paths and earlier empty-answer-only conclusions, remain in
the repository unchanged. Other cross-cutting publication/CI/operator time
has no exclusive attribution here and is not silently declared zero.

No reliable original **gap-specific** attempt count, work-time total, or start
anchor was supplied. The earliest preserved related construction starts at
`2026-09-04T07:54:07Z` (#98); the recorded #173 audit starts at
`2026-09-04T13:57:46Z`, and the explicit #524 attempt at
`2026-09-12T05:31:24Z`. These are distinct historical anchors, not a newly
chosen beginning of the gap. Main must reconcile any additional attribution.
The current admission is one additional bounded task starting
`2026-09-22T13:35:17Z`, with deadline `14:35:17Z`. It does not reset an
ordinary cap or invoke the unrelated #118/B8 exception. The receipt records
this session's actual measured interval separately; the dispatcher owns final
telemetry. No continuation or additional budget is authorized by this audit.

## Validation

The following focused checks succeeded against the unchanged Lean tree at the
base head and the documentation in this packet:

- `lake env lean MIPStarRE/QPBT/Games/StrategyClasses.lean`
- `lake env lean MIPStarRE/QPBT/Games/Symmetrization.lean`
- `lake env lean MIPStarRE/QPBT/Test/AxiomAudit.lean`: all thirteen audited
  declarations, including the symmetrization approximation and four QPBT
  headline theorems, have exactly the three standard axioms.
- `lake env lean MIPStarRE/QPBT.lean`: the direct umbrella consumer checks.
- A `lake env lean --stdin` probe importing `Games.Symmetrization` printed
  axioms for the given-strategy, slack, and approximate theorems,
  `SymmetrizationObstruction.no_strategy`, its `value_eq_zero`, and
  `not_forall_printedSymmetricProjectiveAttainmentClaim`. All six use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `rg -n "sorry|axiom"` on the two support files returned no matches.
- `python3 -B audits/2026-09-22_issue-703-slofstra-system.py` produced the
  dimensions, row statistics, ranks, and rational mass reported above.
  Its `--json` output also parsed successfully, with 235 columns, 184 rows,
  valid column indices, and exactly one odd-parity row.
- `leanblueprint web` rendered successfully. That initial run lacked the
  generated `web.bbl` and warned about bibliography entries. After the normal
  `texra-blueprint bbl` step, `texra-blueprint web` passed with no renderer
  or missing-bibliography warning. These are generated, ignored artifacts.
- The actual rendered dependency graph in
  `blueprint/web/dep_graph_document.html` was parsed using the standard HTML
  parser and Graphviz's `dot -Tdot_json`. Transitive traversal gives exactly
  the descendants listed above. A first attempt using optional `pydot`
  failed because that package is absent; no package was installed.
- `scripts/blueprint_lean_sync.py --root . --update-lean-decls --ci` passed
  with 1877 generated declaration entries. The initial read-only sync after
  web rendering reported 254 stale generated entries; the normal refresh
  resolved them. Four orphan marks and two missing proof marks in unrelated,
  unchanged chapters remain advisory warnings. No metadata in those chapters
  was changed.
- `lake exe checkdecls blueprint/lean_decls` resolved all 1877 declarations.
  It built only the small checker executable, not the library.
- `texra-blueprint paper-gaps check` resolved all 43 referenced slugs and
  registered source keys. Existing missing-verdict-marker warnings remain.
- `scripts/check_paper_gap_note_style.py --changed-files
  docs/paper-gaps/qpbt_symmetrization-attainment.tex --ci` and
  `scripts/check_blueprint_latex.py` passed.
- The focused `make build/qpbt_symmetrization-attainment.pdf` in
  `docs/paper-gaps/` produced a 14-page PDF with resolved citations and no
  overfull boxes. The first run exposed an invalid `split` alignment in the
  new equations; changing that display to `aligned` fixed it. Long declaration
  names in the retained historical section were made breakable.
- `scripts/install_git_hooks.sh --check` and `git diff --check` passed.

There was no full `lake build`, CI run, independent mathematical review, or
kernel proof of the nonempty counterexample. Main owns those next decisions;
the successful support-file checks do not discharge the external theorem.

## Main Disposition

The nonempty mathematical obstruction is now explicit. The adoption request
is not converged: the new refutation still needs the concrete kernel
obligations above, positive slack remains a weaker conclusion under unchanged
C3, and full source-consumer sufficiency includes the answer-reduction rank
obligation. Independent review and main's four-condition decision remain
required. No owner permission blocker was encountered.

Suggested single-line #27 record, for main to post:

> #703 supplies an explicit nonempty symmetric nonattainment game from
> Slofstra's theorem; Lean proof obligations, unchanged C3, and the
> answer-reduction rank comparison keep the symmetrization row open.

Main owns any corresponding event/design-decision entries and publication;
this worker changed no telemetry ledger or runtime state.
