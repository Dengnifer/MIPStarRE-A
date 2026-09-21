# Two source corrections adopted

Main decision, 2026-09-21 UTC (2026-09-22 local date).

PR672 head `691c2880fe1587d73b36ca82226e64ec343cf8ae` has complete green
canonical CI and independent Astra hard review
[5270109079](https://github.com/Dengnifer/MIPStarRE-A/pull/672#pullrequestreview-5270109079).
Reviewer `reviewer-pr672-20260922-01`, thread
`01a0c506-eec1-7613-9287-867a8b0010d7`, completed in459 seconds, exit0.
The genuine final review was formatted with the canonical review helpers and
published without fabricating a fresh-head status. Original author1359 seconds,
earlier audit/review2835 seconds and their predecessors remain charged.

Main adopts only the cross-basis phase and decoder corrections under
issues-prs section6 and completion C3, for these independently verified reasons:

1. Cross-basis correctness: the joint-projector calculation gives the full
trace phase; the admissible `(8,1,2)` counterexample refutes the printed
different-basis commutation branch. Sufficiency: spectral sums and swap
conjugation use the corrected product relation throughout paper, blueprint
and Lean consumers. Minimality: the determined phase is restored without
restricting vectors or changing constructions or robustness conclusions.
Convergence: corrected and downstream results type-check with standard axioms.
2. Decoder correctness: the full-field encoding definition gives precisely
the restricted evaluation identity; `X^2` at `(8,1,2)` refutes both unrestricted
substitutions. Polynomial equality is kept distinct from evaluation equality
when `d >= q`. Sufficiency: both point orientations, non-encoding mass bounds,
pulling and exact swap-label cancellation justify all consumers through both
soundness forms. Minimality: no outcome is removed, no `d < q` restriction or
encoding premise reaches the source-facing construction, and all added errors
fit the unchanged universal error family including zero error. Convergence:
the reviewer checked the22-declaration harness and headline dependencies.

The three exact printed claims are preserved as unasserted `Prop` definitions,
not proved or assumed. The supplied-witness auxiliary is distinguished from
the internally constructed source-facing witnesses. This decision does not
adopt source-law/tensor-code replacements or dispose of any other gap.

A bounded600-second Sol worker now implements just the two terminal cells and
their note citations. That changed head still requires ordinary CI and
independent review before the service may merge it. The approved original
head is deliberately not gated during this serialized change. No completion
claim follows from this adoption.

Other current work: PR669 second review5269830825 has four findings describing
three documentation defects, assigned one900-second Sol repair with both full
rounds and earlier timeouts retained. PR671 dfbaa62b CI built Lean successfully
but19 workflow tests inherited incompatible review-model overrides from the
operator wrapper; the complete canonical CI is rerunning with only those
dispatch/review selectors unset. The failed354-second manifest is preserved at
`/tmp/main-cpa-ci671-dfbaa62b-failed-manifest-20260922.json`, with the original
wrapper log retained separately. Same-head canonical per-step logs are reused
by the rerun. No source edit, test skip or manual successful status was used.

Official comparator run35621468975 independently passed all four exports,
nanoda and Lean default-kernel replay with real landrun at sourcea3683e9b.
Detailed job106405301790 logs are retained under
`/tmp/main-cpa-official662-evidence-20260922.*`. This is preliminary evidence:
the service-merged-main pin, repeat official run and reviewed final comparator
record remain outstanding. Space-3 stays retired; cpa alone supplies main and
at most two detached workers, with no fallback or native delegates.

Both successors actually started: PR669 thread
`01a0c522-1593-7141-8408-2c245bc90d6b`, PR672 thread
`01a0c524-4070-7aa2-87ef-55abd340d65d`. Progress Log boundary comment5765179120
records this stage. The status census at17:59:15Z found no other live worker;
parked infrastructure and issue168 remain untouched.
