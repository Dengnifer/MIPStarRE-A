# Packaging merge and comparator review, 2026-09-21

PR 659 merged through the service at 13:24:44 UTC, commit
`53a47573377eb01081d53e3aca49d55002a0ae4b`, with exact reviewed head
`71715c4c06b13de3f1d0d4fcb0f698ba472a2f90` as its second parent. GitHub readback
confirms closed/merged. The service completed its publication tail at 13:25:41
and published the normal snapshot at `9518c42b3ef599c3f3a46747163ee8dfb6492104`.
No manual merge or train was used. Before integration, the normal freshness
predicate was true for 659 and 663 and false for 660, so neither fresh PR was
eligible for a train.

Independent review 5267089187 was the authorized limited sixth observation,
not a sixth full review. Fresh external session reviewer-642-20260921-01
completed in 418 seconds, exit 0, thread
`01a0c41b-5978-79c0-a4f2-c228aa848046`. The five earlier full reviews remain
retained. All 21 focused tests passed, independent suffix-domain tests rejected
the ordinary and mixed anonymized cases without producing an archive, and
both fresh no-PDF snapshots contained 873 files and all five paper mirrors.
The 49-PDF/922-file result is still historical evidence, not a current rerun.
The main gate independently validated the exact-head COMMENT and complete CI,
then posted and read back success. Raw usage is in sessions.jsonl; effective
model and wire effort remain unknown there and must not be invented.

PR 663 canonical CI passed at `8bd40f9f77d27815f65d85e81a6570146657173a`,
with a complete successful manifest and all eight steps. Build 43 seconds,
blueprint render 53, blueprint sync 258, proof debt 20, proof evasion 52;
remaining steps were 0 or 1 second. Existing frozen-source axiom-audit evidence
is retained separately, not relabeled as an exact-head run.

The first prepared review launch exited 2 before any model session because
main inherited MIPSTARRE_PROSE_MODEL=gpt-6-astra while the routine code review
explicitly selected Sol. The retry sets both model variables to Sol with
independent_review classification, retaining the original failure receipts and
1200-second review budget. No shared routing or policy changed. Canonical
review.sh admitted reviewer-pr663-20260921-01; keyrot confirms PID 1347251 on
space-3 at 13:25:31 UTC. This is independent of all authors and the PR 650 lane.
The exact-head review remains pending. The repair lane blueprint-637-20260921-01
remains live with its original 1500-second budget and no new review admission.

The completion gate run on `c880f9aeb9ead9089567dd60d6da4fa06e2859eb` before
this merge returned C1 PASS, C2 DELEGATED, C3/C4/C5/C7 FAIL, C6 PASS. It found
no proof site in 332 QPBT Lean files, a missing Terminal status column, 11
unmarked/unexempted nodes among 528, no verified comparator record, and the
then-unmerged artifact/deviations files. This is not a post-merge gate result.
The actual official four-target comparator, remaining documentation, terminal
gap adoption and final artifact checks remain outstanding.
