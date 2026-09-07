# Issue301: Required Post-Activation Compatibility Review

This owner-requested check supplements the normal independent control-policy
review. It is not prior approval, a replacement for the complete diff review,
or permission to activate an unmerged branch. Read actual source on ghz only;
return status, hashes, counts and findings, not source contents or diffs to meta.
Do not inspect/export tmux contents or change credentials, leases or launchers.

## Actual Root And Proposed Policy

The current root is UUID01a076bc-f4ad-7813-805b-c8b4dac71a14, PID2085772,
process start182075393, named main, Astra Ultra. Its runtime
default_subagent_model is Astra. The canonical Space lease reserves three
native descendants within five total, with one main and one app-server
reservation and external admission zero.

Meta confirmed this state in:
`/home/drx/.cache/mipstarre-dev/owner-tools/space-switch-immediate-20260907.json`.
The durable launcher is:
`/home/drx/.cache/mipstarre-dev/owner-tools/qpbt-resume-space-cap5-20260907.sh`.
Meta already adapted the merge service at PID2104266; do not duplicate it.

The existing receipt proves only a PRE-activation live-root check. The reviewer
must also verify the current real root and actual canonical lease against the
proposed POST-activation Sol-first policy at the exact reviewed head.

A safe isolated test may substitute only the policy lookup with the proposed
exact-head policy JSON. Keep process discovery, PID/start identity, root model,
effort, actual runtime default, capacity, account and lease validation real.
Do not mock a successful root/lease result or mutate main to create the test.
Record exact reviewed SHA, policy/configuration hashes and whether the source
and observed process stayed unchanged during the check. This isolated result
is compatibility evidence, not a live deployment claim.

The intended result preserves the hot Astra-default root while future routine
children explicitly request Sol. If the actual validator instead requires a
default transition, report the precise failing condition and hold activation
for a coordinated quiescent meta transition. Do not restart or weaken checks.

## Selection And Observation

Against the proposed activated policy, verify routine auto selection for
prover, reviewer and scout returns exact gpt-5.6-sol with Ultra. Hard or
escalated work must select exact gpt-6-astra with an explicit reason. Missing
hardness reasons and requested/observed mismatches must not silently fall back.
Routine review must retain independent identity and exact-head binding, while
this control-policy review is appropriately Astra.

Before activation, auto Astra with an explicit pre-activation rationale is
intentional and is not itself a finding. Preserve this distinction in results.
Check the rolling new-dispatch ratio, exclusions, missing observation handling
and predecessor/budget fields as part of the ordinary complete-patch review.

## Live Acceptance After Merge

Root/coordinator must repeat selector checks against the actual committed main
policy after normal CI, review and service integration. Then use a useful
fresh native Sol job with explicit gpt-5.6-sol, Ultra and a supported
non-full-history fork. Verify actual model/effort context and predecessor
links independently; a resumed Astra child or configured ceiling is not proof.
No filler/probe child is required when no useful job is ready. The prepared
PR249 publication-recovery assignment is a candidate, not an executed test.

Final metadata belongs in `/tmp/qpbt-sol-policy-activation-20260907.json`.
