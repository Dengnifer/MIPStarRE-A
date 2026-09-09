### BLOCKER B7 — PR195 exact-head record versus the four-review cap

Decision requested: May main publish one explicitly labelled, exact-head
operator terminal-disposition review record, based on the fourth approval
and verified unchanged mathematical content, without launching any fifth
full-review or extra triage session?

PR195 is published at c7adb95e1c7f7bdd6b9e971db765e5a53ac4a284, fresh against
main a61ee55, mergeable, and CI-green. The recovery is complete. Main checked
all seven reviewed nontelemetry blobs against fourth-review head40cead3 and
ran the primary merge-loss guard successfully. All 253 incoming-only paths
and both telemetry histories are preserved; no mathematical delta or new
proof hole is introduced.

The binding policy conflict is precise:
- Four full reviews already exist. Approval5123351774 belongs to40cead3;
  the current head has no review record or review status.
- The complete patch fingerprint changed through telemetry, so automatic
  carry-forward under local/protocols/review.md section13 is ineligible.
  The nontelemetry fingerprint is unchanged, but that is not the current
  full-patch criterion.
- local/bin/pr_merge.py gate4 requires an exact-head review record before
  considering adjudication. Its --adjudicated option waives an adverse
  verdict/status, not an absent exact-head record.
- The owner's cap4/no-fifth-or-extra-triage instruction therefore prevents
  an unapproved new review record. Main will not fabricate a carried marker,
  post a false green status, reset the cap, or bypass the gate.

A literal-head operator ADJUDICATION template is queued for the merge
daemon. No merge-gate invocation or merge has been performed by main; no
new review record has been created. This request concerns permission for
the terminal operator record only, retaining all CI, provenance, exact-head,
and daemon-only merge requirements. It is not a request to weaken a
mathematical statement or add another reviewer session.

Other independent work continues: the existing PR238 daemon-owned lifecycle
is publishing its committed routing amendment, and issue118 attempt8 is
validating its scalar-specialization/Apply work with12452 seconds carried
and the original anchor unchanged. PR207 remains blocked by the actual
PR195 merge; downstream tails have not been started speculatively.
