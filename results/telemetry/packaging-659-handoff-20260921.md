# Packaging repair handoff, 2026-09-21

Native author:01a0c22c-d7f6-7bf1-b77c-d1359ef7b62e, now closed.
Published PR659 head:ee5bdb702734bad82e25d486e9d56ede2db689fa.
Repair commit:e2b023cc. Edited ARTIFACT.md, make_artifact.sh and its focused test
file to remove escaped identity leakage and correct the reported prose defects.

The author reports18 passing focused tests and final-head normal/anonymized
no-PDF snapshots with873 files, references/ included, no unresolved imports and
clean leak scans. Earlier full-PDF snapshots at0e710bce16de have49 PDFs and922
files after pruning339 intermediates. MAIN independently checked that the
diff from that PDF-tested head to the final head contains only these excluded
telemetry paths: builds.jsonl, completion-after-raw-20260921.md, events.md and
three github-snapshot JSON files. Independent review must still assess the
actual snapshot/log evidence; no final artifact cold build is claimed.

First checked publication failed on stale compiled dependencies after the
branch refresh. The author directly ran
`lake build MIPStarRE.QPBT.Test.NonVacuity`, a named-target dependency build,
then reran normal checked publication. The subsequent hook performed its own
required validation and pushed dc20edd3..ee5bdb70 successfully. This was not
an unqualified full build or canonical CI.

The author stopped with the PR-body update incomplete. MAIN read the prepared
/tmp/pr659-final-body.md, added the named dependency-build disclosure, updated
the PR through gh_common.py, and read back the exact head and body successfully.
Canonical CI started at the published head; fresh independent review is pending.

Original start04:15:13.967Z; end05:03:55.720Z; actual2921.753 seconds. The
30-minute initial deadline and05:01Z publication checkpoint were both exceeded.
MAIN missed the initial checkpoint, then limited further work to publication
and reporting. All elapsed time, same-task continuations and actual tokens are
retained in sessions.jsonl; there is no reset or new repair attempt.
