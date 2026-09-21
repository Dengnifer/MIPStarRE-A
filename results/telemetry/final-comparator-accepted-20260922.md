# Official four-target acceptance verified

Main independently inspected the complete final job log, downloaded through
gh_common.py. This establishes comparator acceptance at the service-merged
source pin, not overall artifact completion.

- Run35638601720, job106462118372, completed successfully2026-09-21T19:16:36Z.
- URL: https://github.com/Dengnifer/QPBT-comparator/actions/runs/35638601720
- Candidate360402fdf4a39399f94331452d6e5d0a35c144be.
- Both Lake pins: ecb97d1f66eec1e6fad964f144f78b91ce1fab36, the PR671 service
  merge; the remote pin/config readback was independently parsed earlier.
- Exact evidence: `/tmp/main-final-comparator-evidence-20260922.job.json`,
  `.job.log` and`.excerpts.log`; wrapper exit0.

Job log evidence: line1964 invokes `./verify.sh`; lines1974-1975 bind the
landrun and nanoda revisions; lines1977/1981 show no fake-landrun argument;
line1993 invokes `lake env comparator comparator.json`. Line2001 exports all
four configured targets from Challenge; line2791 exports the same four from
Solution. Lines2792-2796 run nanoda and Lean's default kernel, explicitly accept
the solution in both, and finish with `Your solution is okay!`.

The targets are pauli_soundness, pauli_soundness_qubit, exists_spcc_value_one
andexists_ld_soundness underMIPStarRE.QPBT. The unchanged configuration enables
nanoda and permits only propext, Quot.sound andClassical.choice. Four `sorry`
warnings belong to the intentional Challenge statement stubs, not Solution
proofs or QPBT library debt. The toolchain and verifier pins/hashes remain in
`final-comparator-started-20260922.md` and the retained exact-head readback.
The final run reused its matching verification-tool cache; no new diagnostic
substitution, reduced target set or second run was used to obtain acceptance.

One bounded Sol900s worker is now recording this actual result in
docs/comparator.md on its own new branch, including the exact C5 record and
truthful residual trust. It may not touch PR669's README/theorem-index files or
the completion criteria. Normal CI and independent review are still required
before that record reaches main. Issue676's prepared canonical-complement
comparison is deferred to a later free lane in favor of this now-ready record.

## Source Audit Still Pending

The error-contract author completed and published PR675 at
b7ebf9532831aa00cd1fb21f30f3215be7cb4b29, with both rows still pending and no
existing predicate/game/protocol/register change. It retains exact printed
unasserted contracts, explicit big-O quantifiers and a full consumer audit.
Its result reports a substantive C3 obstruction: the additive guarantee loses
the printed product guarantee's independent-variable vanishing, and the
literal source consumer graph remains unproved. Main has admitted complete CI
and fresh independent hard review to check that exact claim, not adopted a
weaker result or changed the goal. Receipt:
`/tmp/main-error-contracts-20260922-result.md`.

Both active model lanes are the general-prime documentation/publication
continuation and the comparator record. CI672/675 and PR669's rebuild remain
model-free and serialized by the normal full-build lock. Completion remains
unproven: C3/C4, the permanent C5 record, truthful integrated docs and the
delegated final artifact checks are outstanding.
