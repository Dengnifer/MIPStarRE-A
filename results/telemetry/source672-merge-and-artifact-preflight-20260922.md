# Source Corrections Merge and Artifact Preflight

The previous goal turn made progress: issue679 was created, the packaging
preflight started, and genuine independent approval5271281096 at exactc9c0b456
was gated for a standalone service merge.

## Verified Merge

GitHub reports PR672 merged at2026-09-21T20:05:34Z as
392b550d613cdb09ccce95c8491f60cc194cb6eb. Main independently checked the API and
the merge's second parent c9c0b456f7461dac3996d827db62b5c270a854c9. The daemon
reported completion20:06:03Z; these are distinct observation timestamps.
The main/remote records settled cleanly at
dcffa512505ab7f3d76db52ee718aa5933f81476. No train or manual merge was used.

The completion gate atdcffa512 returned expected exit1:
C1PASS333QPBTfiles/no sites; C3FAIL11of21rows nonterminal, down from13;
C4FAIL7of528linked nodes; C5FAIL because PR677's record is not merged;
C6PASS only its narrow one-document open-site check; C2/C7remain delegated.
This is not a source-faithfulness or overall completion certificate.

## Actual Packaging Evidence

At frozen73c493c8638a098043733205fe6f155dc6d733d1 the model-free wrapper
/tmp/main-artifact-preflight-20260922.sh finished20:06:21Z with exit0.
The authored archive has956files,673Leanfiles,49built gap-note PDFs whose text
was scanned, and339pruned LaTeX intermediates. Both authored and anonymized
no-PDF variants passed leak scans and internal Lean import resolution.

- Authored SHA256:
  abe7dec8f285dae88b9661aff7e7f2d80f6304d05e74d4a46451982eee003852
- Anonymized no-PDF SHA256:
  d94aaf0e8a024e4851c86f6f8dae85782077fb604030e21858d0a35030a07936
- Logs/manifests and retained unpacked trees:
  /tmp/main-artifact-preflight-20260922-output and the wrapper's .log/.exit.

Both manifests still report2deadlinks of198checked: the gap register links to
excluded local/protocols/completion.md and issues-prs.md. The2missing paper
locators remain references/ldt-paper/commutativity_points.tex and
references/ldt-paper/projectivization.tex. Issue679's prepared brief now names
the actual findings; old guide text misidentifies the dead links. These results
predate PR672 and are intermediate packaging evidence, not a final-tree build.

Main starts /tmp/main-post672-comparator-drift-20260922.sh as a separate
model-free check of the newly merged source. It compares regenerated output,
never updates expected fixtures, and guards against concurrent source changes.
No new official comparator run is claimed.

The first primary-checkout drift run failed with regenerated pre671 private
declarations. Its log is retained, and no fixture was updated. In contrast,
the complete CI672 build log1609-1611 already reports both challenges current,
including all31QPBTfiles. Main verified no source/comparator/toolchain diff
between that frozen clean c9c0b456 worktree and merged dcffa512. The diagnostic
/tmp/main-post672-frozen-drift-20260922.sh rechecks this already-built tree to
distinguish stale primary build products from an actual source change.

PR669's third code phase requests three fixes, while its prose phase remains
live. No writer is admitted to its worktree. Prepared packet
/tmp/main-fix669-third-review-prepared-20260922.md retains the full round count,
requires the final combined review, and names PR677's service merge as the
canonical comparator-record integration dependency. Only one further full
review is available under the ordinary four-round cap.

## Review Admission

PR675's first hard-review admission ended after1800s waiting with exit4,
account capacity exhausted, no reservation and no model invocation. Original
CI and failure logs are retained. Main restarts only the review transport in
/tmp/main-review675-admission-retry-20260922.sh, with the same first-review
1200s Astra/ultra budget and a3600s account wait. The cpa cap remains2, with no
key fallback or budget reset. Existing669code/prose phases are live under the
canonical parallel review tool; queued673/677repairs are unchanged.
