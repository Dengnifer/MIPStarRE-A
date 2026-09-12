# Restore the Domain of Subline Claim 17-2

Issue #414 corrects the constructed measurement used by paper `claim:17-2`.
The new branch starts at PR #400 and merges the published PR #398 constructor dependency.

The mathematical obstruction and correction are in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`; the statement comparison is in
`audits/2026-09-09-subline-claim2-domain-repair.md`.

The source claim uses `S.combinedLineMeasurement` and keeps its original error bound.
The combined-line existence proofs retain that concrete measurement internally, with the
unfinished consistency estimate named explicitly. The abstract witness record is unchanged.
No concrete marginal proof or full pasting proof is included.

The author is session `01a081c4-16db-7613-88c5-c2f1f5030d2d`; independent review must use
another session. The earlier audit and issue #405 proof attempt remain separate records.
