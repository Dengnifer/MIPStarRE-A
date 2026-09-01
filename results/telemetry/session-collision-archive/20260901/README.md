# Session name collision recovery

The primary checkout and the issue-0007 worktree independently allocated
`scout-0007-final-closure-audit-20260901-01` during bootstrap of the repaired
resume command. These directories preserve the two pre-recovery bundles.

- `primary/` contains the failed zero-event capture and its original registry
  row.
- `feature/` contains the successful capture, final message, and original
  registry row, all under the originally allocated `-01` name.

The canonical session registry keeps the primary failure as `-01` and records
the byte-identical successful capture as `-02`. No source capture or original
registry row was overwritten.
