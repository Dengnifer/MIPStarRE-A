# Reports

Dated reports written during the development: audits, investigations,
verification runs, post-mortems. One file per report, named
`<yyyy-mm-dd>_<slug>.md`.

**Empty so far.** The directory exists from the first day because tools scan it
(`scripts/audit_paper_facing_proof_debt.py` reads it, and the artifact packaging
excludes it), and because a report written into a chat window is a report that
is lost.

Conventions:

- **Append-only.** A report is a record of what was found at a date. Correct it
  with a dated note at the bottom, never by rewriting it.
- Lead with the finding, then the evidence, then what was done about it.
- Name the commit the report was made at.
- Reports are excluded from the artifact snapshot. They are development
  records, not part of the mathematics.
