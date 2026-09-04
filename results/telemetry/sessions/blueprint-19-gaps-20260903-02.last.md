## In sync

- `lem:qld-constructing-the-paulis-helper` already depended on `def:expanded-point-measurement` at `22afbcbb`; preserved unchanged.
- No Lean links, `\leanok` markers, Lean sources, or issue #18 material changed.

## Drifted

No remaining dependency drift in this unit. `lem:qld-construct-the-paulis` now uses `def:approx-question-indexed-operators` instead of the answer-indexed `def:povm-distance`.

## Mathematically suspect

The new notes document:

- The quoted linearity theorem’s pointwise-versus-averaged quantifier mismatch.
- The false unrestricted decoding identity and required non-encoding-mass reduction.
- The false cross-basis commutation claim and corrected trace phase.
- The extraction proof’s triangle/normalization errors and missing range-projection transfer.

## Changed

Added four notes under [docs/paper-gaps](/tmp/mipstarre-19-gaps/docs/paper-gaps), the Natarajan–Vidick citation in [references.bib](/tmp/mipstarre-19-gaps/docs/paper-gaps/references.bib), and corrected the dependency in [ch16_qpbt_extraction.tex](/tmp/mipstarre-19-gaps/blueprint/src/chapter/ch16_qpbt_extraction.tex:106).

Committed as `c4e708725ade2e29b898260429f4ac8d6add51ec` with subject `docs(QPBT): record extraction proof gaps` and body `Addresses #19`.

## Evidence

- Four standalone note PDFs: passed without LaTeX warnings.
- `leanblueprint web`: passed; existing missing-bibliography warnings remain.
- `lake exe checkdecls blueprint/lean_decls`: all 1,017 declarations resolved.
- Paper-gap and blueprint style checks: passed.
- Line-length and `git diff --check`: passed.
- Pre-commit hooks: passed.
- No Lean checks or full build were needed because no Lean files or declaration links changed.
- Worktree is clean and ahead by one commit. No PR opened or integration performed.