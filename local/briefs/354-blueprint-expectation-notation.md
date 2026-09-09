# Issue 354: QPBT blueprint expectation notation

## Scope

Repair the four undefined `\Exp` commands in
`blueprint/src/chapter/ch12_qpbt_games.tex`. The change is notation-only: every
mathematical statement, proof, label, citation, and Lean reference remains
unchanged.

## Source

The primary paper defines expectation notation as `\E` in
`references/qpbt-paper/00_preamble.tex` and uses it throughout
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`. The blueprint
likewise defines `\E` in `blueprint/src/macros/common.tex`; it does not define
`\Exp`.

Each affected expression is explicitly an average or expectation. Replacing
`\Exp` with the existing `\E` therefore restores the established notation
without changing the meaning of the displayed formulas.

## Validation

- Run a fresh, noninteractive PDF build with XeLaTeX and halt-on-error enabled.
- Verify the actual `latexmk` exit code and reject a nonempty partial PDF.
- Run the blueprint web build.
- Confirm that the source diff consists only of the four command substitutions
  and this brief.
