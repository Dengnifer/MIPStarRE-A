---
pr: 0001
kind: prose
branch: issue-0002-qpbt-blueprint
base: main
merge_base: c744e92a45536cb074e51741191dbf5355147ae0
head_sha: cf4cfa6eb26ad593c4e130d033b54e6a455a1ae1
verdict: CHANGES_REQUESTED
review_state: CHANGES_REQUESTED
session: reviewer-pr0001-20260830-06
model: (dispatcher default)
generated: 2026-08-30T11:22:04Z
---

# Prose review — PR 0001 @ cf4cfa6eb26a

Local replacement for the `prose-review` job of `.github/workflows/pr-review.yml`.

## Findings

Checkbox states: `[ ]` unresolved (blocks the merge), `[x]` resolved,
`[-]` outdated (the cited lines were rewritten; does not block).

<!-- findings:begin -->
- [-] F1 (changes) `blueprint/src/chapter/ch13_qpbt_test.tex:27` — Game notation drifts from the source’s `\mathfrak G` and changes again across Chapters 14 and 16.  <!-- outdated at 4277943db23d2dde26e90908ede8041fb7902e36 -->
- [-] F2 (changes) `blueprint/src/chapter/ch14_qpbt_observables.tex:101` — The symbol `n = 2^m` silently renames the source and surrounding chapters’ quantity `M = 2^m`.  <!-- outdated at 4277943db23d2dde26e90908ede8041fb7902e36 -->
- [-] F3 (changes) `blueprint/src/chapter/ch14_qpbt_observables.tex:373` — “The strategy under analysis” fixes standing data and invokes Naimark dilation but is incorrectly presented as a definition.  <!-- outdated at 4277943db23d2dde26e90908ede8041fb7902e36 -->
- [-] F4 (changes) `blueprint/src/chapter/ch16_qpbt_extraction.tex:28` — Pointwise decoder–encoder equality does not characterize encodings when `d ≥ q`.  <!-- outdated at 4277943db23d2dde26e90908ede8041fb7902e36 -->
<!-- findings:end -->

## Review

F4 is the substantive mathematical issue. For the admissible tuple \((q,m,d)=(8,1,8)\), take \(g(x)=x^8\). This polynomial representative is not multilinear and hence is not an encoding, but \(\mathrm{Dec}(g)=(0,1)\), so
\[
\mathrm{Dec}(g)\cdot\mathrm{ind}_1(u)=u=u^8=g(u)
\]
for every \(u\in\mathbb F_8\). Thus the claim that the identity “holds exactly when \(g\) is an encoding, and fails otherwise” is false. Line 20’s assertion that the two sides are distinct as functions is false for the same reason. State instead that \(g_{\mathrm{Dec}(g)}=g\) as polynomial representatives exactly for encodings, while their induced functions may agree for nonencodings when \(d\ge q\).

For F1, the source defines `\game` as `\mathfrak{G}` and consistently uses it for the low-degree, Magic Square, and Pauli games. Chapter 13 uses `\mathcal G`, Chapter 14 uses bare `G`, and Chapter 16 returns to `\mathfrak G`; bare \(G\) also conflicts with the notation for type graphs. Standardize the games as \(\mathfrak G^{\mathrm{ld}}\), \(\mathfrak G^{\mathrm{MS}}\), and \(\mathfrak G^{\mathrm{Pauli}}\), reserving \(G\) for graphs.

For F2, the source’s `\nqubits` expands to \(M\), and Chapters 13 and 16 likewise use \(M=2^m\). Either use \(M\) throughout Chapter 14 or explicitly introduce \(n=M=2^m\) and identify \(M\) as the source notation.

For F3, the corresponding source passage is ordinary setup prose. The block introduces no mathematical object: it fixes parameters and a strategy, then applies the already cited Naimark theorem. Replace the definition environment with an unnumbered standing-setup paragraph and update references that currently call it a definition.

The sole changed-chapter `\lean`/`\leanok` link, `MIPStarRE.Quantum.Measurement.postprocess`, is accurate: arbitrary outcome relabeling, fiber summation, and completeness agree with the blueprint statement. Its finiteness and decidable-equality assumptions are faithful boundary conditions. There are no stale `\notready` tags or newly changed Lean declarations requiring status updates. The Schwartz–Zippel restatement correctly remains unlinked because its reduced polynomial-function formulation does not match the existing theorem’s public `MvPolynomial` signature.

No new banned-language or Lean-jargon findings were found. Previously raised feedback was not duplicated. Count: 4 category-A findings, 0 status-tag errors, 0 new category-B findings.

## Verdict

VERDICT: CHANGES_REQUESTED
