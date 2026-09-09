# PR 481: corrected review repair

The repair starts from `52aa00886e76ed4a257383a7c203807e32aa68be` and addresses
corrected CODE request `7045592309d64a7aac65556849e59b1b` and PROSE request
`d31cebca1a2d4a1080e79bda95788681`, each excluding all 16 prior authors.
The earlier requests with incomplete author exclusions provide no review evidence.

## Statement integrity

The source is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.

| Result | Paper Assumptions | Lean Assumptions | Paper Conclusion | Lean Conclusion | Verdict |
| --- | --- | --- | --- | --- | --- |
| Claim 17-1, lines 1140-1166 | Projective setting, preceding point and paired-line measurements, source subline law | Unchanged setting and point/line witnesses; directly indexed subline witness | Complex overlap difference of order sqrt(deltaQ) | Absolute difference of real parts with the same error order on the auxiliary law | Auxiliary carrier; weaker scalar conclusion |
| Claim 17-2, lines 1168-1201 | Projective setting, concrete X-Z-X line measurement, source subline law | Unchanged setting and directly indexed subline witness; concrete sandwich in the conclusion | Complex ordered-to-Z overlap difference of order m sqrt(deltaLine) | Real-part difference with the same error and concrete measurement on the auxiliary law | Concrete scalar proof complete; source scalar/carrier correspondence pending |
| Claim 17-3, lines 1204-1239 | Setting and preceding point/line measurements, source subline law | Unchanged point/line witnesses and directly indexed subline witness | Z overlap close to one with the stated fourth-root error | Corresponding real-part estimate on the auxiliary law | Auxiliary carrier; source correspondence pending |
| Combined points, lines 689-709 | Admissible parameters and passing projective strategy | Unchanged projective setting | Projective joint measurements with self-consistency, both ordered-product comparisons and symmetric equivalents | The same comparisons on all four directed placements, with a universal polynomial error | Faithful contextual encoding; proved on the original expanded spaces |

All non-comment tokens in `Claims.lean` were compared with the frozen source
and are identical: the public hypotheses, universal quantifiers, conclusions,
and all three proof bodies are preserved. The concrete X proof is unchanged.
No proof hole, axiom, hypothesis, or bypass is introduced. The source scalar
claims remain pending, and separate auxiliary blueprint entries record exactly
the directly indexed law, completed evaluations, and real-part conclusions.

The point constructor's blueprint proof now follows field-valued approximate
commutation by Parseval, the Z-X-Z sandwich POVM, orthonormalization on the
original spaces, and squared-distance triangle inequalities. Its source-shaped
statement is unchanged. The original binary-refinement argument is retained as
a distinct explanation, with its ancilla absorption still explicitly open.

The concrete paired-line consistency theorem remains unfinished. Closing the
C2 scalar calculation does not discharge that theorem, the source extended-line
distribution transport, or the complex scalar comparisons. Their status and
future proof targets are recorded in
`docs/paper-gaps/qpbt_subline-claims-line-marginal.tex`.

## Placement compatibility

`Points/PlacementSupport.lean` now imports and re-exports
`Points/Placement.lean`, eliminating duplicate public definitions. The latter
supplies both placed-measurement algebra and EPR exchange. The placement/product
reuse repair at `9122293b` also imports this canonical module; no sibling branch
or unrelated implementation is merged into this repair.

The remaining prose corrections distinguish the Parseval coefficient columns,
preceding zero blocks from later untruncated blocks, ambient-point fibers from
their fixed canonical representative, and Z-deficit specializations from the
separate concrete X argument. They change no Lean declarations.

## Validation

The focused Claims, point-constructor, and compatibility-module build passes.
Both placement import orders elaborate. Axiom inspection of all three scalar
claims, the point constructor, the subline constructor, and the placed
measurement reports only `propext`, `Classical.choice`, and `Quot.sound`.
The separate concrete paired-line consistency theorem retains `sorryAx`, as
recorded in the gap note.

The source-header integrity check and exact non-comment Claims comparison
pass. Blueprint rendering after bibliography generation has no warning or
error lines; synchronization and all 1661 declaration links pass. The global
blueprint axiom audit finds no proof-level completion marker depending on
`sorryAx`. LaTeX conventions, paper-gap style/reference checks and whitespace
checks pass. The gap note compiles to PDF.
