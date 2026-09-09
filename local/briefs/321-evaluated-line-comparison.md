# Completed same-line evaluation comparison

Issue #321 is a formalization-only auxiliary under #119, stacked directly on
the point/point rejection bound from #313. The source calculation is the
consistency triangle from
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:389-395`, applied to
the completed line and point reads used in the proof of `lem:qld-4-7` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`.

For each axis and diagonal line kind, the packet compares Alice's and Bob's
same-line completed reads through Bob's and Alice's point reads. The three
edges of the comparison are exactly the corresponding line/point,
point/point, and reversed point/line rejection probabilities. The point edge
is transported over the full jointly uniform direct sample by an explicit
point-first equivalence and uniform marginalization.

The resulting bound is
`B(t, point) + 2 * sqrt (B(point, point) + B(point, t))`, followed by the
supplied-witness estimate
`2 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`. No projectivity of the line
POVMs is assumed: the applicable consistency triangle holds for arbitrary
complete measurements.

The evaluated defect uses completed `Option`-valued readouts. Agreement on
`none`, especially for zero line directions, is not coefficient equality and
is not hidden by this packet. The result neither proves coefficient collision
nor constructs a witness or establishes the full passing-value theorem.
