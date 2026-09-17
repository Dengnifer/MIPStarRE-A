# Failed completed line-evaluation mass

Issue #332 is a formalization-only auxiliary under #119, stacked on the
completed same-line readout API from #321. It bounds each player's marginal
Born mass of the completed line readout `none` by the corresponding mixed
line/point rejection branch, for both axis and diagonal questions.

The syntactic event inclusion is not valid for every answer pair because a
wrong-format point answer also reads as `none`. The proof uses the actual
constructed strategy: those point-answer effects, and hence their joint Born
weights, vanish. After removing that zero-mass branch, line `none` is paired
with point `some` and is contained in the completed-read mismatch event.

No line projectivity, nonzero-direction assumption, strategy symmetry, or
additional source hypothesis is used. The packet does not identify parameter
evaluation with completed `Option` evaluation and does not prove coefficient
collision or the full passing-value theorem.
