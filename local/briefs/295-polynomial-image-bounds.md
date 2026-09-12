# Issue295: publish preserved ordered polynomial-image bounds

Base: published main `1c223a5f5b2f5c0af9483cc99b6d3771a3385bdc`.
Prerequisite: closed issue #49, the core distance calculus.

Recover the 21 already-proved public declarations in the preserved issue118
PolynomialImageBounds module using current public APIs. Their statements and
mathematical calculations remain unchanged. Add the aggregate import and one
explicitly auxiliary ordered-correlation blueprint statement.

The source is QPBT analysis lines 1289-1320, particularly `eq:qld-g-prime` and
the argument leading to `eq:qld-g-prime-bound`. The actual ordered-correlation
error remains in the conclusion. Do not construct a global-pair witness,
derive a new cross-register transport, or mark unrestricted `lem:qld-4-7`
complete. Stop if public-API adoption needs a new mathematical construction.

This is a publication task, not another B8 attempt. B8 remains at 13 attempts
and 26509 working seconds. Preserve issue118, its source, private artifacts,
gap notes, and all cumulative budgets without mutation.

Validate all 21 axiom closures against current public-source artifacts,
type-check the module and aggregate, compare declaration headers to the
preserved file, render/check the auxiliary blueprint, and use normal hooks
and checked publication. CI, independent review, and daemon merge remain
separate gates. Primary telemetry remains root-owned; setup output is buffered.
