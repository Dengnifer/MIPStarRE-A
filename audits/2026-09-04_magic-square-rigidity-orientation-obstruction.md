# Magic Square Rigidity Orientation Obstruction

Date: 2026-09-04.

## At a glance

Issue #104 asks for the swap-isometry extraction used by
`MIPStarRE.QPBT.exists_ms_rigidity`.  The local controlled-swap calculation is
sound, but its specialization is blocked by a mathematical mismatch between
the one-way linear constraint system self-test cited by the source and the
symmetric Magic Square game formalized in this repository.  The formal game
samples both orientations of every constraint-variable edge and does not
sample any same-question self-loop.  Consequently, an arbitrary strategy may
play the two orientations on independent entangled copies.

This is not an absent Mathlib lemma.  It is a counterexample mechanism at
error zero.  Completing the requested joint state extraction and all four
variable-effect transports would therefore require a hypothesis or a game
condition which is absent from the source-labelled statement.

## Key theorem forms

The cited one-way LCS self-test of Coladangelo--Stark has equation observables
on Alice and one variable observable for each variable on Bob.  Its exact
form identifies those two families with one ideal representation and an EPR
state.

The QPBT statement `thm:ms-rigidity`, at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
uses the symmetric type graph.  It asks for a single pair of local isometries
which simultaneously extracts two EPR pairs and transports the distinguished
variable effects of both Alice and Bob.  The Lean declaration
`MIPStarRE.QPBT.exists_ms_rigidity` has the same conclusion for every
`Strategy msGame`.

The missing implication is therefore

```text
success on both oriented constraint-variable tests
  => Alice's variable representation is paired with Bob's variable representation.
```

Neither the question distribution nor the current hypotheses impose this
pairing.

## The two-copy strategy

Let the standard perfect Magic Square strategy act on a local space `K`, with
maximally entangled state `Omega` and its usual constraint and variable
measurements.  Give each player two copies of `K` and use the reordered state

```text
Omega_(A1,B1) tensor Omega_(A2,B2).
```

Define the measurements by roles:

| question received | Alice acts on | Bob acts on |
|---|---:|---:|
| constraint | copy 1 | copy 2 |
| variable | copy 2 | copy 1 |

When Alice receives a constraint and Bob receives a variable, their answers
come from the first perfect copy.  In the reverse orientation their answers
come from the second perfect copy.  Thus every ordered pair in
`graphDistribution msEdges msEdges_nonempty` is won with probability one.
The unused tensor factor may be measured trivially.

The support fact is visible directly in the definitions.  `msEdges` contains
only the 18 constraint-variable incidence edges, while `graphDistribution`
is uniform on all ordered endpoint pairs whose unordered pair is an edge.
The blueprint says the same at `ch13_qpbt_test.tex:219`: the verifier sends the
two endpoints to a uniformly random assignment of the players and there are no
self-loops.  Although `msWinPredicate` has clauses for identical constraint or
variable questions, those clauses have zero probability in `msGame`.

## Contradiction with zero-error extraction

In the two-copy strategy, Alice's distinguished variable observables act on
`A2`, whereas Bob's distinguished variable observables act on `B1`.  The
reduced state on `A2 tensor B1` is a product of maximally mixed states.  In
particular, for either traceless distinguished ideal reflection, the
Alice--Bob correlation is zero.

Set `epsilon = 0` in `exists_ms_rigidity`.  Every displayed upper bound then
vanishes.  Exact state extraction identifies the transformed state with two
ideal EPR pairs tensored with the auxiliary state.  Exact transport of both
players' variable-0 effects identifies their binary observables with the same
ideal Pauli `X` reflection on the first extracted qubit.  That ideal
Alice--Bob correlation on the EPR state is one.  Local isometries preserve the
correlation of the original observables on the original state, contradicting
the zero correlation above.  The variable-4 `Z` effects give the same
contradiction.

This argument uses only the state conclusion and the Alice/Bob effect
conclusions at zero error.  Approximate anticommutation on each local side,
including `msVarObsA_anticommute` and `msVarObsB_anticommute`, does not address
the obstruction: both independent copies have exact local anticommutation.

## Source comparison

Coladangelo--Stark's definition in
`references/cs-paper/self-testing.tex:669-689` compares Alice's equation
observable with Bob's variable observable in the ordinary one-way LCS game.
The Magic Square specialization in
`references/cs-paper/specific-games.tex:111-135` uses that convention.  It
does not assert the four-variable-family conclusion for the role-symmetric
game above.

The QPBT source imports that theorem after changing the game to a symmetric
presentation.  The value-preserving symmetrization construction at
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:94-130` does not
repair the problem: it puts the original `A` and `B` measurements in different
role-register blocks but supplies no consistency between an untested
same-question pair.  Applied to the two-copy strategy, it preserves both the
perfect value and the separation of the two variable representations.

## Verdict and repair boundary

The requested specialization of the swap extraction is blocked by a false
zero-error implication for the current `msGame`/`Strategy` interface.  Adding
an Alice--Bob variable-agreement assumption to a helper consumed by
`exists_ms_rigidity` would be a load-bearing non-paper hypothesis and is
forbidden by the faithful-formalization policy.

A source-level decision is required before the rigidity theorem can be closed.
Mathematically coherent options include using the original one-way LCS game,
adding consistency self-loops to the symmetric game, or explicitly restricting
the theorem to strategies with the required same-question consistency.  The
latter two options change the theorem or the game and must not be applied
silently.  The generic controlled-swap isometry remains valid and reusable
once a faithful interface supplies the missing cross-player pairing.
