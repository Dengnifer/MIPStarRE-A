# Comparator verification of the headline theorems

Two challenges are configured, one per headline result: the LDT challenge
for `MIPStarRE.LDT.Test.mainFormal` and the QPBT challenge for
`MIPStarRE.QPBT.pauli_soundness` and `MIPStarRE.QPBT.pauli_soundness_qubit`.
They share the generation tooling in `scripts/comparator/`, the drift guard
and the trust model below; each lives in its own challenge repository.

## The LDT challenge

The headline theorem `MIPStarRE.LDT.Test.mainFormal` (the corrected source
statement of `thm:main-formal` from the low individual degree test paper) is
independently verifiable with the official
[leanprover/comparator](https://github.com/leanprover/comparator), the
top level of the escalating checks in the Lean reference manual's
[Validating Proofs](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
chapter.

Following community practice
([lamplighter-comparator](https://github.com/vidick/lamplighter-comparator),
[erdos-unit-distance-comparator](https://github.com/kim-em/erdos-unit-distance-comparator)),
the challenge lives in a separate repository —
**[LDT-comparator](https://github.com/LionSR/LDT-comparator)** —
which requires this library as a lake dependency pinned by commit:

- `Challenge.lean` there imports **only Mathlib** and re-declares, verbatim
  and in dependency order, every declaration in the comparator-relevant
  closure of the statement of `mainFormal` (111 declarations, ~1200 lines),
  then states the theorem with `sorry`.  It is the entire human audit
  surface.
- `Solution.lean` there imports this library, which proves the theorem under
  the same fully-qualified names; no bridging lemmas are needed.
- Its CI runs the comparator (real landrun sandbox, nanoda external kernel,
  `lean4checker` re-check) on every push and weekly.

## What this repository contributes

1. **Environment alignment.**  Comparator compares, constant by constant, the
   full kernel closure of the statement — types, definition bodies, and the
   proofs embedded in them — so `Challenge.lean` must elaborate to
   bit-identical terms.  Every module contributing a declaration to the
   closure therefore uses the full `import Mathlib` (directly or through
   `MIPStarRE/LDT/Basic/ParametersBase.lean` /
   `MIPStarRE/Quantum/FiniteMatrix/Basic.lean`), so tactic elaboration sees
   the same environment as the Mathlib-only `Challenge.lean`.  The four
   modules with direct Mathlib imports carry a comment saying not to narrow
   them.  (Measured impact: only 14 modules that did not already see full
   Mathlib through `Quantum/FiniteMatrix/Basic.lean` gained it.)
2. **Regeneration tooling.**  `scripts/comparator/` holds the closure
   extractor (a Lean metaprogram mirroring comparator's `runForUsedConsts`)
   and the assembler that produce `Challenge.lean`.  After changing any
   definition in the closure: regenerate per `scripts/comparator/README.md`,
   copy the result into LDT-comparator, and bump its library pin.

## Checklist against the official *Validating Proofs* guide

| Level | Requirement | Status |
|---|---|---|
| 2 | `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` | `MIPStarRE/LDT/Test/AxiomAudit.lean`; also enforced by comparator's `permitted_axioms` |
| 3 | `lean4checker --fresh` re-check | `lean4checker: true` in the comparator repo's lean-action step |
| 4 | Statement written in a trusted environment, separate from proof code | `Challenge.lean` imports only Mathlib (CI-enforced grep); separate repo, library pinned by commit |
| 4 | Sandboxed build + export + kernel replay | official comparator binary (pinned to the toolchain tag), real landrun in CI |
| 4 | External checker in addition to the Lean kernel | `enable_nanoda = true` (pinned nanoda tag); local macOS runs use `./verify.sh --fake-landrun` which disables it |
| 5 | No native evaluation (`Lean.trustCompiler`, `decide +native`) | excluded by `permitted_axioms` — comparator rejects any extra axiom |
| — | Statement review: custom notation and type classes must not obscure meaning | `Challenge.lean` uses no custom notation; review of it is the human step |

Deliberate deviations from the comparator README's adversarial setup, per its
own guidance for trusted trees: the `systemd-run` landrun-escape guard is
omitted and prebuilt `.lake` artifacts are reused, because both modules come
from a trusted checkout rather than an untrusted submitter.

Residual trust: Lean's logical soundness, comparator's own plumbing, sandbox
security, simultaneous bugs in all checkers, and human error in
`Challenge.lean` itself — keep that file short, notation-free, and reviewed.

## The QPBT challenge

The QPBT headline theorems `MIPStarRE.QPBT.pauli_soundness` (`thm:pauli`) and
`MIPStarRE.QPBT.pauli_soundness_qubit` (`cor:pauli-binary`) get the same
treatment, in the separate repository
**[QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator)**.

- **Targets.**  Both theorems are verified in one comparator run
  (`theorem_names` lists both), so the challenge re-declares the union of the
  two statement closures.
- **Closure size.**  190 declarations from twenty library
  modules, about 2700 lines — larger than the LDT challenge because the
  Pauli basis test carries the full question/answer combinatorics
  (`PauliType`, `PauliAnswer`, the win predicate and the question
  distribution) into the statement.
- **Generated file.**  `scripts/comparator/expected/ChallengeQPBT.lean.expected`,
  regenerated and byte-compared by the same drift guard as the LDT challenge
  (`--challenge qpbt`).

### Environment alignment for QPBT

Comparator compares the full kernel closure constant by constant, so the
Mathlib-only challenge file must elaborate to bit-identical terms.  Two
obstacles had to be removed in the library:

1. **Narrowed imports.**  Four closure modules —
   `MIPStarRE/QPBT/Algebra/Subspaces.lean`,
   `MIPStarRE/QPBT/Algebra/Coefficients.lean`,
   `MIPStarRE/QPBT/Algebra/LowDegreeCode.lean` and
   `MIPStarRE/QPBT/Algebra/Lines.lean` — imported individual Mathlib files, so
   tactic elaboration there saw a smaller environment than the challenge file
   would.  They now use the full `import Mathlib` and carry the same "do not
   narrow this import" comment as the LDT base modules.  The remaining sixteen
   closure modules already saw full Mathlib through
   `MIPStarRE/LDT/Basic/ParametersBase.lean` or
   `MIPStarRE/Quantum/FiniteMatrix/Basic.lean`.
2. **Private closure members.**  A `private` declaration's real name is
   qualified by its defining module (`_private.<module>.0.<name>`), so a
   challenge file in a different module can never re-declare it under the
   library's name.  Nineteen closure members were private — twelve in
   `MIPStarRE/QPBT/Algebra/FieldBasis.lean` (the self-dual normal basis
   construction that `fixedFieldModel` selects from), six in
   `MIPStarRE/QPBT/Algebra/Subspaces.lean` (the pivot-rank machinery behind
   `canonicalComplement`), and `singlePauliVec` in
   `MIPStarRE/QPBT/Algebra/Pauli.lean`.  Dropping `private` is the smallest
   faithful edit: no statement, definition body or proof script changes, only
   the visibility of names that the statement closure already depends on.

3. **Anonymous local instances.**  Two `local instance`s in
   `MIPStarRE/QPBT/Algebra/FieldBasis.lean` (the group and decidable-equality
   structure on the Galois group) are in the closure, and an anonymous
   instance receives a generated name that encodes its defining module, which
   a challenge file in another module cannot reproduce.  They now carry
   explicit names.

4. **The challenge mirrors the library's module partition.**  Lean caches an
   abstracted nested proof and a `match` auxiliary *per module* — the cache is
   keyed by the statement and the constant is named after whichever declaration
   of that module first needed it — and instance synthesis inside a module only
   sees what that module's imports declare.  A single-file challenge therefore
   cannot reproduce an auxiliary name whenever the library needs the same fact
   in two modules, and it makes every instance visible to every declaration.
   The QPBT challenge is consequently generated as one Mathlib-only module per
   contributing library module (`Challenge/MIPStarRE/...`, mirroring the source
   path), each importing the mirrors of the library modules that its source
   module imports, with `Challenge.lean` importing them all and stating the
   target theorems with `sorry`.  Every mismatch below was closed by that
   change alone; the generator takes the layout from `split=True` in
   `scripts/comparator/challenges.py` and writes it with
   `assemble_challenge.py --split-dir`, and the checked-in copy is the
   directory `scripts/comparator/expected/qpbt/`.

   With a single module, comparator reported 26 mismatching closure constants
   in three families: eight statement types and two proof terms in
   `FieldBasis`/`SelfDualBasis` that picked up `MIPStarRE.Quantum.instNeZeroTwo`
   (a module those files do not import in the library, so the library uses
   `@Nat.instNeZeroSucc 1` there); four definitions that shared
   `instReprPauliKind.repr.match_1` from `Algebra/Pauli.lean` where the library
   creates `pauliPointBlock.match_1` in `Test/PauliBasisTest.lean`; and twelve
   around `conjIsometry._proof_1`/`._proof_2`, which the library recreates as
   `applyOperatorToState._proof_*`, `eprState._proof_1`, `idealState._proof_2`
   and `idealQubitState._proof_2` in five different modules.  With the mirrored
   layout all 26 disappear and `./verify.sh --fake-landrun` reports
   `Your solution is okay!`.

   Because the partition alone is enough, the two named instances added for
   item 5 are no longer needed for acceptance;
   `MIPStarRE.Quantum.instRingHomInvPairIdComplex` in particular is never
   selected by synthesis (the goal carries the `RCLike`-derived `Semiring ℂ`
   path) and does not appear in the closure at all.  Removing them is a
   separate, rebuild-heavy change.

5. **Order-dependent auxiliary proofs.**  Lean lifts a *non-atomic* nested
   proof out of a definition's value into an auto-generated auxiliary
   constant, and names it after whichever declaration first needed it in that
   module.  Two facts in the closure are synthesized as non-atomic proof
   terms: `RingHomInvPair (RingHom.id ℂ) (RingHom.id ℂ)`, reached through
   `RingHomInvPair.ids`, and `NeZero 2`, reached through `Nat.instNeZeroSucc`
   and needed by `ZMod.fintype 2` behind the qubit alphabet.  The library
   spreads the declarations that need them over six modules and so produced
   five and three differently named copies of the same fact, while the
   generated challenge is a single module and produces exactly one — so
   `MIPStarRE.QPBT.qubitOperatorDistanceA` and `qubitOperatorDistanceB`
   referred to `MIPStarRE.QPBT.idealQubitState._proof_2` in the library and to
   `MIPStarRE.QPBT.qubitPauliProj._proof_1` in the challenge, and comparator
   rejected the pair.  Both facts now have explicit named instances,
   `MIPStarRE.Quantum.instRingHomInvPairIdComplex` and
   `MIPStarRE.Quantum.instNeZeroTwo`, in
   `MIPStarRE/Quantum/FiniteMatrix/Basic.lean` — the one module every affected
   declaration imports.  Synthesis now returns an atomic constant, so no
   auxiliary constant is generated on either side.

   The systematic check, if a further mismatch of this class appears: list
   every constant of both exported closures whose name contains `._proof_`,
   `.match_`, `._aux`, `._eq_` or `._simp_`, group them by statement *and*
   value, and give a named declaration to every group that has more than one
   member.  Groups with a single member are safe: the assembler emits a
   declaration before the declarations that depend on it, so a parent that
   owns exactly one copy regenerates the same auxiliary name on both sides.

No statement of either headline theorem changed, and their axiom closure
remains `propext`, `Classical.choice`, `Quot.sound`.

The "do not narrow this import" notes on the shared base modules
(`MIPStarRE/LDT/Basic/ParametersBase.lean`,
`MIPStarRE/LDT/Basic/Distribution.lean`,
`MIPStarRE/Quantum/FiniteMatrix/Basic.lean`) still name only `mainFormal`,
and deliberately so: those modules contribute to both closures, and adding a
line to a module docstring shifts every declaration below it, which would
rewrite the `-- source:` provenance comments of the checked-in LDT challenge.
They are covered by this section instead.

### Regenerating and auditing

Regeneration is the pipeline in `scripts/comparator/README.md` with
`--challenge qpbt`.  After an intentional change to any definition in the
closure: regenerate, copy the expected file into QPBT-comparator as
`Challenge.lean`, bump the `rev` pin in its `lakefile.toml` to the library
commit it was generated from, and run its `./verify.sh`.

What the human must audit, and what no tool can check: that
`ChallengeQPBT.lean` really states the intended theorems.  Concretely, that
the Pauli basis test it defines — `pauliQuestionDistribution`,
`pauliWinPredicate`, `pauliBasisTest` — is the test of the paper; that
`deltaQld` is the paper's error functional; that `PauliSoundnessWitness` and
`QubitSoundnessWitness` package isometries and an auxiliary state without
smuggling in a hypothesis; and that `Strategy.value` and the operator
distances mean what their names claim.  Everything else in the file is
machine-checked to agree with the library.

## Benchmark use

The same statement is submission-ready for
[leanprover/lean-eval](https://github.com/leanprover/lean-eval) (the official
comparator-based benchmark behind [lean-lang.org/eval](https://lean-lang.org/eval/)):
port the statement module to lean-eval's toolchain, tag the theorem
`@[eval_problem]`, add a `manifests/problems/<id>.toml` (`holes`, `submitter`,
`source`, `informal_solution`), and open a PR to lean-eval.  Large
self-contained statement preludes have precedent there (the knot-theory
problems ship a 23 KB trusted `ChallengeDeps.lean`).  Solvers edit only
`Submission.lean`; scoring is comparator acceptance, with submissions run by
the Lean FRO's hosted pipeline.
