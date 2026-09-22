# Comparator verification of the headline theorems

Two challenges are configured.  The LDT challenge targets
`MIPStarRE.LDT.Test.mainFormal`.  The QPBT challenge targets the four registered
QPBT results: `MIPStarRE.QPBT.exists_spcc_value_one`,
`MIPStarRE.QPBT.exists_ld_soundness`, `MIPStarRE.QPBT.pauli_soundness`, and
`MIPStarRE.QPBT.pauli_soundness_qubit`.  They share the generation tooling in
`scripts/comparator/`, the drift guard, and the trust model below; each lives in
its own challenge repository.

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

The QPBT challenge is prepared for the separate repository
**[QPBT-comparator](https://github.com/Dengnifer/QPBT-comparator)**.  Its current
configuration supplies these four theorem names to one comparator run:

- `MIPStarRE.QPBT.exists_spcc_value_one` (`lem:pauli-completeness`);
- `MIPStarRE.QPBT.exists_ld_soundness` (`lem:ld-soundness`);
- `MIPStarRE.QPBT.pauli_soundness` (`thm:pauli`); and
- `MIPStarRE.QPBT.pauli_soundness_qubit` (`cor:pauli-binary`).

The checked-in generated tree is `scripts/comparator/expected/qpbt/`.  It has a
root `Challenge.lean` and thirty Mathlib-only mirror modules under `Challenge/`,
one for each contributing library module.  The root states all four targets
with `sorry`; the drift guard regenerates and byte-compares the complete tree
with `--challenge qpbt`.

### Current verification status

On September 21, 2026 UTC (September 22, 2026 JST), official comparator
[run 35638601720](https://github.com/Dengnifer/QPBT-comparator/actions/runs/35638601720)
([job 106462118372](https://github.com/Dengnifer/QPBT-comparator/actions/runs/35638601720/job/106462118372))
completed successfully at QPBT-comparator commit
`360402fdf4a39399f94331452d6e5d0a35c144be`.  Both `lakefile.toml` and the
manifest's `rev` and `inputRev` pinned library commit
`ecb97d1f66eec1e6fad964f144f78b91ce1fab36`, the merged-main result of PR 671.
The run's configuration named all four targets above, enabled nanoda, and
permitted exactly `propext`, `Quot.sound`, and `Classical.choice`.
Preliminary run 35621468975 at unmerged library commit
`a3683e9b75da4aeb52174af2cccacfde606361ce` is not evidence for this record.

The workflow used Lean `v4.32.0` and the official comparator tag at
`07bc4ea40f2266dcb861820a2ec1fa3244ed307f`, with landrun pinned at
`c91b41ac6cb180e2fdcb989408dcde34449bd8b0` and nanoda pinned at
`f58f2f6d535e189a40fcb02ede8eb95f97a92d37`.  It invoked `./verify.sh` without
`--fake-landrun`, required the real `landrun` executable, and ran
`lake env comparator comparator.json`.  The retained log exports all four
theorem names from both `Challenge` and `Solution`, then records that the nanoda
kernel and Lean's default kernel each accept the solution.  This establishes
equality of the complete union of the four statement closures at the verified
library commit.  Before that run, PR 671 either eliminated the earlier private
and compiler-generated blockers from the closure or made the affected closure
declarations public.  The successful comparison verifies the resulting current
closure; it did not compare those former blockers under their old names.

The completion gate reads the following record.  For an exact-head QPBT
completion claim, C5's delegated evidence must include a passing drift check
from CI on that same commit; carrying this documentation record alone does not
select the comparator build step.

<!-- completion-gate: track=qpbt -->
- challenge-repository: https://github.com/Dengnifer/QPBT-comparator
- verified-library-commit: ecb97d1f66eec1e6fad964f144f78b91ce1fab36
- expected-challenge: scripts/comparator/expected/qpbt
- drift-check: scripts/comparator/check_challenge_drift.py
- covered-theorems: MIPStarRE.QPBT.pauli_soundness, MIPStarRE.QPBT.pauli_soundness_qubit, MIPStarRE.QPBT.exists_spcc_value_one, MIPStarRE.QPBT.exists_ld_soundness

Comparator acceptance is a closure-equality result, not a source-faithfulness
certificate.  It does not prove that the trusted challenge faithfully states
the QPBT paper, settle completion criteria C3 or C4, perform the final artifact
build, or establish that the QPBT track is complete.  Any later change to the
statement closure requires regeneration, a passing drift check, and a new
official comparator run before this verification claim can be advanced.

There is a narrower historical result.  At commit
`4aec9ebedf6ca401e3f2d7b4bd90bd565d38f90d`, the split challenge configured
only `MIPStarRE.QPBT.pauli_soundness` and
`MIPStarRE.QPBT.pauli_soundness_qubit`.  On that exact two-target configuration,
`./verify.sh --fake-landrun` reported acceptance.  Fake landrun disables nanoda,
and that run did not include `exists_spcc_value_one` or `exists_ld_soundness`, so
it is not evidence for the current four-target challenge.

### Environment alignment for QPBT

Comparator compares the full kernel closure constant by constant, so each
Mathlib-only challenge module must elaborate to bit-identical terms.  The
library and generator use the following alignment measures:

1. **Full Mathlib imports.**  Four closure modules -
   `MIPStarRE/QPBT/Algebra/Subspaces.lean`,
   `MIPStarRE/QPBT/Algebra/Coefficients.lean`,
   `MIPStarRE/QPBT/Algebra/LowDegreeCode.lean`, and
   `MIPStarRE/QPBT/Algebra/Lines.lean` - use the full `import Mathlib`, so tactic
   elaboration sees the same environment as the challenge modules.  Other
   closure modules receive Mathlib through existing shared imports.
2. **Public closure members.**  A `private` declaration's real name is qualified
   by its defining module (`_private.<module>.0.<name>`), so a challenge module
   cannot re-declare it under the library's name.  Closure members needed by the
   challenge were therefore made public without changing their statements,
   bodies, or proof scripts.
3. **Named local instances.**  The group and decidable-equality instances for
   the Galois group in `MIPStarRE/QPBT/Algebra/FieldBasis.lean` have explicit
   names.  This avoids generated names that encode the defining module.
4. **Mirrored module partition.**  Lean caches nested proof and `match`
   auxiliaries per module, names them after the first declaration in that module
   that needs them, and limits instance synthesis to the module's imports.  The
   QPBT challenge therefore mirrors the source module partition and import
   graph.  This behavior is selected by `"split": true` in
   `scripts/comparator/challenges/qpbt.json`; `assemble_challenge.py --split-dir`
   writes the tree under `scripts/comparator/expected/qpbt/`.

The split layout also avoids adding QPBT-specific global instance wrappers to
`MIPStarRE/Quantum/FiniteMatrix/Basic.lean`.  The original LDT challenge bytes
are protected independently by the baseline regression described in
`scripts/comparator/README.md`.

No public statement of any of the four targets changed as part of this
comparator alignment.  The official run above established comparator equality
for the verified merged-main library commit.

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
`Challenge.lean` and `Challenge/`, bump the `rev` pin in its `lakefile.toml`
and `lake-manifest.json` to the library commit they were generated from, and
run its `./verify.sh`.

What the human must audit, and what no tool can check: that the challenge
modules really state the intended theorems.  Concretely, that
the Pauli basis test it defines — `pauliQuestionDistribution`,
`pauliWinPredicate`, `pauliBasisTest` — is the test of the paper; that
`deltaQld` is the paper's error functional; that `PauliSoundnessWitness` and
`QubitSoundnessWitness` package isometries and an auxiliary state without
smuggling in a hypothesis; and that `Strategy.value` and the operator
distances mean what their names claim.  Agreement of the remaining declarations
was established by the four-target comparator run above; their intended
mathematical meaning and agreement with the cited paper remain matters for
source comparison and review.

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
