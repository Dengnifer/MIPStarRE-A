#!/usr/bin/env python3
"""Per-challenge configuration for the comparator challenge generators.

One entry per comparator challenge: the target theorems whose statement
closure is extracted, the header/footer that frame the generated file, the
checked-in expected copy, and the elaboration context that the kernel closure
cannot see.

The extractor (`extract_closure.lean`) is shared and selects its roots from
the `COMPARATOR_TARGETS` environment variable; `assemble_challenge.py` and
`check_challenge_drift.py` select the rest from here with `--challenge`.
Adding a challenge means adding an entry, a header, a footer, and a CI drift
step — no generator code changes.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path

# extra context commands needed for re-elaboration but absent from the kernel
# closure (attributes, CoeFun instances that elaboration unfolds), keyed by the
# declaration after which they must appear
Extras = dict[str, list[str]]

LAST_LINE = 10**9


@dataclass(frozen=True)
class Prelude:
    """Elaboration context of one source scope of one module.

    `opens`/`variable`s/`local notation` that the declarations of a source
    section were elaborated under, replayed around the snippets taken from
    lines `first`..`last` of that module.  A module needs one `Prelude` per
    section whose context differs — the self-dual normal basis file, for
    instance, has a group-algebra section and a trace-dual section that bind
    the same identifier to different things.
    """

    ns: tuple[str, ...]
    lines: tuple[str, ...]
    first: int = 1
    last: int = LAST_LINE
    # source section opened with `noncomputable section`: definitions inside
    # it carry no `noncomputable` keyword of their own and do not re-elaborate
    # outside such a section
    noncomputable: bool = False

    @property
    def whole_file(self) -> bool:
        return self.first == 1 and self.last == LAST_LINE

    def covers(self, line: int) -> bool:
        return self.first <= line <= self.last


ModulePreludes = dict[str, tuple[Prelude, ...]]


@dataclass(frozen=True)
class Challenge:
    """Everything that distinguishes one comparator challenge from another."""

    name: str
    targets: tuple[str, ...]
    header: Path
    footer: Path
    expected: Path
    extras: Extras = field(default_factory=dict)
    module_preludes: ModulePreludes = field(default_factory=dict)

    @property
    def target_env(self) -> str:
        """Value of `COMPARATOR_TARGETS` for `extract_closure.lean`."""
        return " ".join(self.targets)


# --------------------------------------------------------------------- LDT

FIELD_MODEL_ATTRIBUTE = [
    "",
    "-- source: MIPStarRE/LDT/Basic/ParametersBase.lean (attribute command)",
    "attribute [instance_reducible, instance] FieldModel.instField FieldModel.instFintype",
    "  FieldModel.instDecidableEq",
]

LDT_EXTRAS: Extras = {
    "MIPStarRE.LDT.FieldModel": FIELD_MODEL_ATTRIBUTE,
    "MIPStarRE.LDT.Polynomial.toFun": [
        "",
        "-- source: MIPStarRE/LDT/Basic/LowDegreePolynomial.lean (elaboration context)",
        "noncomputable instance {params : Parameters} [FieldModel params.q] :",
        "    CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=",
        "  ⟨Polynomial.toFun⟩",
    ],
    "MIPStarRE.LDT.AxisLinePolynomial.toFun": [
        "",
        "-- source: MIPStarRE/LDT/Basic/LinePolynomials.lean (elaboration context)",
        "noncomputable instance {params : Parameters} [FieldModel params.q] :",
        "    CoeFun (AxisLinePolynomial params) (fun _ => Fq params → Fq params) :=",
        "  ⟨AxisLinePolynomial.toFun⟩",
    ],
    "MIPStarRE.LDT.DiagonalLinePolynomial.toFun": [
        "",
        "-- source: MIPStarRE/LDT/Basic/LinePolynomials.lean (elaboration context)",
        "noncomputable instance {params : Parameters} [FieldModel params.q] :",
        "    CoeFun (DiagonalLinePolynomial params) (fun _ => Fq params → Fq params) :=",
        "  ⟨DiagonalLinePolynomial.toFun⟩",
    ],
}

LDT_MODULE_PRELUDES: ModulePreludes = {
    "MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean": (
        Prelude(
            ns=("MIPStarRE.LDT", "ProjStrat"),
            lines=(
                "open MIPStarRE.Quantum",
                "variable {params : Parameters} [FieldModel params.q]",
                "variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]",
                "variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]",
            ),
        ),
    ),
    "MIPStarRE/Quantum/FiniteMatrix/NormalizedTrace.lean": (
        Prelude(
            ns=("MIPStarRE.Quantum",),
            lines=(
                "open scoped Matrix.Norms.Elementwise",
                "open WithLp",
                "variable {d : Type*} [Fintype d]",
            ),
        ),
    ),
}

# -------------------------------------------------------------------- QPBT

QPBT_EXTRAS: Extras = {
    "MIPStarRE.LDT.FieldModel": FIELD_MODEL_ATTRIBUTE,
    # `dsimp` discharges `Distribution.support` of `uniformOnFinset`
    # definitionally, so this rfl-lemma is used by a closure proof without
    # appearing in the kernel closure
    "MIPStarRE.LDT.Distribution.uniformOnFinset": [
        "",
        "-- source: MIPStarRE/LDT/Basic/Distribution.lean:430-432 (simp context)",
        "@[simp]",
        "theorem uniformOnFinset_support {α : Type*} (s : Finset α) :",
        "    (uniformOnFinset s).support = s := rfl",
    ],
    "MIPStarRE.QPBT.Game": [
        "",
        "-- source: MIPStarRE/QPBT/Games/Defs.lean (attribute command)",
        "attribute [instance] Game.questionAFintype Game.questionBFintype",
        "  Game.answerAFintype Game.answerBFintype Game.questionADecidableEq",
        "  Game.questionBDecidableEq Game.answerADecidableEq Game.answerBDecidableEq",
    ],
    "MIPStarRE.QPBT.Strategy": [
        "",
        "-- source: MIPStarRE/QPBT/Games/Defs.lean (attribute command)",
        "attribute [instance] Strategy.ιAFintype Strategy.ιBFintype",
        "  Strategy.ιADecidableEq Strategy.ιBDecidableEq",
    ],
    "MIPStarRE.QPBT.PauliSoundnessWitness": [
        "",
        "-- source: MIPStarRE/QPBT/Test/SoundnessDefs.lean (attribute command)",
        "attribute [instance] PauliSoundnessWitness.ιAFintype"
        " PauliSoundnessWitness.ιBFintype",
        "  PauliSoundnessWitness.ιADecidableEq PauliSoundnessWitness.ιBDecidableEq",
    ],
    "MIPStarRE.QPBT.QubitSoundnessWitness": [
        "",
        "-- source: MIPStarRE/QPBT/Test/QubitForm.lean (attribute command)",
        "attribute [instance] QubitSoundnessWitness.ιAFintype",
        "  QubitSoundnessWitness.ιBFintype QubitSoundnessWitness.ιADecidableEq",
        "  QubitSoundnessWitness.ιBDecidableEq",
    ],
}

QPBT_MODULE_PRELUDES: ModulePreludes = {
    "MIPStarRE/QPBT/Algebra/FieldBasis.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("variable {G : Type*} [CommGroup G]",),
            first=88,
            last=117,
        ),
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=(
                "variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]",
                'local notation "G" => Gal(K/(ZMod 2))',
            ),
            first=119,
            last=385,
        ),
    ),
    "MIPStarRE/QPBT/Algebra/Subspaces.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=(
                "variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]",
            ),
        ),
    ),
    "MIPStarRE/QPBT/Algebra/Lines.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("variable {K : Type*} [Field K]",),
        ),
    ),
    "MIPStarRE/QPBT/Algebra/LowDegreeCode.lean": (
        Prelude(ns=("MIPStarRE.QPBT",), lines=("open MvPolynomial",)),
    ),
    "MIPStarRE/QPBT/Algebra/Pauli.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=(
                "open MIPStarRE.Quantum",
                "variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]",
                "  [Algebra (ZMod 2) K]",
            ),
        ),
    ),
    "MIPStarRE/QPBT/Algebra/PauliTheorems.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("open MIPStarRE.LDT MIPStarRE.Quantum",),
        ),
    ),
    "MIPStarRE/QPBT/Algebra/SelfDualBasisTheorems.lean": (
        Prelude(ns=("MIPStarRE.QPBT",), lines=("open MIPStarRE.LDT",)),
    ),
    "MIPStarRE/QPBT/Games/Defs.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("open MIPStarRE.LDT", "open MIPStarRE.Quantum"),
        ),
    ),
    "MIPStarRE/QPBT/State.lean": (
        Prelude(ns=("MIPStarRE.QPBT",), lines=("open MIPStarRE.Quantum",)),
    ),
    "MIPStarRE/QPBT/Test/LowDegreeGame.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("open MIPStarRE.LDT",),
            first=31,
            last=768,
            noncomputable=True,
        ),
    ),
    "MIPStarRE/QPBT/Test/MagicSquare.lean": (
        Prelude(ns=("MIPStarRE.QPBT",), lines=("open MIPStarRE.LDT",)),
    ),
    "MIPStarRE/QPBT/Test/PauliBasisTest.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("open MIPStarRE.LDT",),
            first=28,
            last=741,
            noncomputable=True,
        ),
    ),
    "MIPStarRE/QPBT/Test/SoundnessDefs.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("open MIPStarRE.LDT", "open MIPStarRE.Quantum"),
            first=28,
            last=207,
            noncomputable=True,
        ),
    ),
    "MIPStarRE/QPBT/Test/QubitForm.lean": (
        Prelude(
            ns=("MIPStarRE.QPBT",),
            lines=("open MIPStarRE.LDT MIPStarRE.Quantum",),
            first=35,
            last=447,
            noncomputable=True,
        ),
    ),
}


CHALLENGES: dict[str, Challenge] = {
    "ldt": Challenge(
        name="ldt",
        targets=("MIPStarRE.LDT.Test.mainFormal",),
        header=Path("scripts/comparator/challenge_header.lean"),
        footer=Path("scripts/comparator/challenge_footer.lean"),
        expected=Path("scripts/comparator/expected/Challenge.lean.expected"),
        extras=LDT_EXTRAS,
        module_preludes=LDT_MODULE_PRELUDES,
    ),
    "qpbt": Challenge(
        name="qpbt",
        targets=(
            "MIPStarRE.QPBT.pauli_soundness",
            "MIPStarRE.QPBT.pauli_soundness_qubit",
        ),
        header=Path("scripts/comparator/challenge_qpbt_header.lean"),
        footer=Path("scripts/comparator/challenge_qpbt_footer.lean"),
        expected=Path("scripts/comparator/expected/ChallengeQPBT.lean.expected"),
        extras=QPBT_EXTRAS,
        module_preludes=QPBT_MODULE_PRELUDES,
    ),
}
