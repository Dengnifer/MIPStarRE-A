#!/usr/bin/env python3
"""Per-challenge configuration for the comparator challenge generators.

One entry per comparator challenge: the target theorems whose statement
closure is extracted, the header/footer that frame the generated file, the
checked-in expected copy, and the elaboration context that the kernel closure
cannot see.

The registry itself comes from `local/project.json`: one challenge per track
that names headline theorems (`load_challenges`).  What cannot come from a
config file — the hand-written elaboration context the kernel closure does not
carry — stays here, in `EXTRAS` and `MODULE_PRELUDES`, keyed by challenge name;
both ship empty, with one commented example of their shape.

The extractor (`extract_closure.lean`) is shared and selects its roots from
the `COMPARATOR_TARGETS` environment variable; `assemble_challenge.py` and
`check_challenge_drift.py` select the rest from here with `--challenge`.
Adding a challenge means adding a track with headline theorems, a header, a
footer, and a CI drift step — no generator code changes.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import project_config  # noqa: E402

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




# --------------------------------------------------------------- the registry

#: Hand-written elaboration context, keyed by challenge name.  The kernel
#: closure cannot see attribute commands or `CoeFun` instances that elaboration
#: unfolds, so the assembler replays them after the declaration they belong to.
#: Only the formalizer can write these, and they grow with the project.  One
#: example of the shape:
#:
#: EXTRAS = {
#:     "core": {
#:         "MyLib.Core.Polynomial.toFun": [
#:             "",
#:             "-- source: MyLib/Core/Polynomial.lean (elaboration context)",
#:             "noncomputable instance {p : Parameters} :",
#:             "    CoeFun (Polynomial p) (fun _ => Point p → F p) :=",
#:             "  ⟨Polynomial.toFun⟩",
#:         ],
#:     },
#: }
EXTRAS: dict[str, Extras] = {}

#: Per-module elaboration scopes, keyed by challenge name and then by module
#: path.  A module needs one `Prelude` per source section whose context differs
#: (a section that opens namespaces or binds `variable`s the snippets rely on).
#: One example of the shape:
#:
#: MODULE_PRELUDES = {
#:     "core": {
#:         "MyLib/Core/Basic.lean": (
#:             Prelude(
#:                 ns=("MyLib.Core",),
#:                 lines=("open scoped BigOperators", "variable {p : Parameters}"),
#:                 first=1,
#:                 last=420,
#:                 noncomputable=True,
#:             ),
#:         ),
#:     },
#: }
MODULE_PRELUDES: dict[str, ModulePreludes] = {}


def _challenge_paths(name: str, default_track: str) -> tuple[Path, Path]:
    """Header and footer of one challenge.

    The project's default track uses the plain names, so a one-track project
    edits `challenge_header.lean` and `challenge_footer.lean`; a second track
    gets its own `challenge_<track>_header.lean` / `_footer.lean` pair.
    """

    stem = "" if name == default_track else f"_{name}"
    return (
        Path(f"scripts/comparator/challenge{stem}_header.lean"),
        Path(f"scripts/comparator/challenge{stem}_footer.lean"),
    )


def load_challenges(root: Path | None = None) -> dict[str, Challenge]:
    """Build the registry from `local/project.json`.

    One challenge per track that names headline theorems: the theorems are the
    challenge's targets, and the track's `expected_challenge` is the checked-in
    copy the drift check compares against.  A repository whose tracks are not
    written yet has no challenge, and the generators say so instead of failing.
    """

    cfg = project_config.load(root)
    default_track = project_config.get(cfg, "project.track", "")
    out: dict[str, Challenge] = {}
    for name in project_config.track_names(cfg):
        entry = project_config.track(cfg, name) or {}
        targets = tuple(theorem for theorem, _label in entry.get("headline", []))
        if not targets:
            continue
        header, footer = _challenge_paths(name, default_track)
        expected = entry.get("expected_challenge") or (
            "scripts/comparator/expected/Challenge"
            + ("" if name == default_track else name.upper())
            + ".lean.expected"
        )
        out[name] = Challenge(
            name=name,
            targets=targets,
            header=header,
            footer=footer,
            expected=Path(expected),
            extras=EXTRAS.get(name, {}),
            module_preludes=MODULE_PRELUDES.get(name, {}),
        )
    return out


CHALLENGES: dict[str, Challenge] = load_challenges()


def default_challenge_name(root: Path | None = None) -> str | None:
    """The challenge of the project's default track, if it has one."""

    name = project_config.get(project_config.load(root), "project.track", "")
    return name if name in CHALLENGES else None


def main(argv: "list[str] | None" = None) -> int:
    """Small CLI so shell steps need not parse `local/project.json` themselves.

    `names` prints one challenge name per line (nothing when none is
    configured); `targets` and `expected` print one challenge's target list and
    checked-in copy, defaulting to the project's default track.
    """

    import argparse

    parser = argparse.ArgumentParser(description="comparator challenge registry")
    parser.add_argument("command", choices=("names", "targets", "expected"))
    parser.add_argument("--challenge", default=None, help="challenge name")
    args = parser.parse_args(argv)

    if args.command == "names":
        for name in sorted(CHALLENGES):
            print(name)
        return 0

    name = args.challenge or default_challenge_name()
    if name is None or name not in CHALLENGES:
        print(
            "no comparator challenge is configured in local/project.json",
            file=sys.stderr,
        )
        return 2
    challenge = CHALLENGES[name]
    print(challenge.target_env if args.command == "targets" else challenge.expected)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
