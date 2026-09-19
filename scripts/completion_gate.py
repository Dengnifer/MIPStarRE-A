#!/usr/bin/env python3
r"""Model-free completion gate for a formalization track.

``local/protocols/completion.md`` defines when a track may be declared
finished.  This script decides the mechanically checkable part of that
definition: it runs no model, opens no network connection, and uses only the
standard library, so its verdict is reproducible by anyone holding the commit.

Six criteria, in the protocol's numbering:

* ``C1`` proof integrity — no ``sorry``/``admit`` site, project ``axiom``
  declaration, native evaluation or ``trustCompiler`` under the track's Lean
  root.
* ``C2`` headline axioms — a committed ``AxiomAudit`` file covering every
  headline theorem (the axiom *values* come from the CI build: delegated).
* ``C3`` paper-gap register — every row terminal.
* ``C4`` blueprint — every ``\lean{}`` node marked ``\leanok`` or exempted.
* ``C5`` comparator — challenge recorded, expected copy present, verified
  library commit an ancestor-or-equal of the commit being declared.
* ``C6`` docs truthful — no stale nonzero open-site claim once ``C1`` holds.

``C2``, ``C4`` and ``C5`` each have a half this gate cannot decide without a
Lean build — the axiom values, ``blueprint_leanok_axioms.py --ci`` and the
comparator drift regeneration.  When their static half holds they report
``DELEGATED`` rather than ``PASS``, so a completion comment can never quote a
``PASS`` for a check nobody ran; ``DELEGATED`` does not count against the exit
code, and a failing static half is still ``FAIL``.

Shared rules, never restated here:

* the sorry-site rule is parsed out of
  ``results/telemetry/owner-tools/estimate.sh`` (``SORRY_SITE_RE``).  The POSIX
  character classes of that ERE are translated to Python syntax; the alternation
  itself is used verbatim, so the estimate posted on the tracker issue and this
  gate can never disagree about what a site is.
* explicit ``axiom``/``constant`` declarations are found with ``DECL_RE`` of
  ``scripts/audit_lean_axiom_declarations.py``, and comments are stripped with
  that module's ``strip_lean_comments``.  Comment stripping there is strictly
  stronger than the estimate's ``sed 's/--.*$//'`` (it also blanks block
  comments and string literals), so the gate can only ever drop sites that are
  not real; it never invents one.
* the set of blueprint environments a node may live in is read out of
  ``_TEX_ENV_BEGIN_RE`` of ``scripts/blueprint_lean_sync.py`` — the parser
  behind ``scripts/blueprint_leanok_axioms.py`` — so ``C4`` and the blueprint
  tooling can never disagree about what a node is.

Exit codes: 0 every mechanically checkable criterion passed, 1 at least one
failed, 2 the gate could not run (missing shared rule, unknown track).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from audit_lean_axiom_declarations import DECL_RE, strip_lean_comments  # noqa: E402
from blueprint_lean_sync import _TEX_ENV_BEGIN_RE  # noqa: E402
from lean_header_utils import line_number  # noqa: E402


ESTIMATE_SH = Path("results/telemetry/owner-tools/estimate.sh")
SORRY_RULE_RE = re.compile(r"^SORRY_SITE_RE='(?P<pattern>[^']*)'", re.M)

# POSIX bracket classes used by the shared rule, translated to Python syntax.
# Unknown classes are an error rather than a silent mistranslation.
POSIX_CLASSES = {"space": " \t", "blank": " \t", "digit": "0-9", "alpha": "A-Za-z"}
POSIX_CLASS_RE = re.compile(r"\[\[:(\w+):\]\]")

# Native evaluation and compiler trust.  No prior implementation exists in the
# repository, so this rule is defined here and only here.
NATIVE_RE = re.compile(
    r"\bnative_decide\b|\bdecide\s*\+\s*native\b|\btrustCompiler\b"
)

# ``DECL_RE`` anchors at the start of a line, so a continuation line that opens
# with the ordinary local name ``constant`` — the QPBT error-bound proofs use it
# for the constant of an estimate — parses as a declaration whose "name" is the
# next token, often ``*``.  A declaration name is a Lean identifier; anything
# else is such a continuation line and is dropped.  Narrowing this way can only
# remove false positives: ``axiom * : ...`` does not elaborate.
DECL_NAME_RE = re.compile(r"[^\W\d]\S*")

EVIDENCE_LIMIT = 10
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

PASS, FAIL, DELEGATED, DEFERRED = "PASS", "FAIL", "DELEGATED", "DEFERRED"


class GateConfigError(Exception):
    """The gate cannot run at all (bad track, missing shared rule)."""


@dataclass(frozen=True)
class Track:
    """Everything the gate needs to judge one track."""

    name: str
    lean_root: str
    headline: tuple[tuple[str, str], ...]
    gap_register: str
    axiom_audit: str
    blueprint_chapters: tuple[str, ...]
    leanok_exemptions: str
    comparator_doc: str
    truthful_docs: tuple[str, ...]


TRACKS: dict[str, Track] = {
    "qpbt": Track(
        name="qpbt",
        lean_root="MIPStarRE/QPBT",
        headline=(
            ("MIPStarRE.QPBT.pauli_soundness", "thm:pauli"),
            ("MIPStarRE.QPBT.pauli_soundness_qubit", "cor:pauli-binary"),
            ("MIPStarRE.QPBT.exists_spcc_value_one", "lem:pauli-completeness"),
            ("MIPStarRE.QPBT.exists_ld_soundness", "lem:ld-soundness"),
        ),
        gap_register="docs/paper-gaps/qpbt-gap-register.md",
        axiom_audit="MIPStarRE/QPBT/Test/AxiomAudit.lean",
        blueprint_chapters=(
            "blueprint/src/chapter/ch11_qpbt_algebra.tex",
            "blueprint/src/chapter/ch12_qpbt_games.tex",
            "blueprint/src/chapter/ch13_qpbt_test.tex",
            "blueprint/src/chapter/ch14_qpbt_observables.tex",
            "blueprint/src/chapter/ch15_qpbt_combining.tex",
            "blueprint/src/chapter/ch16_qpbt_extraction.tex",
        ),
        leanok_exemptions="docs/completion/qpbt-leanok-exemptions.md",
        comparator_doc="docs/comparator.md",
        truthful_docs=("README.md",),
    )
}


@dataclass
class Criterion:
    """One criterion's verdict."""

    ident: str
    title: str
    status: str
    summary: str = ""
    evidence: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    @property
    def counts_against_exit(self) -> bool:
        return self.status == FAIL


# ---------------------------------------------------------------------------
# Shared sorry-site rule
# ---------------------------------------------------------------------------


def translate_posix_ere(pattern: str) -> str:
    """Translate the POSIX bracket classes of an ERE to Python syntax."""

    def replace(match: re.Match[str]) -> str:
        name = match.group(1)
        if name not in POSIX_CLASSES:
            raise GateConfigError(
                f"unsupported POSIX class [[:{name}:]] in the shared sorry-site rule"
            )
        return f"[{POSIX_CLASSES[name]}]"

    return POSIX_CLASS_RE.sub(replace, pattern)


def load_sorry_site_rule(root: Path) -> str:
    """Return the shared sorry-site ERE, translated, from ``estimate.sh``."""

    path = root / ESTIMATE_SH
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise GateConfigError(f"cannot read the shared sorry-site rule: {exc}") from exc
    match = SORRY_RULE_RE.search(text)
    if match is None:
        raise GateConfigError(
            f"{ESTIMATE_SH} has no SORRY_SITE_RE assignment; the gate refuses to "
            "restate the rule in a second place"
        )
    return translate_posix_ere(match.group("pattern"))


def token_rule(pattern: str, token: str) -> re.Pattern[str]:
    """Return the shared rule's *shape*, matched against another token."""

    if "sorry" not in pattern:
        raise GateConfigError("the shared sorry-site rule does not mention `sorry`")
    return re.compile(pattern.replace("sorry", token))


# ---------------------------------------------------------------------------
# Criteria
# ---------------------------------------------------------------------------


def lean_files(root: Path, track: Track) -> list[Path]:
    base = root / track.lean_root
    if not base.exists():
        return []
    return sorted(p for p in base.rglob("*.lean") if p.is_file())


def criterion_proof_integrity(root: Path, track: Track) -> Criterion:
    """C1: no proof debt of any kind under the track's Lean root."""

    rule = load_sorry_site_rule(root)
    sorry_re = token_rule(rule, "sorry")
    admit_re = token_rule(rule, "admit")
    crit = Criterion("C1", "proof integrity", PASS)
    files = lean_files(root, track)
    if not files:
        return Criterion(
            "C1", "proof integrity", FAIL,
            summary=f"no Lean file under {track.lean_root}",
        )

    hits: list[tuple[str, int, str, str]] = []
    for path in files:
        rel = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8", errors="replace")
        stripped = strip_lean_comments(text)
        for number, line in enumerate(stripped.splitlines(), start=1):
            if sorry_re.search(line):
                hits.append((rel, number, "sorry", line.strip()))
            elif admit_re.search(line):
                hits.append((rel, number, "admit", line.strip()))
            elif NATIVE_RE.search(line):
                hits.append((rel, number, "native", line.strip()))
        for match in DECL_RE.finditer(stripped):
            name = match.group(2)
            if not DECL_NAME_RE.fullmatch(name):
                continue
            hits.append(
                (
                    rel,
                    line_number(stripped, match.start()),
                    f"{match.group(1)} declaration",
                    name,
                )
            )

    if not hits:
        crit.summary = f"{len(files)} Lean files, no site"
        return crit
    crit.status = FAIL
    crit.summary = f"{len(hits)} site(s) in {len(files)} Lean files"
    crit.evidence = [
        f"{rel}:{number}: {kind}: {snippet}" for rel, number, kind, snippet in hits
    ]
    return crit


def criterion_headline_axioms(root: Path, track: Track) -> Criterion:
    """C2: the axiom-audit file exists and covers every headline theorem."""

    crit = Criterion("C2", "headline axioms", DELEGATED)
    path = root / track.axiom_audit
    crit.notes.append(
        "axiom values come from the CI build of "
        f"{track.axiom_audit}; permitted: " + ", ".join(STANDARD_AXIOMS)
    )
    if not path.exists():
        crit.status = FAIL
        crit.summary = f"missing {track.axiom_audit}"
        crit.evidence.append(
            f"{track.axiom_audit}:0: no axiom-audit file for this track"
        )
        return crit

    text = path.read_text(encoding="utf-8", errors="replace")
    stripped = strip_lean_comments(text)
    covered: dict[str, int] = {}
    for match in re.finditer(r"assert_standard_axioms\s+(\S+)", stripped):
        covered.setdefault(match.group(1), line_number(stripped, match.start()))
    missing = [name for name, _ in track.headline if name not in covered]
    if missing:
        crit.status = FAIL
        crit.summary = f"{len(missing)} of {len(track.headline)} headline theorems uncovered"
        crit.evidence = [
            f"{track.axiom_audit}:0: no `assert_standard_axioms {name}`"
            for name in missing
        ]
        return crit
    crit.summary = (
        f"all {len(track.headline)} headline theorems asserted; the axiom "
        "values come from the CI build"
    )
    crit.evidence = [
        f"{track.axiom_audit}:{covered[name]}: assert_standard_axioms {name}"
        for name, _ in track.headline
    ]
    return crit


def _table_rows(text: str) -> tuple[int, list[str], list[tuple[int, list[str]]]]:
    """Return (header line, header cells, data rows) of the first markdown table."""

    lines = text.splitlines()
    for index, line in enumerate(lines[:-1]):
        if not line.lstrip().startswith("|"):
            continue
        separator = lines[index + 1].strip()
        if not re.fullmatch(r"\|(\s*:?-{2,}:?\s*\|)+", separator):
            continue
        header = [cell.strip() for cell in line.strip().strip("|").split("|")]
        rows: list[tuple[int, list[str]]] = []
        for offset, row in enumerate(lines[index + 2 :], start=index + 3):
            if not row.lstrip().startswith("|"):
                break
            rows.append((offset, [c.strip() for c in row.strip().strip("|").split("|")]))
        return index + 1, header, rows
    return 0, [], []


def criterion_paper_gaps(root: Path, track: Track) -> Criterion:
    """C3: every register row carries a terminal status."""

    crit = Criterion("C3", "paper gaps terminal", PASS)
    path = root / track.gap_register
    if not path.exists():
        return Criterion(
            "C3", "paper gaps terminal", FAIL,
            summary=f"missing {track.gap_register}",
            evidence=[f"{track.gap_register}:0: no paper-gap register for this track"],
        )
    text = path.read_text(encoding="utf-8", errors="replace")
    header_line, header, rows = _table_rows(text)
    if not header:
        crit.status = FAIL
        crit.summary = "no register table found"
        crit.evidence.append(f"{track.gap_register}:1: no markdown table")
        return crit
    try:
        column = [cell.lower() for cell in header].index("terminal status")
    except ValueError:
        crit.status = FAIL
        crit.summary = "register has no `Terminal status` column"
        crit.evidence.append(
            f"{track.gap_register}:{header_line}: columns are "
            + ", ".join(header)
        )
        return crit

    bad: list[str] = []
    for number, cells in rows:
        value = cells[column].strip("` ").lower() if column < len(cells) else ""
        if value not in {"corrected", "no-difference"}:
            note = cells[0][:60] if cells else ""
            bad.append(
                f"{track.gap_register}:{number}: terminal status "
                f"{value or '(empty)'!r} for {note}"
            )
    if bad:
        crit.status = FAIL
        crit.summary = f"{len(bad)} of {len(rows)} rows not terminal"
        crit.evidence = bad
        return crit
    crit.summary = f"all {len(rows)} rows terminal"
    return crit


# The blueprint's environment list is the repository's, not a second opinion:
# it is read out of the alternation of ``_TEX_ENV_BEGIN_RE`` in
# ``scripts/blueprint_lean_sync.py`` instead of being restated, exactly as the
# sorry-site rule is read out of ``estimate.sh``.  Restating it is how a
# ``\lean{}``-carrying ``example`` or ``remark`` node would become invisible to
# C4 while the blueprint tooling still sees it.
ENV_ALTERNATION_RE = re.compile(r"\\\\begin\\\{\(([^)]+)\)\\\}")
LABEL_RE = re.compile(r"\\label\{(?P<label>[^}]+)\}")


def blueprint_node_rule() -> re.Pattern[str]:
    """Return the node rule, over the shared parser's environment list."""

    match = ENV_ALTERNATION_RE.search(_TEX_ENV_BEGIN_RE.pattern)
    if match is None:
        raise GateConfigError(
            "scripts/blueprint_lean_sync.py no longer spells its blueprint "
            "environments in _TEX_ENV_BEGIN_RE; the gate refuses to restate "
            "the rule in a second place"
        )
    return re.compile(
        r"\\begin\{(" + match.group(1) + r")\}(?P<body>.*?)\\end\{\1\}", re.S
    )


def _exemptions(root: Path, track: Track) -> tuple[dict[str, str], str | None]:
    path = root / track.leanok_exemptions
    if not path.exists():
        return {}, f"{track.leanok_exemptions}:0: no exemption table"
    _, header, rows = _table_rows(path.read_text(encoding="utf-8", errors="replace"))
    if not header:
        return {}, f"{track.leanok_exemptions}:1: no markdown table"
    table = {}
    for _, cells in rows:
        if len(cells) >= 2 and cells[0].strip("` ") and cells[1].strip():
            table[cells[0].strip("` ")] = cells[1]
    return table, None


def criterion_blueprint(root: Path, track: Track) -> Criterion:
    """C4: every blueprint node with a Lean link is marked or exempted."""

    crit = Criterion("C4", "blueprint marked", DELEGATED)
    crit.notes.append(
        "`python3 scripts/blueprint_leanok_axioms.py --ci` must also exit 0; "
        "it needs a Lean build and is not run here"
    )
    node_re = blueprint_node_rule()
    exempt, exempt_problem = _exemptions(root, track)
    unmarked: list[str] = []
    nodes = 0
    for chapter in track.blueprint_chapters:
        path = root / chapter
        if not path.exists():
            crit.status = FAIL
            crit.evidence.append(f"{chapter}:0: blueprint chapter missing")
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for match in node_re.finditer(text):
            body = match.group("body")
            if "\\lean{" not in body:
                continue
            nodes += 1
            if "\\leanok" in body:
                continue
            label_match = LABEL_RE.search(body)
            label = label_match.group("label") if label_match else "(unlabelled)"
            if label in exempt:
                continue
            unmarked.append(
                f"{chapter}:{line_number(text, match.start())}: "
                f"{label} has \\lean{{}} but no \\leanok and no exemption"
            )
    if unmarked:
        crit.status = FAIL
        crit.summary = f"{len(unmarked)} of {nodes} linked nodes unmarked and unexempted"
        crit.evidence.extend(unmarked)
        if exempt_problem:
            crit.evidence.append(exempt_problem)
        return crit
    if crit.status == FAIL:
        crit.summary = "blueprint chapters missing"
        return crit
    crit.summary = (
        f"{nodes} linked nodes, {len(exempt)} exempted with a reason; "
        "the `--ci` run comes from CI"
    )
    return crit


COMPARATOR_KEYS = (
    "challenge-repository",
    "verified-library-commit",
    "expected-challenge",
    "drift-check",
    "covered-theorems",
)


def _comparator_record(root: Path, track: Track) -> tuple[dict[str, str], int, str | None]:
    path = root / track.comparator_doc
    if not path.exists():
        return {}, 0, f"{track.comparator_doc}:0: no comparator document"
    marker = f"<!-- completion-gate: track={track.name} -->"
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    for index, line in enumerate(lines):
        if line.strip() != marker:
            continue
        record: dict[str, str] = {}
        for entry in lines[index + 1 :]:
            entry = entry.strip()
            if not entry.startswith("-"):
                break
            key, _, value = entry.lstrip("- ").partition(":")
            record[key.strip().lower()] = value.strip()
        return record, index + 1, None
    return {}, 0, f"{track.comparator_doc}:0: no `{marker}` block"


def _is_ancestor(root: Path, pin: str, commit: str) -> bool | None:
    try:
        completed = subprocess.run(
            ["git", "merge-base", "--is-ancestor", pin, commit],
            cwd=root,
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError:
        return None
    if completed.returncode in (0, 1):
        return completed.returncode == 0
    return None


def criterion_comparator(root: Path, track: Track, commit: str) -> Criterion:
    """C5: a recorded, drift-checked comparator challenge covering the headlines."""

    crit = Criterion("C5", "lean comparator", DELEGATED)
    crit.notes.append(
        "the drift check regenerates the challenge with `lake env lean` and is "
        "delegated to CI; this gate checks the record, the expected copy and the pin"
    )
    record, record_line, problem = _comparator_record(root, track)
    if problem is not None:
        return Criterion("C5", "lean comparator", FAIL,
                         summary="no comparator record for this track",
                         evidence=[problem], notes=crit.notes)

    missing = [key for key in COMPARATOR_KEYS if not record.get(key)]
    if missing:
        crit.status = FAIL
        crit.summary = f"comparator record missing {len(missing)} field(s)"
        crit.evidence = [
            f"{track.comparator_doc}:{record_line}: missing `{key}`" for key in missing
        ]
        return crit

    problems: list[str] = []
    expected = record["expected-challenge"]
    if not (root / expected).exists():
        problems.append(
            f"{track.comparator_doc}:{record_line}: expected challenge {expected} "
            "does not exist"
        )
    covered = {name.strip() for name in record["covered-theorems"].split(",")}
    for name, _ in track.headline:
        if name not in covered:
            problems.append(
                f"{track.comparator_doc}:{record_line}: headline theorem {name} "
                "is not covered by the challenge"
            )
    pin = record["verified-library-commit"]
    if not re.fullmatch(r"[0-9a-f]{40}", pin):
        problems.append(
            f"{track.comparator_doc}:{record_line}: verified-library-commit "
            f"{pin!r} is not a full commit hash"
        )
    else:
        ancestry = _is_ancestor(root, pin, commit)
        if ancestry is None:
            problems.append(
                f"{track.comparator_doc}:{record_line}: cannot compare the verified "
                f"commit {pin[:12]} with {commit[:12]} (unknown commit?)"
            )
        elif not ancestry:
            problems.append(
                f"{track.comparator_doc}:{record_line}: verified commit {pin[:12]} "
                f"is not an ancestor-or-equal of {commit[:12]}"
            )
    if problems:
        crit.status = FAIL
        crit.summary = f"{len(problems)} problem(s) in the comparator record"
        crit.evidence = problems
        return crit
    crit.summary = (
        f"challenge {record['challenge-repository']} covers all "
        f"{len(track.headline)} headline theorems; verified at {pin[:12]}; "
        "the drift check comes from CI"
    )
    return crit


CLAIM_RE = re.compile(
    r"(?P<count>\d+)\s+(?:open\s+)?(?:sorry|sorries|sorry sites?|open sites?)", re.I
)


def criterion_docs_truthful(root: Path, track: Track, integrity: Criterion) -> Criterion:
    """C6: no doc advertises open sites once there are none."""

    if integrity.status != PASS:
        return Criterion(
            "C6", "docs truthful", DEFERRED,
            summary="criterion C1 does not hold yet; nothing to contradict",
        )
    crit = Criterion("C6", "docs truthful", PASS)
    checked = 0
    missing: list[str] = []
    for doc in track.truthful_docs:
        path = root / doc
        if not path.exists():
            # Fail closed, as every other criterion does: a registered doc that
            # has been renamed or deleted must be noticed, not silently skipped
            # into a green "0 doc(s) checked".
            missing.append(doc)
            crit.status = FAIL
            crit.evidence.append(f"{doc}:0: registered truthful doc is missing")
            continue
        checked += 1
        for number, line in enumerate(
            path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1
        ):
            for match in CLAIM_RE.finditer(line):
                if match.group("count") != "0":
                    crit.status = FAIL
                    crit.evidence.append(f"{doc}:{number}: {line.strip()[:100]}")
    stale = len(crit.evidence) - len(missing)
    if missing and stale:
        crit.summary = (
            f"{stale} stale claim(s) in {checked} doc(s); "
            f"{len(missing)} registered doc(s) missing"
        )
    elif missing:
        crit.summary = f"{len(missing)} of {len(track.truthful_docs)} registered doc(s) missing"
    elif stale:
        crit.summary = f"{stale} stale claim(s) in {checked} doc(s)"
    else:
        crit.summary = f"{checked} doc(s) checked, no stale open-site claim"
    return crit


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def resolve_commit(root: Path, commit: str | None) -> str:
    if commit:
        return commit
    try:
        completed = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=root, check=False, capture_output=True, text=True,
        )
    except OSError:
        return "HEAD"
    return completed.stdout.strip() or "HEAD"


def run_check(root: Path, track: Track, commit: str) -> list[Criterion]:
    integrity = criterion_proof_integrity(root, track)
    return [
        integrity,
        criterion_headline_axioms(root, track),
        criterion_paper_gaps(root, track),
        criterion_blueprint(root, track),
        criterion_comparator(root, track, commit),
        criterion_docs_truthful(root, track, integrity),
    ]


def render_text(track: Track, commit: str, criteria: Sequence[Criterion]) -> str:
    out = [f"completion gate: track {track.name}  commit {commit[:12]}"]
    for crit in criteria:
        out.append(f"{crit.ident} {crit.title:<22} {crit.status:<9} {crit.summary}")
        for line in crit.evidence[:EVIDENCE_LIMIT]:
            out.append(f"    {line}")
        if len(crit.evidence) > EVIDENCE_LIMIT:
            out.append(f"    ... and {len(crit.evidence) - EVIDENCE_LIMIT} more")
        for note in crit.notes:
            out.append(f"    note: {note}")
    failed = [c.ident for c in criteria if c.counts_against_exit]
    delegated = [c.ident for c in criteria if c.status == DELEGATED]
    if failed:
        out.append(f"FAIL: {', '.join(failed)} — the track is not finished")
    else:
        out.append("PASS: every mechanically checkable criterion holds")
    out.append(
        "reminder: C2 axiom values, the blueprint --ci run and the comparator "
        "drift check are delegated to CI" + (f" ({', '.join(delegated)})" if delegated else "")
    )
    return "\n".join(out)


def render_json(track: Track, commit: str, criteria: Sequence[Criterion], code: int) -> str:
    return json.dumps(
        {
            "track": track.name,
            "commit": commit,
            "exit": code,
            "criteria": [
                {
                    "id": c.ident,
                    "title": c.title,
                    "status": c.status,
                    "summary": c.summary,
                    "evidence": c.evidence,
                    "notes": c.notes,
                }
                for c in criteria
            ],
        },
        indent=2,
    )


def parse_args(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    check = sub.add_parser("check", help="check one track against the definition of done")
    check.add_argument("--track", required=True, help="registered track name")
    check.add_argument("--repo-root", type=Path, default=None, help="repository root")
    check.add_argument("--commit", default=None, help="commit being declared (default HEAD)")
    check.add_argument("--json", action="store_true", help="machine-readable output")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    root = (args.repo_root or Path(__file__).resolve().parent.parent).resolve()
    try:
        track = TRACKS[args.track]
    except KeyError:
        print(
            f"unknown track {args.track!r}; registered: {', '.join(sorted(TRACKS))}",
            file=sys.stderr,
        )
        return 2
    try:
        commit = resolve_commit(root, args.commit)
        criteria = run_check(root, track, commit)
    except GateConfigError as exc:
        print(f"completion gate cannot run: {exc}", file=sys.stderr)
        return 2
    code = 1 if any(c.counts_against_exit for c in criteria) else 0
    if args.json:
        print(render_json(track, commit, criteria, code))
    else:
        print(render_text(track, commit, criteria))
    return code


if __name__ == "__main__":
    sys.exit(main())
