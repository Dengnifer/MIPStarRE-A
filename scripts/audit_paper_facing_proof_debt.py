#!/usr/bin/env python3
r"""Audit paper-facing blueprint statements for proof-debt inputs.

The faithful-formalization policy allows auxiliary bridge or repair lemmas,
but a Lean declaration advertised as a paper theorem, lemma, proposition, or
corollary should not acquire an additional public hypothesis whose purpose is
to supply an unproved part of the proof.  This script is a conservative
review aid for that boundary:

* read theorem-like ``\lean{...}`` references from the active blueprint;
* resolve those references to public Lean declarations under ``PaperLib/``;
* inspect only the public input portion of the declaration header after the
  declaration name and before the result type;
* report occurrences of blocking proof-debt vocabulary such as
  ``BridgeHypotheses``, ``Residual``, ``RepairInput``, ``Package``,
  ``Bundle``, ``Conditional``, ``Producer``, ``Obligation``, an ``Input``
  bundle, a wrapper, an ``Unfaithful`` marker type, or a generic
  ``Hypotheses`` / ``Assumptions`` bundle;
* with ``--broad-vocabulary``, also report the wider tracker vocabulary
  ``Statement``, ``Output``, ``Conclusion``, ``Witness``, ``Data``, and
  ``Compatibility`` in public inputs.  This mode is an inventory tool while
  those broad occurrences are classified and reduced; it is deliberately not
  the default blocking gate.
* classify quoted external theorem interfaces separately in broad mode, so
  external citations from the overview are not conflated with internal proof
  obligations.
* reject paper-facing blueprint entries that point to declaration names with
  conditional proof-debt forms such as ``*_of...Obligations``,
  ``*_of...Residual``, ``*_of...Repair``, ``*_of...Bundle``,
  ``*_of...Unfaithful``, ``*_assuming...``, ``conditional...``, or
  ``Conditional...``, even when the declaration header itself has no
  suspicious public input.
* classify known faithful boundary-input packages separately, with paper
  citations, so they do not become indistinguishable from proof debt.
* optionally, with ``--include-informational-envs``, scan ``definition``,
  ``remark``, and ``example`` entries as a report-only frontier.  This mode is
  useful for finding Lean-only construction records advertised near a paper
  proof without turning those construction records into paper theorem
  statements.

The audit is report-only by default.  With ``--ci`` it exits non-zero when a
finding is present, unless ``--warn-only`` is also supplied.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

import project_config  # noqa: E402
from blueprint_lean_sync import (  # noqa: E402
    BlueprintEntry,
    LEAN_DECL_RE,
    LeanDecl,
    collect_blueprint_entries,
    collect_lean_decls,
    strip_lean_comments_preserve_lines,
)
from lean_header_utils import advance_depth, line_number, starts_keyword


THEOREM_LIKE_ENVS = frozenset({"theorem", "lemma", "proposition", "corollary"})
INFORMATIONAL_ENVS = frozenset({"definition", "remark", "example"})

STRICT_UPPER_TOKENS = (
    "Bridge",
    "Residual",
    "Repair",
    "Package",
    "Producer",
    "Input",
    "Hypotheses",
    "Assumptions",
    "Hypothesis",
    "Assumption",
    "Obligation",
    "Obligations",
    "Wrapper",
    "Bundle",
    "Conditional",
    "Unfaithful",
    "CompletionTransport",
)

BROAD_EXTRA_UPPER_TOKENS = (
    "Statement",
    "Output",
    "Conclusion",
    "Witness",
    "Data",
    "Compatibility",
)

STRICT_LOWER_TOKENS = (
    "bridge",
    "residual",
    "repair",
    "package",
    "producer",
    "input",
    "hypotheses",
    "assumptions",
    "hypothesis",
    "assumption",
    "obligation",
    "obligations",
    "wrapper",
    "bundle",
    "conditional",
    "unfaithful",
    "completionTransport",
)

BROAD_EXTRA_LOWER_TOKENS = (
    "statement",
    "output",
    "conclusion",
    "witness",
    "data",
    "compatibility",
)


def _debt_token_re(upper_tokens: tuple[str, ...], lower_tokens: tuple[str, ...]) -> re.Pattern[str]:
    """Build the public-input proof-debt token matcher from token lists."""

    upper_alternation = "|".join(re.escape(token) for token in upper_tokens)
    lower_alternation = "|".join(re.escape(token) for token in lower_tokens)
    return re.compile(
        r"(?<![A-Za-z0-9_'])"
        r"(?:"
        r"(?:[A-Za-z_][A-Za-z0-9_']*)?"
        r"(?:"
        + upper_alternation
        + r")"
        r"[A-Za-z0-9_']*"
        r"|"
        r"(?:h|has|mk|of)?"
        r"(?:"
        + lower_alternation
        + r")"
        r"[A-Za-z0-9_']*"
        r")"
        r"(?![A-Za-z0-9_'])"
    )


STRICT_DEBT_TOKEN_RE = _debt_token_re(STRICT_UPPER_TOKENS, STRICT_LOWER_TOKENS)
BROAD_DEBT_TOKEN_RE = _debt_token_re(
    STRICT_UPPER_TOKENS + BROAD_EXTRA_UPPER_TOKENS,
    STRICT_LOWER_TOKENS + BROAD_EXTRA_LOWER_TOKENS,
)

# Four per-declaration registers, EMPTY in a fresh repository.
#
# The audit reports every paper-facing declaration whose public interface
# carries proof-debt vocabulary.  A project accumulates decisions about
# particular declarations — this one is a faithful encoding of a hypothesis the
# paper states, that one is the interface of an external theorem the paper
# quotes — and records them here so the audit can classify instead of repeating
# them.  They are data about one development, never rules, so they live outside
# the code, in an optional JSON file:
#
#   local/audit-registers.json
#   {
#     "paper_facing_proof_debt": {
#       "faithful_boundary_tokens": {
#         "CascadeHypotheses": "faithful encoding of the numeric regime; see
#            blueprint/src/chapter/ch10.tex:588-689 and
#            references/<mirror>-paper/inductive_step.tex:187-234"
#       },
#       "external_citation_tokens": { "<Type or field name>": "<evidence>" },
#       "source_context_tokens": { "<Type or field name>": "<evidence>" },
#       "source_context_conditional_decl_names": {
#         "<Fully.Qualified.declaration>": "<evidence>"
#       }
#     }
#   }
#
# The value of each entry is the evidence the audit prints: a paper or
# blueprint citation with line numbers, so a reader can check the decision
# without trusting it.  With no file, every register is empty and every finding
# is reported, which is the right default for a new project.
REGISTER_PATH = "local/audit-registers.json"
REGISTER_SECTION = "paper_facing_proof_debt"

FAITHFUL_BOUNDARY_TOKENS: dict[str, str] = {}
EXTERNAL_CITATION_TOKENS: dict[str, str] = {}
SOURCE_CONTEXT_TOKENS: dict[str, str] = {}
SOURCE_CONTEXT_CONDITIONAL_DECL_NAMES: dict[str, str] = {}

#: Register name in the JSON file -> the dict it fills.
_REGISTERS: dict[str, dict[str, str]] = {
    "faithful_boundary_tokens": FAITHFUL_BOUNDARY_TOKENS,
    "external_citation_tokens": EXTERNAL_CITATION_TOKENS,
    "source_context_tokens": SOURCE_CONTEXT_TOKENS,
    "source_context_conditional_decl_names": SOURCE_CONTEXT_CONDITIONAL_DECL_NAMES,
}


def load_registers(root: Path) -> None:
    """Fill the registers from ``root``; leave them empty when there is no file.

    Called once per run, before anything is classified, so a newly recorded
    exemption takes effect without restarting anything.
    """

    path = root / REGISTER_PATH
    data: dict = {}
    if path.is_file():
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise SystemExit(f"{REGISTER_PATH}: not valid JSON ({exc})")
    section = data.get(REGISTER_SECTION) or {}
    for name, register in _REGISTERS.items():
        register.clear()
        entries = section.get(name) or {}
        if not isinstance(entries, dict):
            raise SystemExit(
                f"{REGISTER_PATH}: {REGISTER_SECTION}.{name} must be an object "
                'mapping "name" to the evidence for it'
            )
        register.update({str(k): str(v) for k, v in entries.items()})


# Broad mode should classify mathematical interfaces, not double-count a local
# variable name whose type is already reported, for example
# ``(data : QXPLayerData Outcome ι)``.
IGNORED_BROAD_BINDER_TOKENS = frozenset({"data"})

CONDITIONAL_DECL_NAME_RE = re.compile(
    r"(?:"
    r"FromBridgeInputs"
    r"|BridgeHypotheses"
    r"|BridgeInputs"
    r"|(?:^|_)of(?:[A-Z][A-Za-z0-9_']*)?"
    r"(?:"
    r"Bridge|Obligations|Obligation|Residual|Repair|Package|Producer|Input"
    r"|Hypotheses|Hypothesis|Assumptions|Assumption"
    r"|Statement|Output|Conclusion|Witness|Wrapper|Bundle|Unfaithful"
    r"|Slackness|Dominance"
    r")"
    r"[A-Za-z0-9_']*"
    r"|(?:^|_)ofRepaired[A-Za-z0-9_']*"
    r"|(?:^|_)assuming[A-Za-z0-9_']*"
    r"|Assuming[A-Za-z0-9_']*"
    r"|(?:^|_)conditional[A-Za-z0-9_']*"
    r"|Conditional[A-Za-z0-9_']*"
    r")"
)

@dataclass(frozen=True)
class DebtFinding:
    """One proof-debt token in a paper-facing Lean declaration header."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str
    token_line: int
    header_excerpt: str


@dataclass(frozen=True)
class ClassifiedFinding:
    """One detected token with a mathematical classification and citation."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str
    token_line: int
    header_excerpt: str
    reason: str


@dataclass(frozen=True)
class ConditionalDeclarationNameFinding:
    """One conditional declaration name used for a paper-facing blueprint entry."""

    blueprint_file: str
    blueprint_line: int
    env_type: str
    label: str | None
    lean_decl: str
    lean_file: str
    lean_line: int
    token: str


@dataclass(frozen=True)
class AuditResult:
    """Summary of the paper-facing proof-debt audit."""

    scanned_refs: int
    missing_refs: tuple[str, ...]
    findings: tuple[DebtFinding, ...]
    conditional_decl_findings: tuple[ConditionalDeclarationNameFinding, ...]
    faithful_boundary_findings: tuple[ClassifiedFinding, ...]
    external_citation_findings: tuple[ClassifiedFinding, ...]
    source_context_findings: tuple[ClassifiedFinding, ...]

    @property
    def ok(self) -> bool:
        return (
            not self.findings
            and not self.conditional_decl_findings
            and not self.missing_refs
        )


def paper_facing_entries(
    blueprint_src: Path,
    *,
    include_informational_envs: bool = False,
) -> list[BlueprintEntry]:
    """Return paper-facing blueprint entries that carry a Lean reference."""
    envs = THEOREM_LIKE_ENVS
    if include_informational_envs:
        envs = envs | INFORMATIONAL_ENVS
    return [
        entry
        for entry in collect_blueprint_entries(blueprint_src)
        if entry.env_type in envs
    ]


def _header_after_decl_name(text: str) -> str:
    """Remove the declaration keyword and name from a Lean declaration header."""
    match = LEAN_DECL_RE.match(text)
    if not match:
        return text
    return text[match.end() :]


def _public_header_after_name(source: str, decl: LeanDecl) -> tuple[str, int]:
    """Return the public header, excluding the declaration name.

    The returned line number is the line of the first character in the returned
    text, so token line numbers can be computed without reparsing the file.
    """
    stripped_lines = strip_lean_comments_preserve_lines(source)
    candidate = "\n".join(stripped_lines[decl.line - 1 : decl.end_line])

    stack: list[str] = []
    end = len(candidate)
    i = 0
    while i < len(candidate):
        if candidate.startswith(":=", i) and not stack:
            end = i
            break
        if starts_keyword(candidate, i, "where") and not stack:
            end = i
            break
        advance_depth(candidate[i], stack)
        i += 1

    header = candidate[:end]
    after_name = _header_after_decl_name(header)
    skipped_lines = header[: len(header) - len(after_name)].count("\n")
    return after_name, decl.line + skipped_lines


def _public_inputs_before_result_type(header_after_name: str) -> str:
    """Return the public input part before the declaration result type.

    The audit is meant to detect extra hypotheses or input data on
    paper-facing declarations.  Mathematical result types may legitimately
    mention words such as ``Residual``; those are handled by statement review,
    not by this input-debt scanner.
    """
    stack: list[str] = []
    for i, char in enumerate(header_after_name):
        if char == ":" and not stack:
            return header_after_name[:i]
        advance_depth(char, stack)
    return header_after_name


def _line_excerpt(text: str, one_based_line: int) -> str:
    lines = text.splitlines()
    if one_based_line < 1 or one_based_line > len(lines):
        return ""
    return " ".join(lines[one_based_line - 1].strip().split())


def _faithful_boundary_reason(token: str) -> str | None:
    """Return the paper citation when ``token`` is a faithful boundary input."""
    return FAITHFUL_BOUNDARY_TOKENS.get(token)


def _external_citation_reason(token: str) -> str | None:
    """Return the citation when ``token`` names an external theorem interface."""
    return EXTERNAL_CITATION_TOKENS.get(token)


def _source_context_reason(token: str) -> str | None:
    """Return the citation when ``token`` names fixed source construction context."""
    return SOURCE_CONTEXT_TOKENS.get(token)


def _source_context_conditional_decl_reason(decl_name: str) -> str | None:
    """Return the citation when a conditional-looking name is Lean-only context."""
    return SOURCE_CONTEXT_CONDITIONAL_DECL_NAMES.get(decl_name)


def _is_ignored_broad_binder_token(token: str, *, broad_vocabulary: bool) -> bool:
    """Return whether ``token`` is only a broad-mode local binder name."""
    return broad_vocabulary and token in IGNORED_BROAD_BINDER_TOKENS


def _classified_finding(
    entry: BlueprintEntry,
    decl: LeanDecl,
    *,
    token: str,
    token_line: int,
    header_excerpt: str,
    reason: str,
) -> ClassifiedFinding:
    """Return a classified finding for a detected public-input token."""
    return ClassifiedFinding(
        blueprint_file=entry.file,
        blueprint_line=entry.line,
        env_type=entry.env_type,
        label=entry.label,
        lean_decl=entry.lean_decl,
        lean_file=decl.file,
        lean_line=decl.line,
        token=token,
        token_line=token_line,
        header_excerpt=header_excerpt,
        reason=reason,
    )


def _conditional_decl_name_finding(
    entry: BlueprintEntry,
    decl: LeanDecl,
) -> ConditionalDeclarationNameFinding | None:
    """Return a finding when a paper-facing entry references a conditional name."""
    basename = entry.lean_decl.rsplit(".", 1)[-1]
    match = CONDITIONAL_DECL_NAME_RE.search(basename)
    if match is None:
        return None
    return ConditionalDeclarationNameFinding(
        blueprint_file=entry.file,
        blueprint_line=entry.line,
        env_type=entry.env_type,
        label=entry.label,
        lean_decl=entry.lean_decl,
        lean_file=decl.file,
        lean_line=decl.line,
        token=match.group(0),
    )


def _findings_for_entry(
    root: Path,
    entry: BlueprintEntry,
    decl: LeanDecl,
    *,
    broad_vocabulary: bool,
) -> tuple[
    list[DebtFinding],
    list[ClassifiedFinding],
    list[ClassifiedFinding],
    list[ClassifiedFinding],
]:
    lean_path = root / decl.file
    source = lean_path.read_text(encoding="utf-8", errors="replace")
    header, header_start_line = _public_header_after_name(source, decl)
    public_inputs = _public_inputs_before_result_type(header)

    findings: list[DebtFinding] = []
    faithful_boundary_findings: list[ClassifiedFinding] = []
    external_citation_findings: list[ClassifiedFinding] = []
    source_context_findings: list[ClassifiedFinding] = []
    debt_token_re = BROAD_DEBT_TOKEN_RE if broad_vocabulary else STRICT_DEBT_TOKEN_RE
    for match in debt_token_re.finditer(public_inputs):
        token = match.group(0)
        if _is_ignored_broad_binder_token(token, broad_vocabulary=broad_vocabulary):
            continue
        token_line = header_start_line + line_number(public_inputs, match.start()) - 1
        local_line = line_number(public_inputs, match.start())
        header_excerpt = _line_excerpt(public_inputs, local_line)
        reason = _faithful_boundary_reason(token)
        if reason is not None:
            faithful_boundary_findings.append(
                _classified_finding(
                    entry,
                    decl,
                    token=token,
                    token_line=token_line,
                    header_excerpt=header_excerpt,
                    reason=reason,
                )
            )
            continue
        source_context_reason = _source_context_reason(token)
        if broad_vocabulary and source_context_reason is not None:
            source_context_findings.append(
                _classified_finding(
                    entry,
                    decl,
                    token=token,
                    token_line=token_line,
                    header_excerpt=header_excerpt,
                    reason=source_context_reason,
                )
            )
            continue
        external_reason = _external_citation_reason(token)
        if broad_vocabulary and external_reason is not None:
            external_citation_findings.append(
                _classified_finding(
                    entry,
                    decl,
                    token=token,
                    token_line=token_line,
                    header_excerpt=header_excerpt,
                    reason=external_reason,
                )
            )
            continue
        findings.append(
            DebtFinding(
                blueprint_file=entry.file,
                blueprint_line=entry.line,
                env_type=entry.env_type,
                label=entry.label,
                lean_decl=entry.lean_decl,
                lean_file=decl.file,
                lean_line=decl.line,
                token=token,
                token_line=token_line,
                header_excerpt=header_excerpt,
            )
        )
    return (
        findings,
        faithful_boundary_findings,
        external_citation_findings,
        source_context_findings,
    )


def run_audit(
    root: Path,
    *,
    broad_vocabulary: bool = False,
    include_informational_envs: bool = False,
) -> AuditResult:
    """Run the paper-facing proof-debt audit for ``root``."""
    root = root.resolve()
    load_registers(root)
    blueprint_src = root / "blueprint" / "src"
    lean_root = root / project_config.get(project_config.load(root), "project.lean_root")

    entries = paper_facing_entries(
        blueprint_src,
        include_informational_envs=include_informational_envs,
    )
    decls = collect_lean_decls(lean_root)

    missing: list[str] = []
    findings: list[DebtFinding] = []
    conditional_decl_findings: list[ConditionalDeclarationNameFinding] = []
    faithful_boundary_findings: list[ClassifiedFinding] = []
    external_citation_findings: list[ClassifiedFinding] = []
    source_context_findings: list[ClassifiedFinding] = []
    for entry in entries:
        decl = decls.get(entry.lean_decl)
        if decl is None:
            missing.append(entry.lean_decl)
            continue
        if conditional_finding := _conditional_decl_name_finding(entry, decl):
            source_context_reason = _source_context_conditional_decl_reason(entry.lean_decl)
            if (
                broad_vocabulary
                and include_informational_envs
                and entry.env_type in INFORMATIONAL_ENVS
                and source_context_reason is not None
            ):
                source_context_findings.append(
                    _classified_finding(
                        entry,
                        decl,
                        token=conditional_finding.token,
                        token_line=decl.line,
                        header_excerpt="",
                        reason=source_context_reason,
                    )
                )
            else:
                conditional_decl_findings.append(conditional_finding)
        entry_findings, entry_faithful, entry_external, entry_source_context = _findings_for_entry(
            root,
            entry,
            decl,
            broad_vocabulary=broad_vocabulary,
        )
        findings.extend(entry_findings)
        faithful_boundary_findings.extend(entry_faithful)
        external_citation_findings.extend(entry_external)
        source_context_findings.extend(entry_source_context)

    return AuditResult(
        scanned_refs=len(entries),
        missing_refs=tuple(sorted(set(missing))),
        findings=tuple(findings),
        conditional_decl_findings=tuple(conditional_decl_findings),
        faithful_boundary_findings=tuple(faithful_boundary_findings),
        external_citation_findings=tuple(external_citation_findings),
        source_context_findings=tuple(source_context_findings),
    )


def _print_classified_findings(title: str, findings: tuple[ClassifiedFinding, ...]) -> None:
    """Print findings that carry a mathematical classification."""
    print(f"{title}: {len(findings)}")
    for finding in findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.token_line}: "
            f"{finding.lean_decl} contains {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )
        print(f"    {finding.reason}")
        if finding.header_excerpt:
            print(f"    {finding.header_excerpt}")


def print_text_report(result: AuditResult) -> None:
    """Print a human-readable audit report."""
    print(f"Scanned paper-facing Lean references: {result.scanned_refs}")
    if result.missing_refs:
        print(f"Missing Lean references: {len(result.missing_refs)}")
        for decl in result.missing_refs:
            print(f"  - {decl}")
    else:
        print("Missing Lean references: 0")

    print(f"Proof-debt header findings: {len(result.findings)}")
    for finding in result.findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.token_line}: "
            f"{finding.lean_decl} contains {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )
        if finding.header_excerpt:
            print(f"    {finding.header_excerpt}")

    print(f"Conditional declaration-name findings: {len(result.conditional_decl_findings)}")
    for finding in result.conditional_decl_findings:
        label = f" label={finding.label}" if finding.label else ""
        print(
            f"  - {finding.lean_file}:{finding.lean_line}: "
            f"{finding.lean_decl} has conditional name token {finding.token!r}"
        )
        print(
            f"    blueprint {finding.blueprint_file}:{finding.blueprint_line} "
            f"env={finding.env_type}{label}"
        )

    _print_classified_findings(
        "Faithful boundary input findings",
        result.faithful_boundary_findings,
    )
    _print_classified_findings(
        "External citation input findings",
        result.external_citation_findings,
    )
    _print_classified_findings(
        "Source construction context findings",
        result.source_context_findings,
    )


def _json_default(value: object) -> object:
    if isinstance(value, tuple):
        return list(value)
    raise TypeError(f"Object of type {type(value).__name__} is not JSON serializable")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."), help="repository root")
    parser.add_argument("--json", action="store_true", help="print JSON instead of text")
    parser.add_argument("--ci", action="store_true", help="exit non-zero on findings")
    parser.add_argument(
        "--broad-vocabulary",
        action="store_true",
        help=(
            "also scan broad tracker vocabulary such as Statement, Witness, "
            "Data, Output, Conclusion, and Compatibility"
        ),
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="with --ci, report findings but keep exit code 0",
    )
    parser.add_argument(
        "--include-informational-envs",
        action="store_true",
        help=(
            "also scan blueprint definition, remark, and example entries; this "
            "is intended for report-only frontier audits, not for the default "
            "paper-theorem blocking gate"
        ),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    result = run_audit(
        args.root,
        broad_vocabulary=args.broad_vocabulary,
        include_informational_envs=args.include_informational_envs,
    )

    if args.json:
        print(json.dumps(asdict(result), indent=2, sort_keys=True, default=_json_default))
    else:
        print_text_report(result)

    if args.ci and not args.warn_only and not result.ok:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
