#!/usr/bin/env python3
"""Shared GitHub access for the local workflow.

GitHub is the sole authority for active issues and pull requests.  This module
centralizes CLI and repository discovery, the functional authentication probe,
REST headers, JSON handling, pagination, bounded retries, and idempotent
publication markers.  It deliberately has no offline mutation path.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence, TypeVar


API_VERSION = "2022-11-28"
ACCEPT = "application/vnd.github+json"
DOCUMENTED_REPOSITORY = "Dengnifer/MIPStarRE-A"
CANONICAL_CI_STEPS = (
    "build",
    "blueprint-render",
    "paper-gaps",
    "blueprint-sync",
    "file-length",
    "proof-debt",
    "proof-evasion",
    "statement-origin",
)
CANONICAL_CI_CONTEXTS = tuple(f"local-ci/{step}" for step in CANONICAL_CI_STEPS)
CI_SUMMARY_CONTEXT = "local-ci/summary"
REVIEW_CONTEXT = "local-review/summary"
AUTO_FIX_PREFIXES = ("[codex-auto-fix]", "[codex-review-fix]")
AUTO_FIX_LABEL = "auto-fix-codex"
ADJUDICATION_LABEL = "adjudicated"

_CI_MARKER_RE = re.compile(
    r"<!-- mipstarre:ci-manifest pr=(\d+) "
    r"head=((?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})) run=([^<>\s]+) -->"
)
_REVIEW_MARKER_RE = re.compile(
    r"<!-- mipstarre:review-attestation pr=(\d+) "
    r"head=((?:[0-9a-f]{40}|[0-9a-f]{64})) "
    r"base=((?:[0-9a-f]{40}|[0-9a-f]{64})) run=([^<>\s]+) "
    r"findings=(\d+) event=(COMMENT) fallback=(none) "
    r"digest=([0-9a-f]{64}) -->"
)
_REVIEW_ATTESTATION_RE = re.compile(
    r"## Review attestation\n\n```json\n(.*?)\n```\n\n$", re.DOTALL
)
_CANONICAL_FINDING_LINE_RE = re.compile(
    r"^- \[( |x|-)\] F([1-9]\d*) "
    r"\((blocker|changes|advisory)\) "
    r"`(-|(?:(?!\.{1,2}/)[A-Za-z0-9._+-]+/)*"
    r"(?!\.{1,2}:)[A-Za-z0-9._+-]+:[1-9]\d*)` "
    r"— (\S(?:.*\S)?)$"
)
_SESSION_NAME_RE = re.compile(r"^reviewer-[A-Za-z0-9._-]+$")
_THREAD_ID_RE = re.compile(r"^[A-Za-z0-9._:-]{8,200}$")
_RUN_ID_RE = re.compile(r"^[A-Za-z0-9._:-]{1,28}$")
_ACTOR_RE = re.compile(
    r"^(?=.{1,39}$)[A-Za-z0-9](?:[A-Za-z0-9-]*[A-Za-z0-9])?$"
)

_REPO_RE = re.compile(r"^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$")
_HTTP_RE = re.compile(r"(?:HTTP|status(?: code)?)\D*(\d{3})", re.IGNORECASE)
_TRANSIENT_TEXT = (
    "connection reset",
    "connection refused",
    "connection timed out",
    "context deadline exceeded",
    "could not resolve host",
    "dial tcp",
    "eof",
    "network is unreachable",
    "service unavailable",
    "temporary failure",
    "timeout",
    "timed out",
    "tls handshake timeout",
)
_RATE_LIMIT_TEXT = (
    "api rate limit exceeded",
    "rate limit exceeded",
    "secondary rate limit",
    "retry-after",
    "retry after",
)
_MARKER_RE = re.compile(r"^<!-- mipstarre:[a-z0-9-]+(?: [^<>\r\n]+)* -->$")
_SHA_RE = re.compile(r"(?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})")


class GitHubError(RuntimeError):
    """A safe, classified GitHub operation failure."""

    def __init__(
        self,
        message: str,
        *,
        status: int | None = None,
        transient: bool = False,
        stdout: str = "",
    ) -> None:
        super().__init__(message)
        self.status = status
        self.transient = transient
        self.stdout = stdout


@dataclass(frozen=True)
class CommandResult:
    stdout: str
    stderr: str


@dataclass(frozen=True)
class ReviewLaneEvidence:
    """One independently dispatched reviewer lane."""

    lane: str
    name: str
    thread_id: str
    exit: int
    worktree: str
    start: str
    end: str

    def as_dict(self) -> dict[str, Any]:
        return {
            "lane": self.lane,
            "name": self.name,
            "thread_id": self.thread_id,
            "exit": self.exit,
            "worktree": self.worktree,
            "start": self.start,
            "end": self.end,
        }


@dataclass(frozen=True)
class ReviewFinding:
    """One canonical finding from an attested reviewer lane."""

    lane: str
    identifier: int
    state: str
    severity: str
    location: str
    summary: str

    @property
    def key(self) -> str:
        return f"{self.lane}:F{self.identifier}"

    def as_dict(self) -> dict[str, Any]:
        return {
            "key": self.key,
            "lane": self.lane,
            "identifier": self.identifier,
            "state": self.state,
            "severity": self.severity,
            "location": self.location,
            "summary": self.summary,
        }


@dataclass(frozen=True)
class ReviewAttestation:
    """Strictly parsed marker-bound local review publication."""

    number: int
    head_sha: str
    base_sha: str
    run_id: str
    findings: int
    event: str
    fallback: str
    digest: str
    lanes: tuple[ReviewLaneEvidence, ...]
    finding_rows: tuple[ReviewFinding, ...]
    row: dict[str, Any]

    def as_dict(self) -> dict[str, Any]:
        return {
            "pr": self.number,
            "head_sha": self.head_sha,
            "base_sha": self.base_sha,
            "run_id": self.run_id,
            "canonical_findings": self.findings,
            "event": self.event,
            "fallback": self.fallback,
            "digest": self.digest,
            "lanes": [lane.as_dict() for lane in self.lanes],
            "findings": [finding.as_dict() for finding in self.finding_rows],
        }


@dataclass(frozen=True)
class ReviewEvidence:
    """A review attestation plus its matching exact-head commit status."""

    attestation: ReviewAttestation
    status: dict[str, Any]

    def as_dict(self) -> dict[str, Any]:
        return {**self.attestation.as_dict(), "status": self.status}


@dataclass(frozen=True)
class CIManifestEvidence:
    """A canonical CI manifest and the statuses produced by the same run."""

    number: int
    head_sha: str
    base_sha: str
    run_id: str
    digest: str
    row: dict[str, Any]
    manifest: dict[str, Any]
    statuses: dict[str, dict[str, Any]]

    def as_dict(self) -> dict[str, Any]:
        return {
            "pr": self.number,
            "head_sha": self.head_sha,
            "base_sha": self.base_sha,
            "run_id": self.run_id,
            "digest": self.digest,
            "manifest": self.manifest,
            "statuses": self.statuses,
        }


@dataclass(frozen=True)
class PullIdentity:
    """The refs and full commit identities that define a PR comparison."""

    branch: str
    base: str
    head_sha: str
    base_sha: str


T = TypeVar("T")


def _safe_text(text: str | bytes | None) -> str:
    """Strip controls and redact token-valued environment variables."""
    if text is None:
        text = ""
    if isinstance(text, bytes):
        text = text.decode("utf-8", errors="replace")
    clean = "".join(ch for ch in text if ch in "\n\t" or ord(ch) >= 32)
    for name, value in os.environ.items():
        if "TOKEN" in name.upper() and value:
            clean = clean.replace(value, "<redacted>")
    return clean.strip()[:2000]


def _status_from_stderr(stderr: str) -> int | None:
    match = _HTTP_RE.search(stderr)
    if match:
        return int(match.group(1))
    match = re.search(r"\b(4\d\d|5\d\d)\b", stderr)
    return int(match.group(1)) if match else None


def _is_transient(stderr: str, status: int | None) -> bool:
    if status == 429 or (status is not None and 500 <= status <= 599):
        return True
    lowered = stderr.lower()
    if status == 403 and any(fragment in lowered for fragment in _RATE_LIMIT_TEXT):
        return True
    return any(fragment in lowered for fragment in _TRANSIENT_TEXT)


def stable_digest(payload: Any, *, length: int = 24) -> str:
    encoded = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()[:length]


def stable_marker(kind: str, **parts: object) -> str:
    rendered = " ".join(f"{key}={value}" for key, value in parts.items())
    return f"<!-- mipstarre:{kind}{(' ' + rendered) if rendered else ''} -->"


def create_marker(kind: str, payload: Any) -> str:
    return stable_marker(f"{kind}-create", id=stable_digest(payload))


def normalize_number(value: str | int, *, kind: str = "number") -> int:
    text = str(value)
    if not re.fullmatch(r"[1-9]\d*", text):
        raise GitHubError(f"{kind} must be a positive GitHub number, got {text!r}")
    return int(text)


def normalize_sha(value: str, *, kind: str = "commit SHA") -> str:
    text = str(value).strip()
    if not _SHA_RE.fullmatch(text):
        raise GitHubError(f"{kind} must be an exact 40- or 64-hex SHA, got {text!r}")
    return text.lower()


def normalize_actor(value: Any, *, kind: str = "GitHub actor") -> str:
    """Validate one GitHub user login used as an evidence principal."""
    if not isinstance(value, str) or value != value.strip():
        raise GitHubError(f"{kind} is not a valid GitHub user login: {value!r}")
    text = value
    if not _ACTOR_RE.fullmatch(text):
        raise GitHubError(f"{kind} is not a valid GitHub user login: {text!r}")
    return text


def render_status_description(
    sha: str, context: str, state: str, description: str
) -> str:
    """Render the exact digest-suffixed description stored by GitHub."""
    sha = normalize_sha(sha)
    digest = stable_digest(
        {
            "sha": sha,
            "context": context.casefold(),
            "state": state,
            "description": description,
        },
        length=16,
    )
    suffix = f" [mip:{digest}]"
    return description[: 140 - len(suffix)].rstrip() + suffix


def review_status_description(attestation: ReviewAttestation) -> str:
    verdict = (
        "clean"
        if attestation.event == "COMMENT" and attestation.findings == 0
        else f"findings={attestation.findings}"
    )
    return (
        f"local review digest={attestation.digest} "
        f"run={attestation.run_id} {verdict}"
    )


def review_summary_state(attestation: ReviewAttestation) -> str:
    """Return the summary state without conflating it with raw validity."""
    if (
        attestation.event == "COMMENT"
        and attestation.fallback == "none"
        and attestation.findings == 0
        and str(attestation.row.get("state") or "").upper() == "COMMENTED"
    ):
        return "success"
    return "failure"


def review_pending_description(run_id: str) -> str:
    """Return the canonical pending description for one review run."""
    if not _RUN_ID_RE.fullmatch(run_id):
        raise GitHubError("review run id is invalid")
    return f"local review run={run_id} is pending"


def ci_pending_description(run_id: str) -> str:
    """Return the canonical pending description for one complete CI run."""
    if not _RUN_ID_RE.fullmatch(run_id):
        raise GitHubError("CI run id is invalid")
    return f"local CI run={run_id} is pending"


def ci_manifest_digest(manifest: dict[str, Any]) -> str:
    """Hash the parsed manifest independently of comment JSON formatting."""
    return hashlib.sha256(
        json.dumps(
            manifest, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()


def ci_summary_description(evidence: CIManifestEvidence) -> str:
    conclusion = str(evidence.manifest.get("conclusion") or "")
    verdict = {
        "success": "passed",
        "failure": "failed",
        "error": "could not run",
    }.get(conclusion)
    if verdict is None:
        raise GitHubError("CI evidence has an invalid summary conclusion")
    return (
        f"local CI digest={evidence.digest} run={evidence.run_id} {verdict}"
    )


def ci_summary_state(evidence: CIManifestEvidence) -> str:
    conclusion = str(evidence.manifest.get("conclusion") or "")
    if conclusion not in {"success", "failure", "error"}:
        raise GitHubError("CI evidence has an invalid summary conclusion")
    return conclusion


def ci_status_description(run_id: str, step: dict[str, Any]) -> tuple[str, str]:
    """Return the state and undigested description for one manifest step."""
    outcome = str(step.get("outcome") or "")
    note = str(step.get("note") or "")
    if outcome == "skipped":
        return "success", f"local CI run={run_id} skipped: {note or 'not applicable'}"
    if outcome == "success":
        return "success", f"local CI run={run_id} passed"
    if outcome == "failure":
        suffix = f": {note}" if note else ""
        return "failure", f"local CI run={run_id} failed{suffix}"
    if outcome == "error":
        suffix = f": {note}" if note else ""
        return "error", f"local CI run={run_id} could not run{suffix}"
    raise GitHubError(f"CI manifest step has invalid outcome {outcome!r}")


def _parse_timestamp(value: Any, *, field: str) -> datetime:
    text = str(value or "")
    if not text:
        raise GitHubError(f"review evidence has an empty {field} timestamp")
    try:
        parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError as exc:
        raise GitHubError(f"review evidence has an invalid {field} timestamp") from exc
    if parsed.utcoffset() is None:
        raise GitHubError(f"review evidence has a timezone-free {field} timestamp")
    return parsed


def _same_number(value: Any, expected: int) -> bool:
    text = str(value or "")
    return bool(re.fullmatch(r"\d+", text)) and int(text) == expected


def _read_session_records(path: Path) -> list[dict[str, Any]]:
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        raise GitHubError(f"review session telemetry is unavailable at {path}") from exc
    records: list[dict[str, Any]] = []
    for line_number, raw in enumerate(lines, start=1):
        if not raw.strip():
            continue
        try:
            row = json.loads(raw)
        except json.JSONDecodeError as exc:
            raise GitHubError(
                f"review session telemetry has invalid JSON on line {line_number}"
            ) from exc
        if not isinstance(row, dict):
            raise GitHubError(
                f"review session telemetry line {line_number} is not an object"
            )
        records.append(row)
    return records


def _validate_session_record(
    lane: ReviewLaneEvidence,
    *,
    records: Sequence[dict[str, Any]],
    number: int,
    worktree: str,
) -> None:
    matching = [row for row in records if str(row.get("name") or "") == lane.name]
    if len(matching) != 1:
        raise GitHubError(
            f"reviewer session {lane.name!r} must have exactly one completion record"
        )
    row = matching[0]
    expected_worktree = str(Path(worktree).resolve())
    actual_worktree = str(Path(str(row.get("worktree") or "")).resolve())
    checks = {
        "role": str(row.get("role") or "") == "reviewer",
        "PR": _same_number(row.get("pr"), number),
        "issue": str(row.get("issue") or "") == f"pr{number}",
        "thread": str(row.get("thread_id") or "") == lane.thread_id,
        "exit": type(row.get("exit")) is int and row.get("exit") == 0 == lane.exit,
        "status": str(row.get("status") or "") == "done",
        "worktree": actual_worktree == expected_worktree == lane.worktree,
        "start": str(row.get("start") or "") == lane.start,
        "end": str(row.get("end") or "") == lane.end,
    }
    failed = [name for name, accepted in checks.items() if not accepted]
    if failed:
        raise GitHubError(
            f"reviewer session {lane.name!r} has mismatched completion telemetry: "
            + ", ".join(failed)
        )
    if sum(
        str(other.get("thread_id") or "") == lane.thread_id for other in records
    ) != 1:
        raise GitHubError(
            f"reviewer thread {lane.thread_id!r} does not identify one fresh session"
        )


def validate_reviewer_session(
    dispatch_log: Path,
    telemetry_path: Path,
    *,
    lane: str,
    number: int,
    worktree: Path,
    expected_exit: int,
) -> ReviewLaneEvidence:
    """Validate one dispatch result against append-only session telemetry."""
    if lane not in {"code", "prose"}:
        raise GitHubError(f"invalid reviewer lane {lane!r}")
    try:
        lines = dispatch_log.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        raise GitHubError(f"review dispatch log is unavailable at {dispatch_log}") from exc
    fields: dict[str, str] = {}
    for line in lines:
        key, separator, value = line.partition(": ")
        if separator and key in {"name", "thread_id", "exit"}:
            if key in fields:
                raise GitHubError(f"review dispatch log repeats its {key} field")
            fields[key] = value.strip()
    name = fields.get("name", "")
    thread_id = fields.get("thread_id", "")
    try:
        dispatch_exit = int(fields.get("exit", ""))
    except ValueError as exc:
        raise GitHubError("review dispatch log has no valid exit code") from exc
    if expected_exit != 0 or dispatch_exit != 0 or expected_exit != dispatch_exit:
        raise GitHubError(
            f"reviewer lane {lane} exited nonzero "
            f"(wrapper={expected_exit}, dispatch={dispatch_exit})"
        )
    if not _SESSION_NAME_RE.fullmatch(name):
        raise GitHubError(f"reviewer lane {lane} has an invalid or empty session name")
    if not _THREAD_ID_RE.fullmatch(thread_id):
        raise GitHubError(f"reviewer lane {lane} has an invalid or empty thread_id")

    records = _read_session_records(telemetry_path)
    matching = [row for row in records if str(row.get("name") or "") == name]
    if len(matching) != 1:
        raise GitHubError(
            f"reviewer session {name!r} must have exactly one completion record"
        )
    row = matching[0]
    resolved_worktree = str(worktree.resolve())
    evidence = ReviewLaneEvidence(
        lane=lane,
        name=name,
        thread_id=thread_id,
        exit=dispatch_exit,
        worktree=resolved_worktree,
        start=str(row.get("start") or ""),
        end=str(row.get("end") or ""),
    )
    start = _parse_timestamp(evidence.start, field=f"{lane} start")
    end = _parse_timestamp(evidence.end, field=f"{lane} end")
    if end < start:
        raise GitHubError(f"reviewer lane {lane} ends before it starts")
    _validate_session_record(
        evidence, records=records, number=number, worktree=resolved_worktree
    )
    return evidence


def _validated_marker(marker: str, body: str) -> None:
    if not _MARKER_RE.fullmatch(marker):
        raise GitHubError(f"invalid or missing idempotency marker: {marker!r}")
    if body.count(marker) != 1:
        raise GitHubError("idempotent publication body must contain its marker exactly once")


def _marker_value(marker: str, key: str) -> str | None:
    match = re.search(rf"(?:^| ){re.escape(key)}=([^<>\s]+)(?= | -->)", marker)
    return match.group(1) if match else None


def _review_attestation_from_row(
    row: dict[str, Any], number: int
) -> ReviewAttestation:
    body = str(row.get("body") or "")
    markers = list(_REVIEW_MARKER_RE.finditer(body))
    if len(markers) != 1 or body.count("<!-- mipstarre:review-attestation ") != 1:
        raise GitHubError("review attestation must contain exactly one valid marker")
    marker_match = markers[0]
    marker = marker_match.group(0)
    suffix = body[marker_match.start() :]
    if suffix not in {marker, marker + "\n"}:
        raise GitHubError("review attestation marker must be the final body line")
    prefix = body[: marker_match.start()]
    digest = hashlib.sha256(prefix.encode("utf-8")).hexdigest()
    if digest != marker_match.group(8):
        raise GitHubError("review attestation digest does not cover the canonical body")

    fenced = _REVIEW_ATTESTATION_RE.search(prefix)
    if fenced is None:
        raise GitHubError("review body has no final JSON attestation block")
    if prefix.count("## Review attestation") != 1:
        raise GitHubError("review body has an ambiguous attestation section")
    try:
        payload = json.loads(fenced.group(1))
    except json.JSONDecodeError as exc:
        raise GitHubError(f"review attestation is invalid JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise GitHubError("review attestation JSON is not an object")
    expected_keys = {
        "schema",
        "pr",
        "head_sha",
        "base_sha",
        "run_id",
        "canonical_findings",
        "event",
        "fallback",
        "lanes",
    }
    if (
        set(payload) != expected_keys
        or type(payload.get("schema")) is not int
        or payload.get("schema") != 1
    ):
        raise GitHubError("review attestation has an unsupported or noncanonical schema")

    marker_pr = int(marker_match.group(1))
    marker_head = normalize_sha(marker_match.group(2), kind="review head SHA")
    marker_base = normalize_sha(marker_match.group(3), kind="review base SHA")
    marker_run = marker_match.group(4)
    marker_findings = int(marker_match.group(5))
    marker_event = marker_match.group(6)
    marker_fallback = marker_match.group(7)
    if (
        marker_pr != number
        or type(payload.get("pr")) is not int
        or payload.get("pr") != number
    ):
        raise GitHubError("review attestation names a different PR")
    try:
        payload_head = normalize_sha(payload.get("head_sha"), kind="attested head SHA")
        payload_base = normalize_sha(payload.get("base_sha"), kind="attested base SHA")
    except TypeError as exc:
        raise GitHubError("review attestation has invalid full SHAs") from exc
    comparisons = {
        "head SHA": payload_head == marker_head,
        "base SHA": payload_base == marker_base,
        "run id": payload.get("run_id") == marker_run,
        "findings count": (
            type(payload.get("canonical_findings")) is int
            and payload.get("canonical_findings") == marker_findings
        ),
        "event": payload.get("event") == marker_event,
        "fallback": payload.get("fallback") == marker_fallback,
    }
    mismatched = [name for name, accepted in comparisons.items() if not accepted]
    if mismatched:
        raise GitHubError(
            "review marker and JSON attestation disagree on " + ", ".join(mismatched)
        )
    if not _RUN_ID_RE.fullmatch(marker_run):
        raise GitHubError("review attestation has an invalid run id")

    raw_lanes = payload.get("lanes")
    if not isinstance(raw_lanes, list) or len(raw_lanes) not in {1, 2}:
        raise GitHubError("review attestation must contain one or two reviewer lanes")
    lanes: list[ReviewLaneEvidence] = []
    lane_keys = {"lane", "name", "thread_id", "exit", "worktree", "start", "end"}
    for raw in raw_lanes:
        if not isinstance(raw, dict) or set(raw) != lane_keys:
            raise GitHubError("review attestation contains a noncanonical lane object")
        lane = ReviewLaneEvidence(
            lane=str(raw.get("lane") or ""),
            name=str(raw.get("name") or ""),
            thread_id=str(raw.get("thread_id") or ""),
            exit=raw.get("exit") if type(raw.get("exit")) is int else -1,
            worktree=str(raw.get("worktree") or ""),
            start=str(raw.get("start") or ""),
            end=str(raw.get("end") or ""),
        )
        if lane.lane not in {"code", "prose"}:
            raise GitHubError("review attestation contains an invalid lane name")
        if not _SESSION_NAME_RE.fullmatch(lane.name):
            raise GitHubError("review attestation contains an invalid session name")
        if not _THREAD_ID_RE.fullmatch(lane.thread_id):
            raise GitHubError("review attestation contains an invalid thread id")
        if lane.exit != 0:
            raise GitHubError("review attestation contains a nonzero reviewer exit")
        if not Path(lane.worktree).is_absolute() or str(Path(lane.worktree)) != lane.worktree:
            raise GitHubError("review attestation contains a noncanonical worktree")
        start = _parse_timestamp(lane.start, field=f"{lane.lane} start")
        end = _parse_timestamp(lane.end, field=f"{lane.lane} end")
        if end < start:
            raise GitHubError("review attestation contains reversed lane timestamps")
        lanes.append(lane)
    if [lane.lane for lane in lanes] not in [["code"], ["code", "prose"]]:
        raise GitHubError("review attestation lane order must be code, then optional prose")
    if len({lane.name for lane in lanes}) != len(lanes):
        raise GitHubError("review attestation reuses a reviewer session name")
    if len({lane.thread_id for lane in lanes}) != len(lanes):
        raise GitHubError("review attestation reuses a reviewer thread id")
    if len({lane.worktree for lane in lanes}) != 1:
        raise GitHubError("review attestation lanes name different worktrees")

    canonical_sections = re.findall(
        r"<!-- findings:begin -->\n(.*?)<!-- findings:end -->", prefix, re.DOTALL
    )
    if len(canonical_sections) != len(lanes):
        raise GitHubError("review body does not contain one canonical ledger per lane")
    canonical_findings = 0
    finding_rows: list[ReviewFinding] = []
    states = {" ": "unresolved", "x": "resolved", "-": "outdated"}
    for lane, section in zip(lanes, canonical_sections, strict=True):
        lines = section.splitlines()
        if lines == ["- none"]:
            continue
        if not lines:
            raise GitHubError("review ledger must contain '- none' or canonical findings")
        identifiers: set[int] = set()
        for line in lines:
            match = _CANONICAL_FINDING_LINE_RE.fullmatch(line)
            if match is None:
                raise GitHubError("review body contains a malformed canonical finding")
            identifier = int(match.group(2))
            if identifier in identifiers:
                raise GitHubError("review ledger repeats a finding identifier")
            identifiers.add(identifier)
            finding_rows.append(
                ReviewFinding(
                    lane=lane.lane,
                    identifier=identifier,
                    state=states[match.group(1)],
                    severity=match.group(3),
                    location=match.group(4),
                    summary=match.group(5),
                )
            )
            if match.group(1) == " ":
                canonical_findings += 1
    if canonical_findings != marker_findings:
        raise GitHubError("review attestation findings count does not match the ledger")

    commit_id = normalize_sha(
        str(row.get("commit_id") or ""), kind="review commit SHA"
    )
    if commit_id != marker_head:
        raise GitHubError("review attestation commit_id differs from its full head SHA")
    if (
        marker_event != "COMMENT"
        or marker_fallback != "none"
        or str(row.get("state") or "").upper() != "COMMENTED"
    ):
        raise GitHubError(
            "local review attestations must use COMMENT with fallback=none"
        )
    return ReviewAttestation(
        number=number,
        head_sha=marker_head,
        base_sha=marker_base,
        run_id=marker_run,
        findings=marker_findings,
        event=marker_event,
        fallback=marker_fallback,
        digest=digest,
        lanes=tuple(lanes),
        finding_rows=tuple(finding_rows),
        row=row,
    )


def discover_gh() -> Path:
    override = os.environ.get("MIPSTARRE_GH")
    if override:
        path = Path(override).expanduser()
        if not path.is_file() or not os.access(path, os.X_OK):
            raise GitHubError(
                f"MIPSTARRE_GH points to a missing or non-executable file: {path}"
            )
        return path.resolve()
    found = shutil.which("gh")
    if found:
        return Path(found).resolve()
    user_local = Path.home() / ".local" / "bin" / "gh"
    if user_local.is_file() and os.access(user_local, os.X_OK):
        return user_local.resolve()
    raise GitHubError(
        "GitHub CLI not found. Set MIPSTARRE_GH, add gh to PATH, or install it "
        f"at {user_local}. No local fallback was created."
    )


def _repository_from_url(url: str) -> str | None:
    value = url.strip()
    patterns = (
        r"^(?:ssh://)?git@github\.com[:/]([^/]+/[^/]+?)(?:\.git)?$",
        r"^https?://github\.com/([^/]+/[^/]+?)(?:\.git)?/?$",
        r"^git://github\.com/([^/]+/[^/]+?)(?:\.git)?/?$",
    )
    for pattern in patterns:
        match = re.match(pattern, value)
        if match:
            return match.group(1).removesuffix(".git")
    return None


def discover_repository(repo_root: Path | None = None) -> str:
    override = os.environ.get("MIPSTARRE_GITHUB_REPO")
    if override:
        repo = override.strip().removesuffix(".git")
    else:
        root = repo_root or Path.cwd()
        result = subprocess.run(
            ["git", "-C", str(root), "remote", "get-url", "github"],
            text=True,
            capture_output=True,
            check=False,
        )
        repo = _repository_from_url(result.stdout) or ""
    if not _REPO_RE.fullmatch(repo):
        raise GitHubError(
            "cannot discover a GitHub owner/repository. Set "
            "MIPSTARRE_GITHUB_REPO or configure the 'github' remote; the "
            f"documented repository is {DOCUMENTED_REPOSITORY}."
        )
    return repo


class GitHub:
    """Small stdlib-only wrapper around ``gh``."""

    def __init__(
        self,
        *,
        repo_root: Path | None = None,
        gh: Path | None = None,
        repo: str | None = None,
    ) -> None:
        self.repo_root = (repo_root or Path.cwd()).resolve()
        self.gh = gh or discover_gh()
        self.repo = repo or discover_repository(self.repo_root)
        self.owner, self.name = self.repo.split("/", 1)
        configured_actor = os.environ.get("MIPSTARRE_GITHUB_ACTOR")
        self.trusted_actor = normalize_actor(
            self.owner if configured_actor is None else configured_actor,
            kind="configured trusted GitHub actor",
        )
        self.retries = max(0, int(os.environ.get("MIPSTARRE_GH_RETRIES", "3")))
        self.retry_delay = max(
            0.0, float(os.environ.get("MIPSTARRE_GH_RETRY_DELAY", "1"))
        )
        self.timeout = max(1.0, float(os.environ.get("MIPSTARRE_GH_TIMEOUT", "60")))

    def run(
        self,
        arguments: Sequence[str],
        *,
        input_text: str | None = None,
        retry: bool = False,
    ) -> CommandResult:
        attempts = self.retries + 1 if retry else 1
        last: GitHubError | None = None
        for attempt in range(attempts):
            try:
                result = subprocess.run(
                    [str(self.gh), *arguments],
                    cwd=str(self.repo_root),
                    input=input_text,
                    text=True,
                    capture_output=True,
                    timeout=self.timeout,
                    check=False,
                )
            except subprocess.TimeoutExpired as exc:
                last = GitHubError(
                    f"gh command timed out after {self.timeout:g}s",
                    transient=True,
                    stdout=_safe_text(exc.stdout),
                )
            except OSError as exc:
                last = GitHubError(f"cannot execute gh: {_safe_text(str(exc))}")
            else:
                if result.returncode == 0:
                    return CommandResult(result.stdout, result.stderr)
                stderr = _safe_text(result.stderr or result.stdout)
                status = _status_from_stderr(stderr)
                last = GitHubError(
                    f"GitHub operation failed: {stderr or 'gh exited nonzero'}",
                    status=status,
                    transient=_is_transient(stderr, status),
                    stdout=_safe_text(result.stdout),
                )
            assert last is not None
            if not retry or not last.transient or attempt + 1 >= attempts:
                raise last
            time.sleep(self.retry_delay * (2**attempt))
        raise last or GitHubError("GitHub operation failed")

    def api(
        self,
        endpoint: str,
        *,
        method: str = "GET",
        data: Any | None = None,
        retry: bool | None = None,
    ) -> Any:
        arguments = [
            "api",
            "--method",
            method,
            endpoint.lstrip("/"),
            "-H",
            f"Accept: {ACCEPT}",
            "-H",
            f"X-GitHub-Api-Version: {API_VERSION}",
        ]
        input_text = None
        if data is not None:
            arguments.extend(["-H", "Content-Type: application/json", "--input", "-"])
            input_text = json.dumps(data, ensure_ascii=False)
        if retry is None:
            retry = method.upper() == "GET"
        result = self.run(arguments, input_text=input_text, retry=retry)
        if not result.stdout.strip():
            return None
        try:
            return json.loads(result.stdout)
        except json.JSONDecodeError as exc:
            raise GitHubError(
                f"gh returned invalid JSON for {method} {endpoint}: {exc}"
            ) from exc

    def paginate(self, endpoint: str, *, item_key: str | None = None) -> list[dict[str, Any]]:
        parsed = urllib.parse.urlsplit(endpoint)
        query = urllib.parse.parse_qsl(parsed.query, keep_blank_values=True)
        query = [(key, value) for key, value in query if key not in {"page", "per_page"}]
        collected: list[dict[str, Any]] = []
        for page in range(1, 101):
            page_query = urllib.parse.urlencode([*query, ("per_page", "100"), ("page", str(page))])
            page_endpoint = urllib.parse.urlunsplit(
                (parsed.scheme, parsed.netloc, parsed.path, page_query, parsed.fragment)
            )
            payload = self.api(page_endpoint)
            if item_key is not None:
                if not isinstance(payload, dict) or not isinstance(payload.get(item_key), list):
                    raise GitHubError(
                        f"paginated endpoint {endpoint} did not return list key {item_key!r}"
                    )
                items = payload[item_key]
            else:
                items = payload
            if not isinstance(items, list):
                raise GitHubError(f"paginated endpoint {endpoint} did not return a JSON list")
            if not all(isinstance(item, dict) for item in items):
                raise GitHubError(f"paginated endpoint {endpoint} returned a non-object item")
            collected.extend(items)
            if len(items) < 100:
                return collected
        raise GitHubError(f"pagination exceeded 100 pages for {endpoint}")

    @staticmethod
    def _row_actor(row: dict[str, Any], *, field: str, kind: str) -> str:
        identity = row.get(field)
        if not isinstance(identity, dict):
            raise GitHubError(f"{kind} has no authoritative {field} identity")
        return normalize_actor(identity.get("login"), kind=f"{kind} {field} login")

    def is_trusted_actor_row(
        self, row: dict[str, Any], *, field: str, kind: str
    ) -> bool:
        """Return whether a publication row names the configured principal."""
        try:
            actor = self._row_actor(row, field=field, kind=kind)
        except GitHubError:
            return False
        return actor.casefold() == self.trusted_actor.casefold()

    def require_trusted_actor_row(
        self, row: dict[str, Any], *, field: str, kind: str
    ) -> None:
        """Reject evidence whose authoritative creator is absent or untrusted."""
        actor = self._row_actor(row, field=field, kind=kind)
        if actor.casefold() != self.trusted_actor.casefold():
            raise GitHubError(
                f"{kind} was published by {actor!r}, not configured trusted "
                f"actor {self.trusted_actor!r}"
            )

    def verify_authenticated_actor(self) -> dict[str, Any]:
        """Bind the active ``gh`` credential to the configured principal."""
        payload = self.api("/user")
        if not isinstance(payload, dict):
            raise GitHubError("authenticated-user probe returned a non-object response")
        login = normalize_actor(
            payload.get("login"), kind="authenticated GitHub user login"
        )
        if login.casefold() != self.trusted_actor.casefold():
            raise GitHubError(
                f"authenticated gh user {login!r} does not match configured trusted "
                f"actor {self.trusted_actor!r}"
            )
        return payload

    def probe_authentication(self) -> dict[str, Any]:
        try:
            self.verify_authenticated_actor()
            payload = self.api(f"/repos/{self.repo}")
        except GitHubError as exc:
            raise GitHubError(
                "GitHub authentication/capability probe failed for the configured "
                f"repository {self.repo}: {exc}. Run 'gh auth login' or set the "
                "credential expected by gh; no local fallback was created.",
                status=exc.status,
                transient=exc.transient,
            ) from exc
        if not isinstance(payload, dict):
            raise GitHubError("authentication probe returned a non-object response")
        return payload

    def repository_metadata(self) -> dict[str, Any]:
        """Read current repository settings used by the merge preflight."""
        payload = self.api(f"/repos/{self.repo}")
        if not isinstance(payload, dict):
            raise GitHubError("repository settings response is not a JSON object")
        return payload

    def get_issue(self, number: int) -> dict[str, Any]:
        payload = self.api(f"/repos/{self.repo}/issues/{number}")
        if not isinstance(payload, dict):
            raise GitHubError(f"issue #{number} response is not a JSON object")
        return payload

    def get_pull(self, number: int) -> dict[str, Any]:
        payload = self.api(f"/repos/{self.repo}/pulls/{number}")
        if not isinstance(payload, dict):
            raise GitHubError(f"pull request #{number} response is not a JSON object")
        return payload

    def branch_protection(self, branch: str) -> dict[str, Any]:
        """Read classic protection for one exact base branch."""
        encoded = urllib.parse.quote(branch, safe="")
        payload = self.api(
            f"/repos/{self.repo}/branches/{encoded}/protection"
        )
        if not isinstance(payload, dict):
            raise GitHubError(
                f"classic protection for branch {branch!r} is not a JSON object"
            )
        return payload

    def branch_rules(self, branch: str) -> list[dict[str, Any]]:
        """Read the active rules GitHub says apply to one base branch."""
        encoded = urllib.parse.quote(branch, safe="")
        payload = self.api(f"/repos/{self.repo}/rules/branches/{encoded}")
        if not isinstance(payload, list) or not all(
            isinstance(row, dict) for row in payload
        ):
            raise GitHubError(
                f"effective rules for branch {branch!r} are not a JSON list"
            )
        return payload

    def ruleset(self, identifier: int) -> dict[str, Any]:
        """Read one repository ruleset referenced by an effective branch rule."""
        if type(identifier) is not int or identifier <= 0:
            raise GitHubError("ruleset id must be a positive integer")
        payload = self.api(f"/repos/{self.repo}/rulesets/{identifier}")
        if not isinstance(payload, dict):
            raise GitHubError(f"ruleset {identifier} response is not a JSON object")
        return payload

    def git_commit(self, sha: str) -> dict[str, Any]:
        """Read one exact Git commit object for merge-parent verification."""
        sha = normalize_sha(sha, kind="Git commit SHA")
        payload = self.api(f"/repos/{self.repo}/git/commits/{sha}")
        if not isinstance(payload, dict):
            raise GitHubError(f"Git commit {sha} response is not a JSON object")
        return payload

    def publication_guard(
        self, path: Path, *, authoritative: bool = True
    ) -> Callable[[], None]:
        """Build an in-process committed-comparison guard for a publication."""
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise GitHubError(f"cannot read publication guard {path}: {exc}") from exc
        expected_keys = {
            "schema",
            "pr",
            "branch",
            "base",
            "head_sha",
            "base_sha",
            "worktree",
            "pid",
            "owner",
            "locks",
        }
        if not isinstance(payload, dict) or set(payload) != expected_keys:
            raise GitHubError("publication guard has a noncanonical schema")
        number = normalize_number(payload.get("pr"), kind="publication guard PR number")
        branch = str(payload.get("branch") or "")
        base = str(payload.get("base") or "")
        head_sha = normalize_sha(payload.get("head_sha"), kind="guard head SHA")
        base_sha = normalize_sha(payload.get("base_sha"), kind="guard base SHA")
        worktree = Path(str(payload.get("worktree") or "")).resolve()
        pid = str(payload.get("pid") or "")
        owner = str(payload.get("owner") or "")
        raw_locks = payload.get("locks")
        if (
            payload.get("schema") != 1
            or not branch
            or not base
            or not worktree.is_dir()
            or not isinstance(raw_locks, list)
            or len(raw_locks) not in {0, 2}
        ):
            raise GitHubError("publication guard contains invalid values")
        locks = tuple(Path(str(item)).resolve() for item in raw_locks)
        if locks and (not pid.isdigit() or not owner or len(set(locks)) != 2):
            raise GitHubError("publication guard contains invalid lease values")

        def assert_leases() -> None:
            for lock in locks:
                try:
                    lock_pid = (lock / "pid").read_text(encoding="utf-8").strip()
                    lock_owner = (lock / "owner").read_text(encoding="utf-8").strip()
                except OSError as exc:
                    raise GitHubError(f"publication lease is unreadable: {lock}") from exc
                if lock_pid != pid or lock_owner != owner or (lock / "cancel").exists():
                    raise GitHubError(
                        f"publication lease was lost or cancelled: {lock}"
                    )

        def git_output(*arguments: str) -> str:
            result = subprocess.run(
                ["git", "-C", str(worktree), *arguments],
                text=True,
                capture_output=True,
                check=False,
            )
            if result.returncode:
                raise GitHubError(
                    "cannot validate the worktree immediately before publication"
                )
            return result.stdout.strip()

        def guard() -> None:
            assert_leases()
            pull = self.get_pull(number) if authoritative else None
            local_branch = git_output("symbolic-ref", "--quiet", "--short", "HEAD")
            local_head = git_output("rev-parse", "HEAD")
            local_base = git_output(
                "rev-parse", f"refs/remotes/github/{base}^{{commit}}"
            )
            dirty = git_output("status", "--porcelain=v1", "--untracked-files=all")
            assert_leases()
            if (
                (
                    pull is not None
                    and (
                        str(pull.get("state") or "") != "open"
                        or str((pull.get("head") or {}).get("ref") or "") != branch
                        or str((pull.get("base") or {}).get("ref") or "") != base
                        or str((pull.get("head") or {}).get("sha") or "").lower()
                        != head_sha
                        or str((pull.get("base") or {}).get("sha") or "").lower()
                        != base_sha
                    )
                )
                or local_branch != branch
                or local_head != head_sha
                or local_base != base_sha
                or dirty
            ):
                raise GitHubError(
                    "comparison or worktree changed immediately before publication"
                )

        return guard

    def labels(self) -> list[dict[str, Any]]:
        return self.paginate(f"/repos/{self.repo}/labels")

    def validate_labels(self, requested: Iterable[str]) -> list[str]:
        labels = list(dict.fromkeys(name.strip() for name in requested if name.strip()))
        if not labels:
            return []
        existing = {str(item.get("name")) for item in self.labels()}
        missing = [name for name in labels if name not in existing]
        if missing:
            raise GitHubError(
                "GitHub label(s) do not exist in "
                f"{self.repo}: {', '.join(missing)}. Repository labels are authoritative."
            )
        return labels

    def remove_label(self, number: int, label: str) -> None:
        encoded = urllib.parse.quote(label, safe="")

        def present() -> bool:
            issue = self.get_issue(number)
            names = {
                str(item.get("name") if isinstance(item, dict) else item)
                for item in (issue.get("labels") or [])
            }
            return label in names

        if not present():
            return
        last: GitHubError | None = None
        for attempt in range(self.retries + 1):
            try:
                self.api(
                    f"/repos/{self.repo}/issues/{number}/labels/{encoded}",
                    method="DELETE",
                    retry=False,
                )
                if not present():
                    return
                last = GitHubError(
                    f"GitHub reported success but retained label {label!r} on #{number}",
                    transient=True,
                )
            except GitHubError as exc:
                last = exc
                if not present():
                    return
                if not exc.transient or attempt >= self.retries:
                    raise
            if attempt >= self.retries:
                break
            time.sleep(self.retry_delay * (2**attempt))
        raise last or GitHubError("label removal failed")

    def comments(self, number: int) -> list[dict[str, Any]]:
        return self.paginate(f"/repos/{self.repo}/issues/{number}/comments")

    def reviews(self, number: int) -> list[dict[str, Any]]:
        return self.paginate(f"/repos/{self.repo}/pulls/{number}/reviews")

    def pull_commits(self, number: int) -> list[dict[str, Any]]:
        pull = self.get_pull(number)
        expected = pull.get("commits")
        if not isinstance(expected, int) or expected < 0:
            raise GitHubError(
                f"PR #{number} does not report a trustworthy commit count"
            )
        if expected > 250:
            raise GitHubError(
                f"PR #{number} reports {expected} commits, beyond GitHub's "
                "250-commit PR endpoint cap; complete fix history cannot be proven"
            )
        rows = self.paginate(f"/repos/{self.repo}/pulls/{number}/commits")
        if len(rows) != expected:
            raise GitHubError(
                f"PR #{number} reports {expected} commits but the endpoint returned "
                f"{len(rows)}; refusing incomplete history"
            )
        return rows

    def statuses(self, sha: str) -> list[dict[str, Any]]:
        sha = normalize_sha(sha)
        return self.paginate(f"/repos/{self.repo}/commits/{sha}/statuses")

    def latest_statuses(self, sha: str) -> dict[str, dict[str, Any]]:
        sha = normalize_sha(sha)
        result: dict[str, dict[str, Any]] = {}
        rows = self.statuses(sha)
        rows.sort(
            key=lambda row: (
                str(row.get("created_at") or ""),
                int(row.get("id") or 0),
            ),
            reverse=True,
        )
        for row in rows:
            row_sha = str(row.get("sha") or "")
            if not _SHA_RE.fullmatch(row_sha) or row_sha.lower() != sha:
                continue
            context = str(row.get("context") or "").casefold()
            if context and context not in result:
                result[context] = row
        return result

    @staticmethod
    def _latest(rows: Iterable[dict[str, Any]], timestamp: str) -> dict[str, Any]:
        candidates = list(rows)
        if not candidates:
            raise GitHubError("no matching authoritative publication was found")

        def order(row: dict[str, Any]) -> tuple[datetime, int]:
            identifier = row.get("id")
            if type(identifier) is not int or identifier <= 0:
                raise GitHubError("authoritative publication has an invalid numeric id")
            submitted = row.get(timestamp) or row.get("created_at")
            return _parse_timestamp(submitted, field=timestamp), identifier

        candidates.sort(
            key=order,
            reverse=True,
        )
        return candidates[0]

    def ci_evidence(
        self, number: int, sha: str, base_sha: str | None = None
    ) -> CIManifestEvidence:
        """Parse a complete manifest and bind every status to its exact run."""
        self.verify_authenticated_actor()
        number = normalize_number(number, kind="PR number")
        sha = normalize_sha(sha)
        expected_base = normalize_sha(base_sha, kind="pull-request base SHA") if base_sha else None
        matches: list[dict[str, Any]] = []
        for row in self.comments(number):
            body = str(row.get("body") or "")
            markers = _CI_MARKER_RE.findall(body)
            if not any(int(pr) == number and head.lower() == sha for pr, head, _ in markers):
                continue
            if not self.is_trusted_actor_row(
                row, field="user", kind="CI manifest comment"
            ):
                continue
            matches.append(row)
        row = self._latest(matches, "created_at")
        body = str(row.get("body") or "")
        if body.count("<!-- mipstarre:ci-manifest ") != 1:
            raise GitHubError("latest exact-head CI manifest has ambiguous markers")
        marker_match = _CI_MARKER_RE.search(body)
        if marker_match is None:
            raise GitHubError("latest exact-head CI manifest has a malformed marker")
        marker = marker_match.group(0)
        if body[marker_match.start() :] not in {marker, marker + "\n"}:
            raise GitHubError("latest exact-head CI manifest marker is not the final line")
        marker_run = marker_match.group(3)
        if not _RUN_ID_RE.fullmatch(marker_run):
            raise GitHubError("latest CI manifest has an invalid run id")
        fenced = re.search(r"```json\s*\n(.*?)\n```", body, re.DOTALL)
        if not fenced or body.count("```json") != 1:
            raise GitHubError("latest exact-head CI comment has no JSON manifest fence")
        try:
            manifest = json.loads(fenced.group(1))
        except json.JSONDecodeError as exc:
            raise GitHubError(f"latest exact-head CI manifest is invalid JSON: {exc}") from exc
        if not isinstance(manifest, dict):
            raise GitHubError("latest exact-head CI manifest is not an object")
        manifest_head = normalize_sha(
            str(manifest.get("head_sha") or ""), kind="CI manifest head SHA"
        )
        manifest_base = normalize_sha(
            str(manifest.get("base_sha") or ""), kind="CI manifest base SHA"
        )
        if manifest_head != sha:
            raise GitHubError("latest CI manifest does not record the exact requested head")
        if expected_base is not None and manifest_base != expected_base:
            raise GitHubError("latest CI manifest does not record the exact requested base")
        if (
            not _same_number(manifest.get("pr"), number)
            or manifest.get("partial") is not False
            or manifest.get("run_id") != marker_run
        ):
            raise GitHubError("latest CI manifest has the wrong PR or is partial")
        if str(manifest.get("conclusion") or "") not in {"success", "failure", "error"}:
            raise GitHubError("latest CI manifest has an invalid conclusion")
        steps = manifest.get("steps")
        if not isinstance(steps, list):
            raise GitHubError("latest CI manifest has no step list")
        if len(steps) != len(CANONICAL_CI_STEPS) or not all(
            isinstance(step, dict) for step in steps
        ):
            raise GitHubError("latest CI manifest must contain exactly eight step objects")
        names = [str(step.get("step") or "") for step in steps]
        if len(set(names)) != len(names) or set(names) != set(CANONICAL_CI_STEPS):
            raise GitHubError("latest CI manifest does not contain exactly the canonical steps")
        statuses = self.latest_statuses(sha)
        for step in steps:
            step_name = str(step.get("step") or "")
            state, description = ci_status_description(marker_run, step)
            context = f"local-ci/{step_name}"
            status = statuses.get(context.casefold()) or {}
            self.require_trusted_actor_row(
                status, field="creator", kind=f"{context} status"
            )
            expected_description = render_status_description(
                sha, context, state, description
            )
            if (
                str(status.get("state") or "").casefold() != state
                or str(status.get("description") or "") != expected_description
            ):
                raise GitHubError(
                    f"{context} is not bound to CI run {marker_run} and its manifest"
                )
        return CIManifestEvidence(
            number=number,
            head_sha=sha,
            base_sha=manifest_base,
            run_id=marker_run,
            digest=ci_manifest_digest(manifest),
            row=row,
            manifest=manifest,
            statuses=statuses,
        )

    def ci_success_evidence(
        self, number: int, sha: str, base_sha: str
    ) -> CIManifestEvidence:
        """Return a complete exact-comparison CI run that satisfies the gate."""
        evidence = self.ci_evidence(number, sha, base_sha)
        manifest = evidence.manifest
        if str(manifest.get("conclusion") or "") != "success":
            raise GitHubError("exact-run CI manifest conclusion is not success")
        failures = [
            f"{step.get('step')}={step.get('outcome')}"
            for step in manifest.get("steps") or []
            if str(step.get("outcome") or "") not in {"success", "skipped"}
        ]
        if failures:
            raise GitHubError(
                "exact-run CI manifest has non-success canonical steps: "
                + ", ".join(failures)
            )
        statuses = self.latest_statuses(evidence.head_sha)
        summary = statuses.get(CI_SUMMARY_CONTEXT.casefold()) or {}
        self.require_trusted_actor_row(
            summary, field="creator", kind=f"{CI_SUMMARY_CONTEXT} status"
        )
        expected_description = render_status_description(
            evidence.head_sha,
            CI_SUMMARY_CONTEXT,
            "success",
            ci_summary_description(evidence),
        )
        if (
            str(summary.get("state") or "").casefold() != "success"
            or str(summary.get("description") or "") != expected_description
        ):
            raise GitHubError(
                f"{CI_SUMMARY_CONTEXT} does not match CI run "
                f"{evidence.run_id} and digest {evidence.digest}"
            )
        return evidence

    def finalize_ci_status(
        self,
        number: int,
        sha: str,
        base_sha: str,
        run_id: str,
        *,
        before_mutation: Callable[[], None] | None = None,
        before_write: Callable[[], None] | None = None,
    ) -> CIManifestEvidence:
        """Publish a summary only after authoritative manifest read-back."""
        if not _RUN_ID_RE.fullmatch(run_id):
            raise GitHubError("CI finalization run id is invalid")
        evidence = self.ci_evidence(number, sha, base_sha)
        if evidence.run_id != run_id:
            raise GitHubError("CI finalization run does not match the latest manifest")
        state = ci_summary_state(evidence)

        def assert_finalizable() -> None:
            if before_mutation is not None:
                before_mutation()
            current = self.ci_evidence(number, sha, base_sha)
            if current.run_id != run_id or current.digest != evidence.digest:
                raise GitHubError("CI manifest changed before summary publication")
            if before_mutation is not None:
                before_mutation()
            if before_write is not None:
                before_write()

        self.post_status(
            evidence.head_sha,
            CI_SUMMARY_CONTEXT,
            state,
            ci_summary_description(evidence),
            before_mutation=assert_finalizable,
        )
        current = self.ci_evidence(number, sha, base_sha)
        summary = self.latest_statuses(sha).get(CI_SUMMARY_CONTEXT.casefold()) or {}
        self.require_trusted_actor_row(
            summary, field="creator", kind=f"{CI_SUMMARY_CONTEXT} status"
        )
        expected = render_status_description(
            sha,
            CI_SUMMARY_CONTEXT,
            state,
            ci_summary_description(current),
        )
        if (
            current.run_id != run_id
            or current.digest != evidence.digest
            or str(summary.get("state") or "").casefold() != state
            or str(summary.get("description") or "") != expected
        ):
            raise GitHubError("CI summary failed authoritative final read-back")
        return current

    def ci_manifest(
        self, number: int, sha: str, base_sha: str | None = None
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        """Return readable exact-head CI evidence, including failed/error runs."""
        evidence = self.ci_evidence(number, sha, base_sha)
        return evidence.row, evidence.manifest

    def _review_attestations(self, number: int) -> list[ReviewAttestation]:
        self.verify_authenticated_actor()
        attestations: list[ReviewAttestation] = []
        for row in self.reviews(number):
            body = str(row.get("body") or "")
            if "mipstarre:review-attestation" not in body:
                continue
            if not self.is_trusted_actor_row(
                row, field="user", kind="review COMMENT row"
            ):
                continue
            attestations.append(_review_attestation_from_row(row, number))
        session_owners: dict[str, tuple[str, str, str, str]] = {}
        thread_owners: dict[str, tuple[str, str, str, str]] = {}
        run_owners: dict[str, tuple[str, str, str, str]] = {}
        for attestation in attestations:
            identity = (
                attestation.head_sha,
                attestation.base_sha,
                attestation.run_id,
                attestation.digest,
            )
            prior = run_owners.setdefault(attestation.run_id, identity)
            if prior != identity:
                raise GitHubError(
                    f"review run {attestation.run_id!r} is replayed across "
                    "distinct review attestations"
                )
            for lane in attestation.lanes:
                prior = session_owners.setdefault(lane.name, identity)
                if prior != identity:
                    raise GitHubError(
                        f"reviewer session {lane.name!r} is replayed across "
                        "distinct review attestations"
                    )
                prior = thread_owners.setdefault(lane.thread_id, identity)
                if prior != identity:
                    raise GitHubError(
                        f"reviewer thread {lane.thread_id!r} is replayed across "
                        "distinct review attestations"
                    )
        return attestations

    def _validate_attestation_sessions(
        self, attestation: ReviewAttestation
    ) -> None:
        records = _read_session_records(
            self.repo_root / "results" / "telemetry" / "sessions.jsonl"
        )
        worktree = attestation.lanes[0].worktree
        for lane in attestation.lanes:
            _validate_session_record(
                lane,
                records=records,
                number=attestation.number,
                worktree=worktree,
            )

    def _complete_review_evidence(
        self, attestation: ReviewAttestation
    ) -> ReviewEvidence:
        self._validate_attestation_sessions(attestation)
        statuses = self.latest_statuses(attestation.head_sha)
        status = statuses.get(REVIEW_CONTEXT.casefold()) or {}
        self.require_trusted_actor_row(
            status, field="creator", kind=f"{REVIEW_CONTEXT} status"
        )
        state = review_summary_state(attestation)
        expected_description = render_status_description(
            attestation.head_sha,
            REVIEW_CONTEXT,
            state,
            review_status_description(attestation),
        )
        if (
            str(status.get("state") or "").casefold() != state
            or str(status.get("description") or "") != expected_description
        ):
            raise GitHubError(
                f"{REVIEW_CONTEXT} does not match review run "
                f"{attestation.run_id} and digest {attestation.digest}"
            )
        return ReviewEvidence(attestation=attestation, status=status)

    def latest_review_attestation(self, number: int) -> ReviewAttestation | None:
        attestations = self._review_attestations(number)
        if not attestations:
            return None
        rows = [attestation.row for attestation in attestations]
        latest = self._latest(rows, "submitted_at")
        selected = next(item for item in attestations if item.row is latest)
        self._validate_attestation_sessions(selected)
        return selected

    def review_attestations(self, number: int) -> list[ReviewAttestation]:
        """Return every structurally and session-valid attestation for a PR."""
        attestations = self._review_attestations(number)
        for attestation in attestations:
            self._validate_attestation_sessions(attestation)
        return attestations

    def review_attestation(
        self, number: int, sha: str, base_sha: str | None = None
    ) -> ReviewAttestation:
        sha = normalize_sha(sha)
        expected_base = normalize_sha(base_sha, kind="pull-request base SHA") if base_sha else None
        matches = [
            item
            for item in self._review_attestations(number)
            if item.head_sha == sha
            and (expected_base is None or item.base_sha == expected_base)
        ]
        selected_row = self._latest(
            [attestation.row for attestation in matches], "submitted_at"
        )
        selected = next(item for item in matches if item.row is selected_row)
        self._validate_attestation_sessions(selected)
        return selected

    def review_publication_state(
        self, number: int, sha: str, base_sha: str
    ) -> dict[str, Any]:
        """Classify exact-attestation summary evidence for rerun recovery."""
        sha = normalize_sha(sha)
        base_sha = normalize_sha(base_sha, kind="pull-request base SHA")
        matches = [
            item
            for item in self._review_attestations(number)
            if item.head_sha == sha and item.base_sha == base_sha
        ]
        if not matches:
            return {"state": "absent"}
        selected_row = self._latest(
            [attestation.row for attestation in matches], "submitted_at"
        )
        attestation = next(item for item in matches if item.row is selected_row)
        self._validate_attestation_sessions(attestation)
        status = self.latest_statuses(sha).get(REVIEW_CONTEXT.casefold())
        if status is not None:
            self.require_trusted_actor_row(
                status, field="creator", kind=f"{REVIEW_CONTEXT} status"
            )
        final_state = review_summary_state(attestation)
        expected_final = render_status_description(
            sha,
            REVIEW_CONTEXT,
            final_state,
            review_status_description(attestation),
        )
        if status is not None and (
            str(status.get("state") or "").casefold() == final_state
            and str(status.get("description") or "") == expected_final
        ):
            return {
                "state": "complete",
                "summary_state": final_state,
                "attestation": attestation.as_dict(),
            }
        expected_pending = render_status_description(
            sha,
            REVIEW_CONTEXT,
            "pending",
            review_pending_description(attestation.run_id),
        )
        if status is None or (
            str(status.get("state") or "").casefold() == "pending"
            and str(status.get("description") or "") == expected_pending
        ):
            return {
                "state": "recoverable",
                "summary_state": final_state,
                "attestation": attestation.as_dict(),
            }
        raise GitHubError(
            "latest review summary belongs to a different run or does not "
            "match the exact review attestation"
        )

    def finalize_review_status(
        self,
        number: int,
        sha: str,
        base_sha: str,
        run_id: str,
        digest: str,
        *,
        before_mutation: Callable[[], None] | None = None,
        before_write: Callable[[], None] | None = None,
    ) -> ReviewEvidence:
        """Revalidate one exact attestation and idempotently finalize its status."""
        if not _RUN_ID_RE.fullmatch(run_id):
            raise GitHubError("review finalization run id is invalid")
        if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise GitHubError("review finalization digest is invalid")
        publication = self.review_publication_state(number, sha, base_sha)
        if publication.get("state") == "absent":
            raise GitHubError("cannot finalize a missing exact review attestation")
        attestation = self.review_attestation(number, sha, base_sha)
        if attestation.run_id != run_id or attestation.digest != digest:
            raise GitHubError(
                "review finalization identity does not match the latest exact attestation"
            )
        if publication.get("state") == "complete":
            return self._complete_review_evidence(attestation)
        if publication.get("state") != "recoverable":
            raise GitHubError("review publication is not finalizable")
        state = review_summary_state(attestation)

        def assert_finalizable() -> None:
            if before_mutation is not None:
                before_mutation()
            current = self.review_publication_state(number, sha, base_sha)
            current_attestation = current.get("attestation") or {}
            if (
                current.get("state") != "recoverable"
                or current_attestation.get("run_id") != run_id
                or current_attestation.get("digest") != digest
            ):
                raise GitHubError(
                    "review summary changed before final status publication"
                )
            if before_mutation is not None:
                before_mutation()
            if before_write is not None:
                before_write()

        self.post_status(
            attestation.head_sha,
            REVIEW_CONTEXT,
            state,
            review_status_description(attestation),
            before_mutation=assert_finalizable,
        )
        return self.review_evidence(number, sha, base_sha)

    def latest_review_evidence(self, number: int) -> ReviewEvidence | None:
        selected = self.latest_review_attestation(number)
        return self._complete_review_evidence(selected) if selected else None

    def review_evidence(
        self, number: int, sha: str, base_sha: str | None = None
    ) -> ReviewEvidence:
        selected = self.review_attestation(number, sha, base_sha)
        return self._complete_review_evidence(selected)

    def latest_review_ledger(self, number: int) -> dict[str, Any] | None:
        attestation = self.latest_review_attestation(number)
        return attestation.row if attestation else None

    def review_ledger(
        self, number: int, sha: str, base_sha: str | None = None
    ) -> dict[str, Any]:
        return self.review_attestation(number, sha, base_sha).row

    def post_status(
        self,
        sha: str,
        context: str,
        state: str,
        description: str,
        *,
        before_mutation: Callable[[], None] | None = None,
    ) -> dict[str, Any]:
        self.verify_authenticated_actor()
        sha = normalize_sha(sha)
        context = context.strip()
        if not context or any(ord(ch) < 32 for ch in context):
            raise GitHubError("commit status context must be nonempty and printable")
        if state not in {"pending", "success", "failure", "error"}:
            raise GitHubError(f"invalid commit status state {state!r}")
        rendered_description = render_status_description(
            sha, context, state, description
        )

        def matches(row: dict[str, Any]) -> bool:
            row_sha = str(row.get("sha") or "")
            return (
                _SHA_RE.fullmatch(row_sha) is not None
                and row_sha.lower() == sha
                and str(row.get("context") or "").casefold() == context.casefold()
                and str(row.get("state") or "").casefold() == state
                and str(row.get("description") or "") == rendered_description
                and self.is_trusted_actor_row(
                    row, field="creator", kind="commit status"
                )
            )

        def lookup() -> dict[str, Any] | None:
            row = self.latest_statuses(sha).get(context.casefold())
            return row if row is not None and matches(row) else None

        def mutate() -> dict[str, Any]:
            if before_mutation is not None:
                before_mutation()
            payload = self.api(
                f"/repos/{self.repo}/statuses/{sha}",
                method="POST",
                data={
                    "state": state,
                    "context": context,
                    "description": rendered_description,
                },
                retry=False,
            )
            if not isinstance(payload, dict):
                raise GitHubError("commit status creation returned a non-object response")
            return payload

        row = self._idempotent_mutation(lookup=lookup, mutate=mutate)
        if not matches(row):
            raise GitHubError(
                "commit status response does not match its exact SHA, context, "
                "state, and digest"
            )
        return row

    def _idempotent_mutation(
        self,
        *,
        lookup: Callable[[], T | None],
        mutate: Callable[[], T],
    ) -> T:
        found = lookup()
        if found is not None:
            return found
        try:
            return mutate()
        except GitHubError as exc:
            if not exc.transient:
                raise
            for attempt in range(self.retries + 1):
                found = lookup()
                if found is not None:
                    return found
                if attempt < self.retries:
                    time.sleep(self.retry_delay * (2**attempt))
            raise GitHubError(
                "mutation outcome is ambiguous after authoritative read-back; "
                "refusing to issue a second mutation",
                status=exc.status,
                transient=True,
                stdout=exc.stdout,
            ) from exc

    def comment_once(
        self,
        number: int,
        body: str,
        marker: str,
        *,
        before_mutation: Callable[[], None] | None = None,
    ) -> dict[str, Any]:
        self.verify_authenticated_actor()
        _validated_marker(marker, body)

        def lookup() -> dict[str, Any] | None:
            for row in self.comments(number):
                adopted_body = str(row.get("body") or "")
                if marker not in adopted_body:
                    continue
                if not self.is_trusted_actor_row(
                    row, field="user", kind="issue comment"
                ):
                    continue
                if adopted_body != body:
                    raise GitHubError(
                        "comment marker collision: authoritative body differs from "
                        "the requested publication"
                    )
                return row
            return None

        def mutate() -> dict[str, Any]:
            if before_mutation is not None:
                before_mutation()
            payload = self.api(
                f"/repos/{self.repo}/issues/{number}/comments",
                method="POST",
                data={"body": body},
                retry=False,
            )
            if not isinstance(payload, dict):
                raise GitHubError("comment creation returned a non-object response")
            return payload

        row = self._idempotent_mutation(lookup=lookup, mutate=mutate)
        self.require_trusted_actor_row(row, field="user", kind="issue comment")
        if str(row.get("body") or "") != body:
            raise GitHubError("comment publication returned a different authoritative body")
        return row

    def review_once(
        self,
        number: int,
        commit_id: str,
        body: str,
        event: str,
        marker: str,
        *,
        before_mutation: Callable[[], None] | None = None,
        before_write: Callable[[], None] | None = None,
    ) -> tuple[dict[str, Any], str]:
        self.verify_authenticated_actor()
        number = normalize_number(number, kind="PR number")
        commit_id = normalize_sha(commit_id, kind="review commit SHA")
        _validated_marker(marker, body)
        if event != "COMMENT":
            raise GitHubError("local review publication permits only COMMENT")
        requested = _review_attestation_from_row(
            {
                "body": body,
                "commit_id": commit_id,
                "state": "COMMENTED",
            },
            number,
        )
        marker_match = _REVIEW_MARKER_RE.search(body)
        if marker_match is None or marker_match.group(0) != marker:
            raise GitHubError("review marker does not match the canonical attestation")
        if requested.event != "COMMENT" or requested.fallback != "none":
            raise GitHubError("review event and fallback do not match the attestation")

        requested_identity = (
            requested.head_sha,
            requested.base_sha,
            requested.run_id,
            requested.digest,
        )
        def assert_identity_available() -> None:
            for existing in self._review_attestations(number):
                existing_identity = (
                    existing.head_sha,
                    existing.base_sha,
                    existing.run_id,
                    existing.digest,
                )
                if existing_identity == requested_identity:
                    continue
                if existing.run_id == requested.run_id:
                    raise GitHubError(
                        "review run id is already bound to a distinct attestation"
                    )
                existing_names = {lane.name for lane in existing.lanes}
                existing_threads = {lane.thread_id for lane in existing.lanes}
                if any(lane.name in existing_names for lane in requested.lanes):
                    raise GitHubError(
                        "reviewer session name is already bound to a distinct "
                        "attestation"
                    )
                if any(lane.thread_id in existing_threads for lane in requested.lanes):
                    raise GitHubError(
                        "reviewer thread id is already bound to a distinct attestation"
                    )

        assert_identity_available()

        def lookup() -> dict[str, Any] | None:
            for row in self.reviews(number):
                adopted_body = str(row.get("body") or "")
                if marker not in adopted_body:
                    continue
                if not self.is_trusted_actor_row(
                    row, field="user", kind="review COMMENT row"
                ):
                    continue
                if str(row.get("commit_id") or "").lower() != commit_id:
                    raise GitHubError(
                        "review marker collision: authoritative review is bound to "
                        "a different commit"
                    )
                if adopted_body != body:
                    raise GitHubError(
                        "review marker collision: authoritative body differs from "
                        "the requested ledger"
                    )
                _review_attestation_from_row(row, number)
                return row
            return None

        def mutate() -> dict[str, Any]:
            endpoint = f"/repos/{self.repo}/pulls/{number}/reviews"
            if before_mutation is not None:
                before_mutation()
            assert_identity_available()
            if before_mutation is not None:
                before_mutation()
            if before_write is not None:
                before_write()
            payload = self.api(
                endpoint,
                method="POST",
                data={"body": body, "event": "COMMENT", "commit_id": commit_id},
                retry=False,
            )
            if not isinstance(payload, dict):
                raise GitHubError("review creation returned a non-object response")
            return payload

        row = self._idempotent_mutation(lookup=lookup, mutate=mutate)
        self.require_trusted_actor_row(
            row, field="user", kind="review COMMENT row"
        )
        if str(row.get("commit_id") or "").lower() != commit_id:
            raise GitHubError("review publication returned a different commit binding")
        if str(row.get("body") or "") != body:
            raise GitHubError("review publication returned a different authoritative body")
        adopted_state = str(row.get("state") or "").upper()
        if adopted_state != "COMMENTED":
            raise GitHubError(
                f"review publication returned unexpected state {adopted_state or 'missing'}"
            )
        published = _review_attestation_from_row(row, number)
        if published.event != "COMMENT" or published.fallback != "none":
            raise GitHubError("published review does not retain its attested semantics")
        return row, "COMMENT"


def pull_identity(pull: dict[str, Any]) -> PullIdentity:
    try:
        branch = str(pull["head"]["ref"])
        head_sha = str(pull["head"]["sha"])
        base = str(pull["base"]["ref"])
        base_sha = str(pull["base"]["sha"])
    except (KeyError, TypeError) as exc:
        raise GitHubError("pull request response lacks full base/head refs and SHAs") from exc
    if not branch or not base:
        raise GitHubError("pull request response contains invalid base/head data")
    return PullIdentity(
        branch=branch,
        base=base,
        head_sha=normalize_sha(head_sha, kind="pull-request head SHA"),
        base_sha=normalize_sha(base_sha, kind="pull-request base SHA"),
    )


def pull_head(pull: dict[str, Any]) -> tuple[str, str, str]:
    identity = pull_identity(pull)
    return identity.branch, identity.base, identity.head_sha


def fix_iteration_count(commits: Sequence[dict[str, Any]]) -> int:
    count = 0
    for row in commits:
        message = str((row.get("commit") or {}).get("message") or "")
        subject = message.splitlines()[0] if message else ""
        if subject.startswith(AUTO_FIX_PREFIXES):
            count += 1
    return count


def require_ci_success(
    client: GitHub, number: int, sha: str, base_sha: str
) -> CIManifestEvidence:
    """Require the complete manifest and digest-bound CI summary contract."""
    return client.ci_success_evidence(number, sha, base_sha)


def _atomic_write(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temp_name = tempfile.mkstemp(dir=path.parent, prefix=path.name + ".", suffix=".tmp")
    try:
        with os.fdopen(handle, "w", encoding="utf-8") as stream:
            json.dump(payload, stream, indent=2, ensure_ascii=False, sort_keys=True)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp_name, path)
    except BaseException:
        try:
            os.unlink(temp_name)
        except OSError:
            pass
        raise


def write_snapshot(client: GitHub, destination: Path) -> dict[str, Any]:
    issues = [
        row
        for row in client.paginate(f"/repos/{client.repo}/issues?state=open")
        if "pull_request" not in row
    ]
    pulls = client.paginate(f"/repos/{client.repo}/pulls?state=open")
    generated = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    generation = stable_digest({"generated": generated, "issues": issues, "pulls": pulls})
    metadata = {
        "schema": 1,
        "generation": generation,
        "repository": client.repo,
        "generated": generated,
        "authority": "GitHub",
        "lifecycle_input": False,
        "open_issue_count": len(issues),
        "open_pull_count": len(pulls),
    }
    parent = destination.parent
    parent.mkdir(parents=True, exist_ok=True)
    generations = parent / f".{destination.name}-generations"
    generations.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(dir=generations, prefix=".snapshot-"))
    final = generations / (
        f"snapshot-{generated.replace(':', '')}-{generation}-{os.getpid()}-{time.time_ns()}"
    )
    fail_after = os.environ.get("MIPSTARRE_SNAPSHOT_FAIL_AFTER", "")

    def inject(point: str) -> None:
        if fail_after == point:
            raise GitHubError(f"injected snapshot failure after {point}")

    link_tmp = parent / f".{destination.name}.link-{os.getpid()}-{generation}"
    try:
        _atomic_write(stage / "open-issues.json", issues)
        inject("issues")
        _atomic_write(stage / "open-pulls.json", pulls)
        inject("pulls")
        _atomic_write(stage / "metadata.json", metadata)
        inject("metadata")
        os.replace(stage, final)
        inject("generation")

        if destination.exists() and not destination.is_symlink():
            raise GitHubError(
                f"snapshot destination {destination} is a real directory; refusing "
                "a non-atomic in-place migration. Move it aside once, then retry."
            )
        relative = os.path.relpath(final, parent)
        os.symlink(relative, link_tmp)
        os.replace(link_tmp, destination)
        directory_fd = os.open(parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except BaseException:
        if link_tmp.is_symlink():
            link_tmp.unlink()
        if stage.exists():
            shutil.rmtree(stage)
        raise
    return metadata


def _read_body(path: str) -> str:
    return Path(path).read_text(encoding="utf-8")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--no-probe", action="store_true", help=argparse.SUPPRESS)
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("probe")
    sub.add_parser("repo")

    pull = sub.add_parser("pull")
    pull.add_argument("number")

    target = sub.add_parser("target")
    target.add_argument("number")

    status_list = sub.add_parser("statuses")
    status_list.add_argument("sha")

    require_ci = sub.add_parser("require-ci")
    require_ci.add_argument("number")
    require_ci.add_argument("sha")
    require_ci.add_argument("base_sha")

    post_status = sub.add_parser("post-status")
    post_status.add_argument("sha")
    post_status.add_argument("context")
    post_status.add_argument("state", choices=("pending", "success", "failure", "error"))
    post_status.add_argument("description")
    post_status.add_argument("--guard-file", type=Path)

    comment = sub.add_parser("comment-once")
    comment.add_argument("number")
    comment.add_argument("body_file")
    comment.add_argument("marker")
    comment.add_argument("--guard-file", type=Path)

    review = sub.add_parser("review-once")
    review.add_argument("number")
    review.add_argument("commit_id")
    review.add_argument("body_file")
    review.add_argument("event", choices=("COMMENT",))
    review.add_argument("marker")
    review.add_argument("--guard-file", type=Path)

    comments = sub.add_parser("comments")
    comments.add_argument("number")
    reviews = sub.add_parser("reviews")
    reviews.add_argument("number")
    commits = sub.add_parser("commits")
    commits.add_argument("number")

    fix_count = sub.add_parser("fix-count")
    fix_count.add_argument("number")

    ci_manifest = sub.add_parser("ci-manifest")
    ci_manifest.add_argument("number")
    ci_manifest.add_argument("sha")
    ci_manifest.add_argument("base_sha", nargs="?")

    ci_evidence = sub.add_parser("ci-evidence")
    ci_evidence.add_argument("number")
    ci_evidence.add_argument("sha")
    ci_evidence.add_argument("base_sha")

    ci_finalize = sub.add_parser("ci-finalize")
    ci_finalize.add_argument("number")
    ci_finalize.add_argument("sha")
    ci_finalize.add_argument("base_sha")
    ci_finalize.add_argument("run_id")
    ci_finalize.add_argument("--guard-file", type=Path)

    review_ledger = sub.add_parser("review-ledger")
    review_ledger.add_argument("number")
    review_ledger.add_argument("sha")
    review_ledger.add_argument("base_sha", nargs="?")

    review_attestation = sub.add_parser("review-attestation")
    review_attestation.add_argument("number")
    review_attestation.add_argument("sha")
    review_attestation.add_argument("base_sha")

    review_state = sub.add_parser("review-state")
    review_state.add_argument("number")
    review_state.add_argument("sha")
    review_state.add_argument("base_sha")

    review_finalize = sub.add_parser("review-finalize")
    review_finalize.add_argument("number")
    review_finalize.add_argument("sha")
    review_finalize.add_argument("base_sha")
    review_finalize.add_argument("run_id")
    review_finalize.add_argument("digest")
    review_finalize.add_argument("--guard-file", type=Path)

    review_evidence = sub.add_parser("review-evidence")
    review_evidence.add_argument("number")
    review_evidence.add_argument("sha")
    review_evidence.add_argument("base_sha")

    review_session = sub.add_parser("review-session")
    review_session.add_argument("dispatch_log", type=Path)
    review_session.add_argument("telemetry", type=Path)
    review_session.add_argument("lane", choices=("code", "prose"))
    review_session.add_argument("number")
    review_session.add_argument("worktree", type=Path)
    review_session.add_argument("expected_exit", type=int)

    latest_review_ledger = sub.add_parser("latest-review-ledger")
    latest_review_ledger.add_argument("number")

    remove_label = sub.add_parser("remove-label")
    remove_label.add_argument("number")
    remove_label.add_argument("label")

    snapshot = sub.add_parser("snapshot")
    snapshot.add_argument("destination", type=Path)
    return parser


def cli(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    client = GitHub(repo_root=args.repo_root)
    if args.no_probe:
        client.verify_authenticated_actor()
    else:
        client.probe_authentication()
    if args.command == "probe":
        print(
            f"authenticated actor: {client.trusted_actor}; "
            f"repository: {client.repo}"
        )
    elif args.command == "repo":
        print(client.repo)
    elif args.command == "pull":
        print(json.dumps(client.get_pull(normalize_number(args.number, kind="PR number"))))
    elif args.command == "target":
        number = normalize_number(args.number, kind="issue or PR number")
        issue = client.get_issue(number)
        payload: dict[str, Any] = {"kind": "issue", "issue": issue}
        if "pull_request" in issue:
            payload = {"kind": "pr", "issue": issue, "pull": client.get_pull(number)}
        print(json.dumps(payload, ensure_ascii=False))
    elif args.command == "statuses":
        print(json.dumps(client.statuses(args.sha)))
    elif args.command == "require-ci":
        require_ci_success(
            client,
            normalize_number(args.number),
            args.sha,
            args.base_sha,
        )
        print(args.sha)
    elif args.command == "post-status":
        guard = client.publication_guard(args.guard_file) if args.guard_file else None
        client.post_status(
            args.sha,
            args.context,
            args.state,
            args.description,
            before_mutation=guard,
        )
    elif args.command == "comment-once":
        guard = client.publication_guard(args.guard_file) if args.guard_file else None
        row = client.comment_once(
            normalize_number(args.number),
            _read_body(args.body_file),
            args.marker,
            before_mutation=guard,
        )
        print(json.dumps(row))
    elif args.command == "review-once":
        guard = client.publication_guard(args.guard_file) if args.guard_file else None
        local_guard = (
            client.publication_guard(args.guard_file, authoritative=False)
            if args.guard_file
            else None
        )
        row, event = client.review_once(
            normalize_number(args.number),
            args.commit_id,
            _read_body(args.body_file),
            args.event,
            args.marker,
            before_mutation=guard,
            before_write=local_guard,
        )
        print(json.dumps({"review": row, "event": event}))
    elif args.command == "comments":
        print(json.dumps(client.comments(normalize_number(args.number))))
    elif args.command == "reviews":
        print(json.dumps(client.reviews(normalize_number(args.number))))
    elif args.command == "commits":
        print(json.dumps(client.pull_commits(normalize_number(args.number))))
    elif args.command == "fix-count":
        rows = client.pull_commits(normalize_number(args.number))
        print(fix_iteration_count(rows))
    elif args.command == "ci-manifest":
        _, manifest = client.ci_manifest(
            normalize_number(args.number), args.sha, args.base_sha
        )
        print(json.dumps(manifest, ensure_ascii=False))
    elif args.command == "ci-evidence":
        evidence = client.ci_success_evidence(
            normalize_number(args.number), args.sha, args.base_sha
        )
        print(json.dumps(evidence.as_dict(), ensure_ascii=False))
    elif args.command == "ci-finalize":
        guard = client.publication_guard(args.guard_file) if args.guard_file else None
        local_guard = (
            client.publication_guard(args.guard_file, authoritative=False)
            if args.guard_file
            else None
        )
        evidence = client.finalize_ci_status(
            normalize_number(args.number),
            args.sha,
            args.base_sha,
            args.run_id,
            before_mutation=guard,
            before_write=local_guard,
        )
        print(json.dumps(evidence.as_dict(), ensure_ascii=False))
    elif args.command == "review-ledger":
        row = client.review_ledger(
            normalize_number(args.number), args.sha, args.base_sha
        )
        print(str(row.get("body") or ""))
    elif args.command == "review-attestation":
        attestation = client.review_attestation(
            normalize_number(args.number), args.sha, args.base_sha
        )
        payload = {
            **attestation.as_dict(),
            "body": str(attestation.row.get("body") or ""),
        }
        print(json.dumps(payload, ensure_ascii=False))
    elif args.command == "review-state":
        state = client.review_publication_state(
            normalize_number(args.number), args.sha, args.base_sha
        )
        print(json.dumps(state, ensure_ascii=False))
    elif args.command == "review-finalize":
        guard = client.publication_guard(args.guard_file) if args.guard_file else None
        local_guard = (
            client.publication_guard(args.guard_file, authoritative=False)
            if args.guard_file
            else None
        )
        evidence = client.finalize_review_status(
            normalize_number(args.number),
            args.sha,
            args.base_sha,
            args.run_id,
            args.digest,
            before_mutation=guard,
            before_write=local_guard,
        )
        print(json.dumps(evidence.as_dict(), ensure_ascii=False))
    elif args.command == "review-evidence":
        evidence = client.review_evidence(
            normalize_number(args.number), args.sha, args.base_sha
        )
        print(json.dumps(evidence.as_dict(), ensure_ascii=False))
    elif args.command == "review-session":
        evidence = validate_reviewer_session(
            args.dispatch_log,
            args.telemetry,
            lane=args.lane,
            number=normalize_number(args.number, kind="PR number"),
            worktree=args.worktree,
            expected_exit=args.expected_exit,
        )
        print(json.dumps(evidence.as_dict(), ensure_ascii=False))
    elif args.command == "latest-review-ledger":
        row = client.latest_review_ledger(normalize_number(args.number))
        if row is not None:
            print(str(row.get("body") or ""))
    elif args.command == "remove-label":
        client.remove_label(normalize_number(args.number), args.label)
    elif args.command == "snapshot":
        print(json.dumps(write_snapshot(client, args.destination)))
    else:  # pragma: no cover
        raise GitHubError(f"unknown command {args.command}")
    return 0


def main() -> int:
    try:
        return cli()
    except (GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"github_api.py: {_safe_text(str(exc))}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
