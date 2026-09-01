#!/usr/bin/env python3
"""Merge a GitHub pull request after all exact-head local gates pass."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any, Iterator, Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))
from github_api import (  # noqa: E402
    ADJUDICATION_LABEL,
    CI_SUMMARY_CONTEXT,
    CIManifestEvidence,
    GitHub,
    GitHubError,
    PullIdentity,
    REVIEW_CONTEXT,
    ReviewAttestation,
    ReviewEvidence,
    fix_iteration_count,
    normalize_number,
    normalize_sha,
    pull_identity,
    render_status_description,
)


DEFAULT_FIX_CAP = 5
REQUIRED_STATUS_CONTEXTS = {CI_SUMMARY_CONTEXT, REVIEW_CONTEXT}
ADJUDICATION_MARKER_RE = re.compile(
    r"<!-- mipstarre:adjudication pr=(\d+) "
    r"head=((?:[0-9a-f]{40}|[0-9a-f]{64})) "
    r"base=((?:[0-9a-f]{40}|[0-9a-f]{64})) review=(\d+) "
    r"run=([^<>\s]+) digest=([0-9a-f]{64}) body=([0-9a-f]{64}) -->"
)


class GateFailure(RuntimeError):
    """A merge-gate refusal with an operator-facing explanation."""


class NonconformingMerge(GateFailure):
    """An already-merged result that cannot be attributed to this local gate."""


@dataclass(frozen=True)
class GateExpectation:
    """The immutable PR comparison accepted for this merge invocation."""

    branch: str
    base: str
    head_sha: str
    base_sha: str


@dataclass(frozen=True)
class GateSnapshot:
    """One complete evaluation of all merge evidence."""

    pull: dict[str, Any]
    identity: PullIdentity
    worktree: Path
    ci: CIManifestEvidence
    review: ReviewEvidence | AdjudicationEvidence
    iterations: int


@dataclass(frozen=True)
class AdjudicationEvidence:
    """A unique, unedited adjudication bound to its latest source review."""

    comment: dict[str, Any]
    payload: dict[str, Any]
    source: ReviewAttestation
    digest: str


@dataclass(frozen=True)
class HeldLock:
    path: Path
    pid: int

    def require_owned(self, *, reject_cancel: bool = False) -> None:
        try:
            recorded = int((self.path / "pid").read_text(encoding="utf-8").strip())
        except (OSError, ValueError) as exc:
            raise GateFailure(f"reserved lock {self.path} lost its owner record") from exc
        if not self.path.is_dir() or recorded != self.pid:
            raise GateFailure(f"reserved lock {self.path} is no longer owned by this merge")
        if reject_cancel and (self.path / "cancel").exists():
            raise GateFailure(
                f"an auto-fix attempted to supersede the reserved merge lock {self.path}"
            )


def git(root: Path, *arguments: str, check: bool = True) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *arguments],
        text=True,
        capture_output=True,
        check=False,
    )
    if check and result.returncode != 0:
        raise GateFailure(
            result.stderr.strip() or f"git {' '.join(arguments)} failed"
        )
    return result.stdout.strip()


def primary_root(value: Path | None) -> Path:
    root = (value or Path.cwd()).resolve()
    common = git(root, "rev-parse", "--path-format=absolute", "--git-common-dir")
    common_path = Path(common)
    return common_path.parent if common_path.name == ".git" else root


def branch_worktree(root: Path, branch: str) -> Path | None:
    current: Path | None = None
    for line in git(root, "worktree", "list", "--porcelain").splitlines():
        if line.startswith("worktree "):
            current = Path(line.removeprefix("worktree "))
        elif line == f"branch refs/heads/{branch}" and current is not None:
            return current
    return None


def exact_local_head(root: Path, branch: str) -> tuple[str, Path]:
    if any(ch in branch for ch in "[]~^:?*\\ \t\r\n"):
        raise GateFailure(f"unsafe GitHub head branch {branch!r}")
    worktree = branch_worktree(root, branch)
    if worktree is None or not worktree.is_dir():
        raise GateFailure(f"no local worktree is registered for PR branch {branch!r}")
    symbolic = git(worktree, "symbolic-ref", "--quiet", "--short", "HEAD")
    if symbolic != branch:
        raise GateFailure(
            f"worktree {worktree} is on {symbolic!r}, expected {branch!r}"
        )
    return normalize_sha(git(worktree, "rev-parse", "HEAD")), worktree


def require_clean_worktree(worktree: Path) -> None:
    dirty = git(
        worktree,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
    )
    if dirty:
        raise GateFailure(
            f"merge worktree {worktree} is dirty at a gate boundary"
        )


def _contexts_from_classic(value: dict[str, Any]) -> set[str]:
    raw_contexts = value.get("contexts")
    raw_checks = value.get("checks")
    context_sets: list[set[str]] = []
    if raw_contexts is not None:
        if not isinstance(raw_contexts, list) or not all(
            isinstance(item, str) and item for item in raw_contexts
        ):
            raise GateFailure("classic required status contexts are malformed")
        context_sets.append({item.casefold() for item in raw_contexts})
    if not isinstance(raw_checks, list) or not all(
        isinstance(item, dict)
        and isinstance(item.get("context"), str)
        and item.get("context")
        and "app_id" in item
        and (
            item.get("app_id") is None
            or (type(item.get("app_id")) is int and item.get("app_id") == -1)
        )
        for item in raw_checks
    ):
        raise GateFailure(
            "classic required status checks must name PAT producers "
            "with app_id null or -1"
        )
    context_sets.append(
        {str(item["context"]).casefold() for item in raw_checks}
    )
    if not context_sets or any(value != context_sets[0] for value in context_sets[1:]):
        raise GateFailure("classic required status context representations disagree")
    return context_sets[0]


def _empty_actor_allowances(value: Any) -> bool:
    if value is None:
        return True
    return (
        isinstance(value, dict)
        and set(value) == {"users", "teams", "apps"}
        and all(value.get(key) == [] for key in ("users", "teams", "apps"))
    )


def _require_zero_approval_rule(value: dict[str, Any], *, source: str) -> None:
    approvals = value.get("required_approving_review_count")
    code_owner_key = (
        "require_code_owner_reviews"
        if "require_code_owner_reviews" in value
        else "require_code_owner_review"
    )
    if type(approvals) is not int or approvals != 0:
        raise GateFailure(f"{source} must require exactly zero approvals")
    if value.get(code_owner_key) is not False:
        raise GateFailure(f"{source} must not require code-owner review")
    if value.get("require_last_push_approval") is not False:
        raise GateFailure(f"{source} must not require last-push approval")


def require_server_policy(client: GitHub, base: str) -> None:
    """Validate classic protection and every active effective ruleset."""
    try:
        client.verify_authenticated_actor()
        repository = client.repository_metadata()
        protection = client.branch_protection(base)
        rules = client.branch_rules(base)
    except GitHubError as exc:
        raise GateFailure(
            f"cannot validate server policy for actual base {base!r}: {exc}"
        ) from exc

    if repository.get("allow_merge_commit") is not True:
        raise GateFailure("repository settings must allow merge commits")

    status_rule = protection.get("required_status_checks")
    if not isinstance(status_rule, dict) or status_rule.get("strict") is not True:
        raise GateFailure("classic branch protection must use strict required checks")
    if _contexts_from_classic(status_rule) != {
        context.casefold() for context in REQUIRED_STATUS_CONTEXTS
    }:
        raise GateFailure(
            "classic branch protection must require exactly local-ci/summary "
            "and local-review/summary"
        )
    admins = protection.get("enforce_admins")
    if not isinstance(admins, dict) or admins.get("enabled") is not True:
        raise GateFailure("classic branch protection must enforce administrators")
    reviews = protection.get("required_pull_request_reviews")
    if not isinstance(reviews, dict):
        raise GateFailure("classic branch protection needs a pull-request review rule")
    _require_zero_approval_rule(reviews, source="classic pull-request review rule")
    if not _empty_actor_allowances(reviews.get("bypass_pull_request_allowances")):
        raise GateFailure("classic pull-request bypass allowances must be empty")
    for field, label in (
        ("allow_force_pushes", "force pushes"),
        ("allow_deletions", "branch deletions"),
    ):
        value = protection.get(field)
        if not isinstance(value, dict) or value.get("enabled") is not False:
            raise GateFailure(f"classic branch protection must disable {label}")

    ruleset_ids: set[int] = set()
    for rule in rules:
        rule_type = str(rule.get("type") or "")
        parameters = rule.get("parameters")
        if rule_type == "merge_queue":
            raise GateFailure("an active merge queue is incompatible with one-shot merge")
        if rule_type == "required_status_checks":
            if not isinstance(parameters, dict):
                raise GateFailure("effective required-status rule is malformed")
            raw_checks = parameters.get("required_status_checks")
            if not isinstance(raw_checks, list) or not all(
                isinstance(item, dict)
                and isinstance(item.get("context"), str)
                and item.get("context")
                and "integration_id" in item
                and (
                    item.get("integration_id") is None
                    or (
                        type(item.get("integration_id")) is int
                        and item.get("integration_id") == -1
                    )
                )
                for item in raw_checks
            ):
                raise GateFailure(
                    "effective required-status checks must name PAT producers "
                    "with integration_id null or -1"
                )
            contexts = {str(item["context"]).casefold() for item in raw_checks}
            if (
                parameters.get("strict_required_status_checks_policy") is not True
                or not {item.casefold() for item in REQUIRED_STATUS_CONTEXTS}
                <= contexts
            ):
                raise GateFailure(
                    "effective required-status rules weaken strict summary checks"
                )
        if rule_type == "pull_request":
            if not isinstance(parameters, dict):
                raise GateFailure("effective pull-request rule is malformed")
            _require_zero_approval_rule(
                parameters, source="effective pull-request rule"
            )
            methods = parameters.get("allowed_merge_methods")
            if methods is not None and (
                not isinstance(methods, list) or "merge" not in methods
            ):
                raise GateFailure("effective rules do not permit a merge commit")
        ruleset_id = rule.get("ruleset_id")
        if ruleset_id is not None:
            if type(ruleset_id) is not int or ruleset_id <= 0:
                raise GateFailure("effective rule has an invalid ruleset id")
            ruleset_ids.add(ruleset_id)

    for ruleset_id in ruleset_ids:
        try:
            ruleset = client.ruleset(ruleset_id)
        except GitHubError as exc:
            raise GateFailure(f"cannot validate effective ruleset {ruleset_id}: {exc}") from exc
        if ruleset.get("enforcement") != "active":
            raise GateFailure(f"effective ruleset {ruleset_id} is not provably active")
        if ruleset.get("bypass_actors") != []:
            raise GateFailure(f"effective ruleset {ruleset_id} has bypass actors")


def require_open_mergeable(pull: dict[str, Any], number: int) -> PullIdentity:
    if str(pull.get("state") or "").casefold() != "open":
        raise GateFailure(f"PR #{number} is not open")
    if bool(pull.get("draft")):
        raise GateFailure(f"PR #{number} is a draft")
    if pull.get("mergeable") is not True:
        state = pull.get("mergeable_state") or "unknown"
        raise GateFailure(f"PR #{number} is not proven mergeable (state={state})")
    return pull_identity(pull)


def require_ci(
    client: GitHub, number: int, head_sha: str, base_sha: str
) -> CIManifestEvidence:
    try:
        evidence = client.ci_success_evidence(number, head_sha, base_sha)
    except GitHubError as exc:
        raise GateFailure(f"invalid exact-head CI evidence: {exc}") from exc
    manifest = evidence.manifest
    if str(manifest.get("conclusion") or "") != "success":
        raise GateFailure("the exact-run CI manifest conclusion is not success")
    failures = [
        f"{step.get('step')}={step.get('outcome')}"
        for step in manifest.get("steps") or []
        if str(step.get("outcome") or "") not in {"success", "skipped"}
    ]
    if failures:
        raise GateFailure("exact-head CI gate failed: " + ", ".join(failures))
    return evidence


def row_order(row: dict[str, Any]) -> tuple[datetime, int]:
    raw_timestamp = str(row.get("submitted_at") or row.get("created_at") or "")
    identifier = row.get("id")
    if type(identifier) is not int or identifier <= 0 or not raw_timestamp:
        raise GateFailure("review ordering evidence lacks an id or timestamp")
    try:
        timestamp = datetime.fromisoformat(raw_timestamp.replace("Z", "+00:00"))
    except ValueError as exc:
        raise GateFailure("review ordering evidence has an invalid timestamp") from exc
    if timestamp.utcoffset() is None:
        raise GateFailure("review ordering evidence has a timezone-free timestamp")
    return timestamp, identifier


def require_review(
    client: GitHub, number: int, sha: str, base_sha: str | None = None
) -> ReviewEvidence:
    try:
        evidence = client.review_evidence(number, sha, base_sha)
    except GitHubError as exc:
        raise GateFailure(f"no valid exact-head review attestation: {exc}") from exc
    attestation = evidence.attestation
    ledger = attestation.row
    if (
        attestation.event != "COMMENT"
        or attestation.fallback != "none"
        or attestation.findings != 0
        or str(ledger.get("state") or "").upper() != "COMMENTED"
    ):
        raise GateFailure(
            "the selected exact-head review is not a clean COMMENT attestation"
        )
    ledger_order = row_order(ledger)
    for review in client.reviews(number):
        if str(review.get("commit_id") or "").lower() != sha:
            continue
        if str(review.get("state") or "").upper() != "CHANGES_REQUESTED":
            continue
        if row_order(review) > ledger_order:
            raise GateFailure("a later exact-head CHANGES_REQUESTED review is unresolved")
    return evidence


def adjudication_status_description(evidence: AdjudicationEvidence) -> str:
    review_id = evidence.source.row.get("id")
    return (
        f"local adjudication review={review_id} run={evidence.source.run_id} "
        f"source={evidence.source.digest} body={evidence.digest}"
    )


def _required_nonempty_text(value: Any, *, field: str) -> str:
    if not isinstance(value, str) or value != value.strip() or not value:
        raise GateFailure(f"adjudication {field} must be a nonempty trimmed string")
    if len(value) > 1000 or any(ord(character) < 32 for character in value):
        raise GateFailure(f"adjudication {field} contains invalid text")
    return value


def _adjudication_comment_has_shape(
    client: GitHub,
    row: dict[str, Any],
    *,
    number: int,
    sha: str,
    base_sha: str,
) -> bool:
    """Recognize an unedited trusted comment for the exact comparison."""
    if not client.is_trusted_actor_row(
        row, field="user", kind="adjudication comment"
    ):
        return False
    created = str(row.get("created_at") or "")
    if not created or str(row.get("updated_at") or "") != created:
        return False
    body = str(row.get("body") or "")
    matches = list(ADJUDICATION_MARKER_RE.finditer(body))
    if len(matches) != 1 or body.count("<!-- mipstarre:adjudication ") != 1:
        return False
    marker_match = matches[0]
    marker = marker_match.group(0)
    if body[marker_match.start() :] not in {marker, marker + "\n"}:
        return False
    prefix = body[: marker_match.start()]
    if re.fullmatch(r"ADJUDICATION\n\n```json\n.*\n```\n\n", prefix, re.DOTALL) is None:
        return False
    return (
        int(marker_match.group(1)) == number
        and marker_match.group(2).lower() == sha
        and marker_match.group(3).lower() == base_sha
    )


def require_adjudication(
    client: GitHub,
    pull: dict[str, Any],
    number: int,
    sha: str,
    base_sha: str,
    *,
    require_status: bool,
) -> AdjudicationEvidence:
    try:
        client.verify_authenticated_actor()
    except GitHubError as exc:
        raise GateFailure(f"cannot verify trusted adjudication actor: {exc}") from exc
    labels = {
        str(item.get("name") if isinstance(item, dict) else item)
        for item in (pull.get("labels") or [])
    }
    if ADJUDICATION_LABEL not in labels:
        raise GateFailure(f"adjudicated merge requires label {ADJUDICATION_LABEL!r}")
    adjudications = [
        row
        for row in client.comments(number)
        if _adjudication_comment_has_shape(
            client, row, number=number, sha=sha, base_sha=base_sha
        )
    ]
    if len(adjudications) != 1:
        raise GateFailure(
            "the PR must contain exactly one structurally valid, unedited "
            "trusted ADJUDICATION comment for this comparison"
        )
    comment = adjudications[0]
    try:
        client.require_trusted_actor_row(
            comment, field="user", kind="adjudication comment"
        )
    except GitHubError as exc:  # Defensive: selection above owns this invariant.
        raise GateFailure(str(exc)) from exc
    created = str(comment.get("created_at") or "")
    updated = str(comment.get("updated_at") or "")
    if not created or created != updated:
        raise GateFailure("the ADJUDICATION comment must be unedited")
    row_order(comment)

    body = str(comment.get("body") or "")
    marker_matches = list(ADJUDICATION_MARKER_RE.finditer(body))
    if (
        len(marker_matches) != 1
        or body.count("<!-- mipstarre:adjudication ") != 1
    ):
        raise GateFailure("the ADJUDICATION comment has an ambiguous marker")
    marker_match = marker_matches[0]
    marker = marker_match.group(0)
    if body[marker_match.start() :] not in {marker, marker + "\n"}:
        raise GateFailure("the adjudication marker must be the final body line")
    prefix = body[: marker_match.start()]
    body_digest = hashlib.sha256(prefix.encode("utf-8")).hexdigest()
    if marker_match.group(7) != body_digest:
        raise GateFailure("the adjudication body digest does not match")
    fenced = re.fullmatch(
        r"ADJUDICATION\n\n```json\n(.*?)\n```\n\n", prefix, re.DOTALL
    )
    if fenced is None or prefix.count("```json") != 1:
        raise GateFailure("the ADJUDICATION comment has no canonical JSON body")
    try:
        payload = json.loads(fenced.group(1))
    except json.JSONDecodeError as exc:
        raise GateFailure("the ADJUDICATION JSON is invalid") from exc
    if fenced.group(1) != json.dumps(payload, indent=2, sort_keys=True):
        raise GateFailure("the ADJUDICATION JSON is not canonically serialized")
    expected_keys = {
        "schema",
        "pr",
        "head_sha",
        "base_sha",
        "source_review",
        "rounds",
        "dispositions",
    }
    if not isinstance(payload, dict) or set(payload) != expected_keys:
        raise GateFailure("the ADJUDICATION JSON has a noncanonical schema")
    if type(payload.get("schema")) is not int or payload.get("schema") != 1:
        raise GateFailure("the ADJUDICATION schema version is invalid")
    try:
        payload_head = normalize_sha(
            str(payload.get("head_sha") or ""), kind="adjudication head SHA"
        )
        payload_base = normalize_sha(
            str(payload.get("base_sha") or ""), kind="adjudication base SHA"
        )
        marker_head = normalize_sha(marker_match.group(2))
        marker_base = normalize_sha(marker_match.group(3))
    except GitHubError as exc:
        raise GateFailure(str(exc)) from exc
    if (
        type(payload.get("pr")) is not int
        or payload.get("pr") != number
        or int(marker_match.group(1)) != number
        or payload_head != sha
        or marker_head != sha
        or payload_base != base_sha
        or marker_base != base_sha
    ):
        raise GateFailure("the ADJUDICATION comment names a different comparison")

    try:
        attestations = client.review_attestations(number)
    except GitHubError as exc:
        raise GateFailure(f"adjudication review rounds are invalid: {exc}") from exc
    if not attestations:
        raise GateFailure("adjudication has no validated source review")
    source = max(attestations, key=lambda item: row_order(item.row))
    source_id = source.row.get("id")
    source_payload = payload.get("source_review")
    source_keys = {"review_id", "run_id", "digest"}
    if not isinstance(source_payload, dict) or set(source_payload) != source_keys:
        raise GateFailure("adjudication source_review is noncanonical")
    if (
        type(source_id) is not int
        or source_id <= 0
        or type(source_payload.get("review_id")) is not int
        or source.head_sha != sha
        or source.base_sha != base_sha
        or source.findings <= 0
        or source_payload.get("review_id") != source_id
        or source_payload.get("run_id") != source.run_id
        or source_payload.get("digest") != source.digest
        or int(marker_match.group(4)) != source_id
        or marker_match.group(5) != source.run_id
        or marker_match.group(6) != source.digest
    ):
        raise GateFailure("adjudication is not bound to the latest source review")
    source_order = row_order(source.row)
    for review in client.reviews(number):
        if str(review.get("commit_id") or "").lower() != sha:
            continue
        state = str(review.get("state") or "").upper()
        authoritative_comment = client.is_trusted_actor_row(
            review, field="user", kind="review row"
        )
        if row_order(review) > source_order and (
            state == "CHANGES_REQUESTED" or authoritative_comment
        ):
            raise GateFailure("a later exact-head review supersedes the adjudication source")
    if row_order(comment) <= source_order:
        raise GateFailure("the adjudication comment must be strictly later than its source review")

    raw_rounds = payload.get("rounds")
    if not isinstance(raw_rounds, list) or len(raw_rounds) < 4:
        raise GateFailure("adjudication requires at least four validated review rounds")
    by_id = {item.row.get("id"): item for item in attestations}
    rounds: list[ReviewAttestation] = []
    round_ids: set[int] = set()
    round_runs: set[str] = set()
    round_digests: set[str] = set()
    for raw_round in raw_rounds:
        if not isinstance(raw_round, dict) or set(raw_round) != source_keys:
            raise GateFailure("adjudication contains a noncanonical review round")
        review_id = raw_round.get("review_id")
        if type(review_id) is not int or review_id not in by_id:
            raise GateFailure("adjudication names an unknown review round")
        attestation = by_id[review_id]
        if (
            attestation.head_sha != sha
            or attestation.base_sha != base_sha
            or raw_round.get("run_id") != attestation.run_id
            or raw_round.get("digest") != attestation.digest
            or review_id in round_ids
            or attestation.run_id in round_runs
            or attestation.digest in round_digests
        ):
            raise GateFailure("adjudication review rounds are duplicated or mismatched")
        round_ids.add(review_id)
        round_runs.add(attestation.run_id)
        round_digests.add(attestation.digest)
        rounds.append(attestation)
    if rounds[-1] is not source or rounds != sorted(
        rounds, key=lambda item: row_order(item.row)
    ):
        raise GateFailure("adjudication rounds must be ordered and end at the source")

    eligible = {
        finding.key
        for finding in source.finding_rows
        if finding.state == "unresolved"
    }
    raw_dispositions = payload.get("dispositions")
    if not isinstance(raw_dispositions, list):
        raise GateFailure("adjudication dispositions must be a list")
    disposed: set[str] = set()
    for disposition in raw_dispositions:
        if not isinstance(disposition, dict):
            raise GateFailure("adjudication contains a malformed disposition")
        finding = disposition.get("finding")
        outcome = disposition.get("outcome")
        if not isinstance(finding, str) or finding in disposed:
            raise GateFailure("adjudication repeats or malforms a finding disposition")
        disposed.add(finding)
        if outcome == "fixed":
            if set(disposition) != {"finding", "outcome", "reason", "evidence"}:
                raise GateFailure("fixed dispositions need exactly reason and evidence")
            _required_nonempty_text(disposition.get("reason"), field="fixed reason")
            _required_nonempty_text(
                disposition.get("evidence"), field="fixed evidence"
            )
        elif outcome == "tracked":
            if set(disposition) != {"finding", "outcome", "issue"}:
                raise GateFailure("tracked dispositions need exactly one issue number")
            issue_number = disposition.get("issue")
            if type(issue_number) is not int or issue_number <= 0:
                raise GateFailure("tracked disposition issue must be positive")
            try:
                issue = client.get_issue(issue_number)
            except GitHubError as exc:
                raise GateFailure(
                    f"tracked disposition issue #{issue_number} is unreadable: {exc}"
                ) from exc
            expected_url = f"https://github.com/{client.repo}/issues/{issue_number}"
            if (
                str(issue.get("state") or "").casefold() != "open"
                or "pull_request" in issue
                or str(issue.get("html_url") or "") != expected_url
            ):
                raise GateFailure(
                    f"tracked disposition issue #{issue_number} is not an open "
                    "same-repository issue"
                )
        else:
            raise GateFailure("adjudication outcome must be exactly fixed or tracked")
    if disposed != eligible:
        raise GateFailure(
            "adjudication dispositions do not exactly cover eligible unresolved findings"
        )

    evidence = AdjudicationEvidence(
        comment=comment,
        payload=payload,
        source=source,
        digest=body_digest,
    )
    if require_status:
        status = client.latest_statuses(sha).get(REVIEW_CONTEXT.casefold()) or {}
        try:
            client.require_trusted_actor_row(
                status, field="creator", kind=f"{REVIEW_CONTEXT} status"
            )
        except GitHubError as exc:
            raise GateFailure(str(exc)) from exc
        expected = render_status_description(
            sha,
            REVIEW_CONTEXT,
            "success",
            adjudication_status_description(evidence),
        )
        if (
            str(status.get("state") or "").casefold() != "success"
            or str(status.get("description") or "") != expected
        ):
            raise GateFailure(
                "local-review/summary is not the exact validated adjudication success"
            )
    return evidence


def require_no_live_fix(cache: Path, branch: str) -> None:
    lock = cache / "locks" / f"fix-{branch.replace('/', '-')}.lock"
    if not lock.is_dir():
        return
    try:
        pid = int((lock / "pid").read_text(encoding="utf-8").strip())
    except (OSError, ValueError):
        return
    try:
        os.kill(pid, 0)
    except OSError:
        return
    raise GateFailure(f"live auto-fix lock {lock} is held by pid {pid}")


@contextmanager
def reserve_runtime_lock(path: Path, label: str) -> Iterator[HeldLock]:
    """Atomically reserve one runtime lock and release only our lease."""
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        path.mkdir()
    except FileExistsError as exc:
        try:
            holder = int((path / "pid").read_text(encoding="utf-8").strip())
            if holder <= 0:
                holder = None
        except (OSError, ValueError):
            holder = None
        state = f"live pid {holder}" if holder is not None else "unproven owner"
        if holder is not None:
            try:
                os.kill(holder, 0)
            except ProcessLookupError:
                state = f"stale pid {holder}"
            except PermissionError:
                pass
        recovery = ""
        if holder is None or state.startswith("stale pid"):
            recovery = (
                "; after verifying no CI, review, auto-fix, or merge process "
                f"owns it, remove {path} explicitly and retry"
            )
        raise GateFailure(
            f"cannot reserve runtime lock {path} ({state}){recovery}"
        ) from exc
    held = HeldLock(path=path, pid=os.getpid())
    try:
        (path / "pid").write_text(f"{held.pid}\n", encoding="utf-8")
        (path / "owner").write_text(
            f"{held.pid}\nmerge-reservation\n{label}\n", encoding="utf-8"
        )
        (path / "label").write_text(label + "\n", encoding="utf-8")
        held.require_owned()
        yield held
    finally:
        try:
            owner = int((path / "pid").read_text(encoding="utf-8").strip())
        except (OSError, ValueError):
            owner = None
        if owner == held.pid:
            shutil.rmtree(path)


def require_merge_capability(client: GitHub) -> None:
    result = client.run(["pr", "merge", "--help"], retry=True)
    if "--match-head-commit" not in result.stdout:
        raise GateFailure(
            "installed gh lacks 'pr merge --match-head-commit'; upgrade before merging"
        )


def exact_local_base(root: Path, base: str) -> str:
    reference = f"refs/remotes/github/{base}^{{commit}}"
    try:
        return normalize_sha(git(root, "rev-parse", "--verify", reference))
    except (GateFailure, GitHubError) as exc:
        raise GateFailure(f"fetched GitHub base ref does not resolve: {reference}") from exc


def _require_expected(identity: PullIdentity, expected: GateExpectation) -> None:
    observed = GateExpectation(
        branch=identity.branch,
        base=identity.base,
        head_sha=identity.head_sha,
        base_sha=identity.base_sha,
    )
    if observed != expected:
        raise GateFailure(
            "PR head/base changed during merge gating "
            f"(expected={expected}, observed={observed})"
        )


def evaluate_gate(
    client: GitHub,
    number: int,
    expected: GateExpectation,
    root: Path,
    review_lock: HeldLock,
    fix_lock: HeldLock,
    ci_lock: HeldLock,
    cap: int,
    *,
    adjudicated: bool,
    require_adjudication_status: bool = True,
) -> GateSnapshot:
    """Evaluate the complete fail-closed gate from authoritative state."""
    client.verify_authenticated_actor()
    review_lock.require_owned()
    ci_lock.require_owned()
    fix_lock.require_owned(reject_cancel=True)
    pull = client.get_pull(number)
    identity = require_open_mergeable(pull, number)
    _require_expected(identity, expected)
    require_server_policy(client, identity.base)
    local_head, worktree = exact_local_head(root, expected.branch)
    local_base = exact_local_base(root, expected.base)
    if local_head != expected.head_sha or local_base != expected.base_sha:
        raise GateFailure(
            "local head/base do not match the immutable GitHub comparison "
            f"(local_head={local_head}, local_base={local_base})"
        )
    require_clean_worktree(worktree)

    ci = require_ci(client, number, expected.head_sha, expected.base_sha)
    fix_lock.require_owned(reject_cancel=True)
    commits = client.pull_commits(number)
    iterations = fix_iteration_count(commits)
    if iterations > cap:
        raise GateFailure(
            f"fix iteration count {iterations} exceeds configured cap {cap}"
        )
    # Rebind the comparison after all potentially paginated reads. The review
    # check is last so a same-head adverse review introduced during evaluation
    # cannot be hidden by an earlier clean-ledger read.
    final_pull = client.get_pull(number)
    final_identity = require_open_mergeable(final_pull, number)
    _require_expected(final_identity, expected)
    require_server_policy(client, final_identity.base)
    final_local_head, final_worktree = exact_local_head(root, expected.branch)
    final_local_base = exact_local_base(root, expected.base)
    if (
        final_local_head != expected.head_sha
        or final_local_base != expected.base_sha
        or final_worktree.resolve() != worktree.resolve()
    ):
        raise GateFailure("local head/base/worktree changed during gate evaluation")
    require_clean_worktree(final_worktree)
    fix_lock.require_owned(reject_cancel=True)
    if adjudicated:
        review: ReviewEvidence | AdjudicationEvidence = require_adjudication(
            client,
            final_pull,
            number,
            expected.head_sha,
            expected.base_sha,
            require_status=require_adjudication_status,
        )
        attested_worktree = Path(review.source.lanes[0].worktree).resolve()
    else:
        review = require_review(
            client, number, expected.head_sha, expected.base_sha
        )
        attested_worktree = Path(review.attestation.lanes[0].worktree).resolve()
    if attested_worktree != worktree.resolve():
        raise GateFailure(
            "review session telemetry is bound to a different feature worktree"
        )
    review_lock.require_owned()
    ci_lock.require_owned()
    fix_lock.require_owned(reject_cancel=True)
    require_clean_worktree(final_worktree)
    return GateSnapshot(
        pull=final_pull,
        identity=final_identity,
        worktree=worktree,
        ci=ci,
        review=review,
        iterations=iterations,
    )


def merge_once(
    client: GitHub,
    number: int,
    expected: GateExpectation,
    command: Sequence[str],
) -> tuple[dict[str, Any], str]:
    """Issue one merge mutation and reconcile its result by read-back only."""
    mutation_error: GitHubError | None = None
    client.verify_authenticated_actor()
    try:
        client.run(command, retry=False)
    except GitHubError as exc:
        mutation_error = exc

    merged = client.get_pull(number)
    if merged.get("merged") is not True:
        if mutation_error is not None and mutation_error.transient:
            raise GateFailure(
                "merge outcome is ambiguous after authoritative read-back; "
                "the merge mutation was not retried"
            ) from mutation_error
        if mutation_error is not None:
            raise mutation_error
        raise GateFailure("gh returned success but GitHub does not report the PR merged")
    if str(merged.get("state") or "").casefold() != "closed":
        raise NonconformingMerge(
            "external/nonconforming result: merged=true but the PR is not closed"
        )
    try:
        merged_identity = pull_identity(merged)
        merge_sha = normalize_sha(
            str(merged.get("merge_commit_sha") or ""), kind="merge commit SHA"
        )
    except GitHubError as exc:
        raise NonconformingMerge(
            f"external/nonconforming merged identity: {exc}"
        ) from exc
    if (
        merged_identity.branch != expected.branch
        or merged_identity.base != expected.base
        or merged_identity.head_sha != expected.head_sha
    ):
        raise NonconformingMerge(
            "external/nonconforming result changed the frozen head/ref/base-ref identity"
        )
    try:
        commit = client.git_commit(merge_sha)
        commit_sha = normalize_sha(
            str(commit.get("sha") or ""), kind="reported merge Git commit SHA"
        )
        raw_parents = commit.get("parents")
        if not isinstance(raw_parents, list) or len(raw_parents) != 2:
            raise GitHubError("reported merge commit does not have exactly two parents")
        parents = [
            normalize_sha(
                str(parent.get("sha") or ""), kind="reported merge parent SHA"
            )
            for parent in raw_parents
            if isinstance(parent, dict)
        ]
        if commit_sha != merge_sha or parents != [expected.base_sha, expected.head_sha]:
            raise GitHubError(
                "reported merge commit parents are not frozen base then frozen head"
            )
    except (GitHubError, AttributeError) as exc:
        raise NonconformingMerge(
            f"external/nonconforming merge commit: {exc}"
        ) from exc
    return merged, merge_sha


def fast_forward_base(root: Path, base: str) -> None:
    git(
        root,
        "fetch",
        "--no-tags",
        "github",
        f"refs/heads/{base}:refs/remotes/github/{base}",
    )
    worktree = branch_worktree(root, base)
    if worktree is None:
        raise GateFailure(
            f"GitHub merged the PR, but no local checkout of base branch {base!r} exists"
        )
    if git(worktree, "status", "--porcelain"):
        raise GateFailure(
            f"GitHub merged the PR, but base worktree {worktree} is dirty; "
            "it was not advanced"
        )
    git(worktree, "merge", "--ff-only", f"refs/remotes/github/{base}")


def cleanup_feature(root: Path, branch: str, worktree: Path, merge_sha: str) -> None:
    if git(worktree, "status", "--porcelain"):
        raise GateFailure(
            f"PR merged, but feature worktree {worktree} is dirty; cleanup was skipped"
        )
    ancestor = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", branch, merge_sha],
        check=False,
    )
    if ancestor.returncode != 0:
        raise GateFailure(
            f"PR merged, but local branch {branch!r} is not contained in {merge_sha}; "
            "cleanup was skipped"
        )
    git(root, "worktree", "remove", str(worktree))
    git(root, "branch", "-d", branch)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("number", help="GitHub pull-request number")
    parser.add_argument("--adjudicated", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--fix-cap", type=int, default=None)
    parser.add_argument("--repo-root", type=Path)
    return parser


def run(args: argparse.Namespace) -> int:
    number = normalize_number(args.number, kind="PR number")
    root = primary_root(args.repo_root)
    cache = Path(
        os.environ.get("MIPSTARRE_CACHE_ROOT", Path.home() / ".cache/mipstarre-dev")
    )
    cap = args.fix_cap
    if cap is None:
        cap = int(os.environ.get("MIPSTARRE_FIX_CAP", str(DEFAULT_FIX_CAP)))
    if cap < 0:
        raise GateFailure("fix cap must be nonnegative")

    client = GitHub(repo_root=root)
    client.probe_authentication()
    require_merge_capability(client)
    review_path = cache / "locks" / f"review-{number}.lock"
    with reserve_runtime_lock(review_path, f"merge review pr={number}") as review_lock:
        pull = client.get_pull(number)
        identity = require_open_mergeable(pull, number)
        expected = GateExpectation(
            branch=identity.branch,
            base=identity.base,
            head_sha=identity.head_sha,
            base_sha=identity.base_sha,
        )
        fix_path = (
            cache
            / "locks"
            / f"fix-{expected.branch.replace('/', '-')}.lock"
        )
        with reserve_runtime_lock(
            fix_path, f"merge fix-reservation pr={number} branch={expected.branch}"
        ) as fix_lock:
            ci_path = cache / "locks" / f"ci-{number}.lock"
            with reserve_runtime_lock(
                ci_path, f"merge ci-reservation pr={number}"
            ) as ci_lock:
                first = evaluate_gate(
                    client,
                    number,
                    expected,
                    root,
                    review_lock,
                    fix_lock,
                    ci_lock,
                    cap,
                    adjudicated=args.adjudicated,
                    require_adjudication_status=not args.adjudicated,
                )
                command = [
                    "pr",
                    "merge",
                    str(number),
                    "--repo",
                    client.repo,
                    "--merge",
                    "--match-head-commit",
                    expected.head_sha,
                ]
                if args.dry_run:
                    prefix = "gate passed; would publish adjudication status and " \
                        if args.adjudicated else "gate passed; would "
                    print(prefix + "run: gh " + " ".join(command))
                    return 0

                if args.adjudicated:
                    if not isinstance(first.review, AdjudicationEvidence):
                        raise GateFailure("adjudication gate returned the wrong evidence")
                    initial_adjudication = first.review

                    def revalidate_adjudication() -> None:
                        current = evaluate_gate(
                            client,
                            number,
                            expected,
                            root,
                            review_lock,
                            fix_lock,
                            ci_lock,
                            cap,
                            adjudicated=True,
                            require_adjudication_status=False,
                        )
                        if (
                            not isinstance(current.review, AdjudicationEvidence)
                            or current.review.digest != initial_adjudication.digest
                            or current.review.source.run_id
                            != initial_adjudication.source.run_id
                            or current.review.source.digest
                            != initial_adjudication.source.digest
                        ):
                            raise GateFailure(
                                "adjudication changed before summary publication"
                            )

                    client.post_status(
                        expected.head_sha,
                        REVIEW_CONTEXT,
                        "success",
                        adjudication_status_description(initial_adjudication),
                        before_mutation=revalidate_adjudication,
                    )

                # The same evaluator runs again as the final operation before
                # the guarded merge, catching evidence, policy, tree, and base races.
                final = evaluate_gate(
                    client,
                    number,
                    expected,
                    root,
                    review_lock,
                    fix_lock,
                    ci_lock,
                    cap,
                    adjudicated=args.adjudicated,
                )
                if first.worktree.resolve() != final.worktree.resolve():
                    raise GateFailure(
                        "feature worktree changed between gate evaluations"
                    )
                review_lock.require_owned()
                fix_lock.require_owned(reject_cancel=True)
                ci_lock.require_owned()
                require_clean_worktree(final.worktree)
                _merged, merge_sha = merge_once(
                    client, number, expected, command
                )
                feature_worktree = final.worktree
    fast_forward_base(root, expected.base)
    cleanup_feature(root, expected.branch, feature_worktree, merge_sha)
    print(f"merged GitHub PR #{number} at {merge_sha}")
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (GateFailure, GitHubError, OSError, ValueError) as exc:
        sys.stderr.write(f"pr_merge.py: merge refused: {exc}\n")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
