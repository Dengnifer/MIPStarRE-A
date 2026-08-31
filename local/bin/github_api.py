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
REVIEW_CONTEXT = "local-review/summary"
AUTO_FIX_PREFIXES = ("[codex-auto-fix]", "[codex-review-fix]")
AUTO_FIX_LABEL = "auto-fix-codex"
ADJUDICATION_LABEL = "adjudicated"

_CI_MARKER_RE = re.compile(
    r"<!-- mipstarre:ci-manifest pr=(\d+) "
    r"head=((?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})) run=([^<>\s]+) -->"
)
_REVIEW_MARKER_RE = re.compile(
    r"<!-- mipstarre:review-ledger pr=(\d+) "
    r"head=((?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})) run=([^<>\s]+) "
    r"event=(COMMENT|REQUEST_CHANGES) fallback=(none|COMMENT) -->"
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


def _validated_marker(marker: str, body: str) -> None:
    if not _MARKER_RE.fullmatch(marker):
        raise GitHubError(f"invalid or missing idempotency marker: {marker!r}")
    if body.count(marker) != 1:
        raise GitHubError("idempotent publication body must contain its marker exactly once")


def _marker_value(marker: str, key: str) -> str | None:
    match = re.search(rf"(?:^| ){re.escape(key)}=([^<>\s]+)(?= | -->)", marker)
    return match.group(1) if match else None


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

    def probe_authentication(self) -> dict[str, Any]:
        try:
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
        candidates.sort(
            key=lambda row: (
                str(row.get(timestamp) or row.get("created_at") or ""),
                int(row.get("id") or 0),
            ),
            reverse=True,
        )
        return candidates[0]

    def ci_manifest(self, number: int, sha: str) -> tuple[dict[str, Any], dict[str, Any]]:
        sha = normalize_sha(sha)
        matches: list[dict[str, Any]] = []
        for row in self.comments(number):
            body = str(row.get("body") or "")
            markers = _CI_MARKER_RE.findall(body)
            if not any(int(pr) == number and head.lower() == sha for pr, head, _ in markers):
                continue
            matches.append(row)
        row = self._latest(matches, "created_at")
        body = str(row.get("body") or "")
        if body.count("<!-- mipstarre:ci-manifest ") != 1:
            raise GitHubError("latest exact-head CI manifest has ambiguous markers")
        fenced = re.search(r"```json\s*\n(.*?)\n```", body, re.DOTALL)
        if not fenced:
            raise GitHubError("latest exact-head CI comment has no JSON manifest fence")
        try:
            manifest = json.loads(fenced.group(1))
        except json.JSONDecodeError as exc:
            raise GitHubError(f"latest exact-head CI manifest is invalid JSON: {exc}") from exc
        if not isinstance(manifest, dict):
            raise GitHubError("latest exact-head CI manifest is not an object")
        if str(manifest.get("head_sha") or "").lower() != sha:
            raise GitHubError("latest CI manifest does not record the exact requested head")
        if str(manifest.get("pr") or "") != str(number) or manifest.get("partial"):
            raise GitHubError("latest CI manifest has the wrong PR or is partial")
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
        outcomes = {"success", "failure", "error", "skipped"}
        if any(str(step.get("outcome") or "") not in outcomes for step in steps):
            raise GitHubError("latest CI manifest contains an invalid or missing step outcome")
        return row, manifest

    def _review_ledger_rows(self, number: int) -> list[dict[str, Any]]:
        """Return validated marker-bound review ledgers for one PR."""
        matches: list[dict[str, Any]] = []
        for row in self.reviews(number):
            body = str(row.get("body") or "")
            if "<!-- mipstarre:review-ledger " not in body:
                continue
            if body.count("<!-- mipstarre:review-ledger ") != 1:
                raise GitHubError("review ledger has ambiguous markers")
            marker = _REVIEW_MARKER_RE.search(body)
            if marker is None:
                raise GitHubError("review ledger has a malformed marker")
            marker_pr = int(marker.group(1))
            marker_sha = marker.group(2).lower()
            if marker_pr != number:
                raise GitHubError("review ledger marker names a different PR")
            commit_sha = normalize_sha(
                str(row.get("commit_id") or ""), kind="review-ledger commit SHA"
            )
            if commit_sha != marker_sha:
                raise GitHubError("review ledger marker is bound to a different commit")
            event, fallback = marker.group(4), marker.group(5)
            state = str(row.get("state") or "").upper()
            expected_states = (
                {"COMMENTED"} if event == "COMMENT" else {"CHANGES_REQUESTED"}
            )
            if event == "REQUEST_CHANGES" and fallback == "COMMENT":
                expected_states.add("COMMENTED")
            if event == "COMMENT" and fallback != "none":
                raise GitHubError(
                    "a clean review-ledger marker cannot declare a fallback"
                )
            if state not in expected_states:
                raise GitHubError(
                    f"review ledger state {state or 'missing'} does not match "
                    f"event {event}"
                )
            matches.append(row)
        return matches

    def latest_review_ledger(self, number: int) -> dict[str, Any] | None:
        """Return the latest validated local-review ledger, if one exists."""
        matches = self._review_ledger_rows(number)
        return self._latest(matches, "submitted_at") if matches else None

    def review_ledger(self, number: int, sha: str) -> dict[str, Any]:
        sha = normalize_sha(sha)
        matches = [
            row
            for row in self._review_ledger_rows(number)
            if str(row.get("commit_id") or "").lower() == sha
        ]
        row = self._latest(matches, "submitted_at")
        return row

    def post_status(self, sha: str, context: str, state: str, description: str) -> None:
        sha = normalize_sha(sha)
        context = context.strip()
        if not context or any(ord(ch) < 32 for ch in context):
            raise GitHubError("commit status context must be nonempty and printable")
        if state not in {"pending", "success", "failure", "error"}:
            raise GitHubError(f"invalid commit status state {state!r}")
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
        rendered_description = description[: 140 - len(suffix)].rstrip() + suffix

        def matches(row: dict[str, Any]) -> bool:
            row_sha = str(row.get("sha") or "")
            return (
                _SHA_RE.fullmatch(row_sha) is not None
                and row_sha.lower() == sha
                and str(row.get("context") or "").casefold() == context.casefold()
                and str(row.get("state") or "").casefold() == state
                and str(row.get("description") or "") == rendered_description
            )

        def lookup() -> dict[str, Any] | None:
            for row in self.statuses(sha):
                if matches(row):
                    return row
            return None

        def mutate() -> dict[str, Any]:
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

    def _idempotent_mutation(
        self,
        *,
        lookup: Callable[[], T | None],
        mutate: Callable[[], T],
    ) -> T:
        found = lookup()
        if found is not None:
            return found
        last: GitHubError | None = None
        for attempt in range(self.retries + 1):
            try:
                return mutate()
            except GitHubError as exc:
                last = exc
                if not exc.transient:
                    raise
                found = lookup()
                if found is not None:
                    return found
                if attempt >= self.retries:
                    break
                time.sleep(self.retry_delay * (2**attempt))
        raise last or GitHubError("idempotent mutation failed")

    def comment_once(self, number: int, body: str, marker: str) -> dict[str, Any]:
        _validated_marker(marker, body)

        def lookup() -> dict[str, Any] | None:
            for row in self.comments(number):
                adopted_body = str(row.get("body") or "")
                if marker not in adopted_body:
                    continue
                if adopted_body != body:
                    raise GitHubError(
                        "comment marker collision: authoritative body differs from "
                        "the requested publication"
                    )
                return row
            return None

        def mutate() -> dict[str, Any]:
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
    ) -> tuple[dict[str, Any], str]:
        commit_id = normalize_sha(commit_id, kind="review commit SHA")
        _validated_marker(marker, body)
        if event not in {"COMMENT", "REQUEST_CHANGES"}:
            raise GitHubError(f"invalid review event {event!r}")
        if _marker_value(marker, "event") != event:
            raise GitHubError("review marker must record the requested event exactly")
        fallback = _marker_value(marker, "fallback")
        if fallback not in {"none", "COMMENT"}:
            raise GitHubError("review marker must record fallback=none or fallback=COMMENT")
        if event == "COMMENT" and fallback != "none":
            raise GitHubError("a COMMENT review cannot declare an event fallback")
        if marker.count(" event=") != 1 or marker.count(" fallback=") != 1:
            raise GitHubError("review marker must record event and fallback exactly once")

        def lookup() -> dict[str, Any] | None:
            for row in self.reviews(number):
                adopted_body = str(row.get("body") or "")
                if marker not in adopted_body:
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
                state = str(row.get("state") or "").upper()
                allowed = {"COMMENTED"} if event == "COMMENT" else {"CHANGES_REQUESTED"}
                if event == "REQUEST_CHANGES" and fallback == "COMMENT":
                    allowed.add("COMMENTED")
                if state not in allowed:
                    raise GitHubError(
                        f"adopted review has state {state or 'missing'}, not an "
                        f"allowed result for {event}"
                    )
                return row
            return None

        used_event = event

        def mutate() -> dict[str, Any]:
            nonlocal used_event
            try:
                payload = self.api(
                    f"/repos/{self.repo}/pulls/{number}/reviews",
                    method="POST",
                    data={"body": body, "event": used_event, "commit_id": commit_id},
                    retry=False,
                )
            except GitHubError as exc:
                rejection = f"{exc}\n{exc.stdout}".casefold()
                self_review = any(
                    phrase in rejection
                    for phrase in (
                        "cannot request changes on your own pull request",
                        "can not request changes on your own pull request",
                        "pull request author cannot request changes",
                    )
                )
                if (
                    used_event == "REQUEST_CHANGES"
                    and fallback == "COMMENT"
                    and exc.status == 422
                    and self_review
                ):
                    used_event = "COMMENT"
                    payload = self.api(
                        f"/repos/{self.repo}/pulls/{number}/reviews",
                        method="POST",
                        data={"body": body, "event": used_event, "commit_id": commit_id},
                        retry=False,
                    )
                else:
                    raise
            if not isinstance(payload, dict):
                raise GitHubError("review creation returned a non-object response")
            return payload

        row = self._idempotent_mutation(lookup=lookup, mutate=mutate)
        if str(row.get("commit_id") or "").lower() != commit_id:
            raise GitHubError("review publication returned a different commit binding")
        if str(row.get("body") or "") != body:
            raise GitHubError("review publication returned a different authoritative body")
        adopted_state = str(row.get("state") or "").upper()
        if adopted_state == "COMMENTED":
            used_event = "COMMENT"
        elif adopted_state == "CHANGES_REQUESTED":
            used_event = "REQUEST_CHANGES"
        else:
            raise GitHubError(
                f"review publication returned unexpected state {adopted_state or 'missing'}"
            )
        return row, used_event


def pull_head(pull: dict[str, Any]) -> tuple[str, str, str]:
    try:
        branch = str(pull["head"]["ref"])
        sha = str(pull["head"]["sha"])
        base = str(pull["base"]["ref"])
    except (KeyError, TypeError) as exc:
        raise GitHubError("pull request response lacks base/head ref and SHA") from exc
    if not branch or not base:
        raise GitHubError("pull request response contains invalid base/head data")
    return branch, base, normalize_sha(sha, kind="pull-request head SHA")


def fix_iteration_count(commits: Sequence[dict[str, Any]]) -> int:
    count = 0
    for row in commits:
        message = str((row.get("commit") or {}).get("message") or "")
        subject = message.splitlines()[0] if message else ""
        if subject.startswith(AUTO_FIX_PREFIXES):
            count += 1
    return count


def require_ci_success(client: GitHub, sha: str) -> None:
    sha = normalize_sha(sha)
    latest = client.latest_statuses(sha)
    failures = []
    for context in CANONICAL_CI_CONTEXTS:
        state = str(
            (latest.get(context.casefold()) or {}).get("state") or "missing"
        ).casefold()
        if state != "success":
            failures.append(f"{context}={state}")
    if failures:
        raise GitHubError(
            f"exact-head CI is not green for {sha}: " + ", ".join(failures)
        )


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
    require_ci.add_argument("sha")

    post_status = sub.add_parser("post-status")
    post_status.add_argument("sha")
    post_status.add_argument("context")
    post_status.add_argument("state", choices=("pending", "success", "failure", "error"))
    post_status.add_argument("description")

    comment = sub.add_parser("comment-once")
    comment.add_argument("number")
    comment.add_argument("body_file")
    comment.add_argument("marker")

    review = sub.add_parser("review-once")
    review.add_argument("number")
    review.add_argument("commit_id")
    review.add_argument("body_file")
    review.add_argument("event", choices=("COMMENT", "REQUEST_CHANGES"))
    review.add_argument("marker")

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

    review_ledger = sub.add_parser("review-ledger")
    review_ledger.add_argument("number")
    review_ledger.add_argument("sha")

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
    if not args.no_probe:
        client.probe_authentication()
    if args.command == "probe":
        print(f"authenticated repository: {client.repo}")
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
        require_ci_success(client, args.sha)
        print(args.sha)
    elif args.command == "post-status":
        client.post_status(args.sha, args.context, args.state, args.description)
    elif args.command == "comment-once":
        row = client.comment_once(
            normalize_number(args.number), _read_body(args.body_file), args.marker
        )
        print(json.dumps(row))
    elif args.command == "review-once":
        row, event = client.review_once(
            normalize_number(args.number),
            args.commit_id,
            _read_body(args.body_file),
            args.event,
            args.marker,
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
        _, manifest = client.ci_manifest(normalize_number(args.number), args.sha)
        print(json.dumps(manifest, ensure_ascii=False))
    elif args.command == "review-ledger":
        row = client.review_ledger(normalize_number(args.number), args.sha)
        print(str(row.get("body") or ""))
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
