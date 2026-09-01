#!/usr/bin/env python3
"""Serialize ownership-sensitive transitions of runtime lock directories."""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import shutil
import socket
import stat
import sys
import uuid
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterator, Sequence


_TOKEN_RE = re.compile(r"^[0-9a-f]{32}$")
_DIGEST_RE = re.compile(r"^[0-9a-f]{64}$")
_OWNER_KEYS = {
    "schema",
    "pid",
    "token",
    "identity",
    "owner",
    "host",
    "created_at",
}
_CANCEL_KEYS = {
    "schema",
    "identity",
    "pid",
    "token",
    "owner_digest",
    "requester",
    "requested_at",
}


class MalformedLock(RuntimeError):
    """A canonical lock exists but does not contain one complete owner record."""


@dataclass(frozen=True)
class LockIdentity:
    """Stable device/inode identity for one directory entry."""

    device: int
    inode: int

    def render(self) -> str:
        return f"{self.device}:{self.inode}"

    @classmethod
    def parse(cls, value: str) -> "LockIdentity":
        match = re.fullmatch(r"([0-9]+):([0-9]+)", value)
        if match is None:
            raise ValueError(f"invalid runtime-lock identity {value!r}")
        return cls(int(match.group(1)), int(match.group(2)))


@dataclass(frozen=True)
class LockClaim:
    """The complete immutable claim used to authorize one lock transition."""

    identity: LockIdentity
    pid: int
    token: str
    owner_digest: str


@dataclass(frozen=True)
class LockRecord:
    """A validated on-disk runtime-lock owner record."""

    identity: LockIdentity
    pid: int
    token: str
    owner: str
    host: str
    created_at: str
    owner_digest: str

    @property
    def claim(self) -> LockClaim:
        return LockClaim(
            identity=self.identity,
            pid=self.pid,
            token=self.token,
            owner_digest=self.owner_digest,
        )


@dataclass(frozen=True)
class TransitionResult:
    """Result of an ownership-sensitive directory transition."""

    state: str
    detail: str = ""
    record: LockRecord | None = None


def new_token() -> str:
    """Return a process-independent random token suitable for a new lock."""
    return uuid.uuid4().hex


def directory_identity(path: Path) -> LockIdentity | None:
    """Return the non-symlink directory identity at *path*, if one exists."""
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return None
    if not stat.S_ISDIR(metadata.st_mode):
        return None
    return LockIdentity(metadata.st_dev, metadata.st_ino)


def transition_path(path: Path) -> Path:
    """Return the persistent sibling mutex file for one canonical lock path."""
    return path.with_name(f".{path.name}.transition")


@contextmanager
def transition_mutex(path: Path) -> Iterator[None]:
    """Hold the stable per-lock transition mutex until the context exits."""
    path.parent.mkdir(parents=True, exist_ok=True)
    mutex = transition_path(path)
    descriptor = os.open(mutex, os.O_CREAT | os.O_RDWR | os.O_CLOEXEC, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _clean_text(value: object, *, field: str, limit: int) -> str:
    if not isinstance(value, str) or not value or len(value) > limit:
        raise MalformedLock(f"owner {field} is missing or invalid")
    if any(ord(character) < 32 or ord(character) == 127 for character in value):
        raise MalformedLock(f"owner {field} contains a control character")
    return value


def _read_regular_text(path: Path, *, limit: int) -> str:
    try:
        metadata = path.lstat()
        if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > limit:
            raise MalformedLock(f"{path.name} is not a bounded regular file")
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise MalformedLock(f"{path.name} is unreadable") from exc


def _canonical_json(payload: dict[str, object]) -> bytes:
    return json.dumps(
        payload,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def _owner_digest(payload: dict[str, object]) -> str:
    return hashlib.sha256(_canonical_json(payload)).hexdigest()


def _read_record(path: Path, identity: LockIdentity) -> LockRecord:
    pid_text = _read_regular_text(path / "pid", limit=64)
    token_text = _read_regular_text(path / "token", limit=128)
    identity_text = _read_regular_text(path / "identity", limit=128)
    owner_text = _read_regular_text(path / "owner", limit=8192)
    if not re.fullmatch(r"[1-9][0-9]*\n?", pid_text):
        raise MalformedLock("pid is missing or malformed")
    token = token_text.removesuffix("\n")
    if not _TOKEN_RE.fullmatch(token):
        raise MalformedLock("token is missing or malformed")
    try:
        recorded_identity = LockIdentity.parse(identity_text.strip())
    except ValueError as exc:
        raise MalformedLock("identity is missing or malformed") from exc
    if recorded_identity != identity:
        raise MalformedLock("recorded identity does not match the lock directory")
    try:
        payload = json.loads(owner_text)
    except json.JSONDecodeError as exc:
        raise MalformedLock("owner metadata is not valid JSON") from exc
    if not isinstance(payload, dict) or set(payload) != _OWNER_KEYS:
        raise MalformedLock("owner metadata has a noncanonical schema")
    pid = int(pid_text.strip())
    owner = _clean_text(payload.get("owner"), field="name", limit=1000)
    host = _clean_text(payload.get("host"), field="host", limit=255)
    created_at = _clean_text(
        payload.get("created_at"), field="creation time", limit=100
    )
    if (
        payload.get("schema") != 1
        or payload.get("pid") != pid
        or payload.get("token") != token
        or payload.get("identity") != identity.render()
    ):
        raise MalformedLock("owner metadata disagrees with the ownership files")
    return LockRecord(
        identity=identity,
        pid=pid,
        token=token,
        owner=owner,
        host=host,
        created_at=created_at,
        owner_digest=_owner_digest(payload),
    )


def _inspect_locked(path: Path) -> TransitionResult:
    identity = directory_identity(path)
    if identity is None:
        if os.path.lexists(path):
            return TransitionResult("unsafe", "canonical path is not a directory")
        return TransitionResult("absent", "canonical directory is absent")
    try:
        record = _read_record(path, identity)
    except MalformedLock as exc:
        return TransitionResult("unsafe", str(exc))
    return TransitionResult("held", record=record)


def inspect_lock(path: Path) -> TransitionResult:
    """Inspect one complete record while holding its transition mutex."""
    with transition_mutex(path):
        return _inspect_locked(path)


def _validate_new_owner(pid: int, token: str, owner: str) -> None:
    if pid <= 0:
        raise ValueError("runtime-lock pid must be positive")
    if not _TOKEN_RE.fullmatch(token):
        raise ValueError("runtime-lock token must be a lowercase UUID4 hex value")
    parsed = uuid.UUID(hex=token)
    if parsed.version != 4 or parsed.hex != token:
        raise ValueError("runtime-lock token must be a lowercase UUID4 hex value")
    _clean_text(owner, field="name", limit=1000)


def _write_record(path: Path, pid: int, token: str, owner: str) -> LockRecord:
    identity = directory_identity(path)
    if identity is None:
        raise RuntimeError("new runtime lock has no directory identity")
    created_at = datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")
    payload: dict[str, object] = {
        "schema": 1,
        "pid": pid,
        "token": token,
        "identity": identity.render(),
        "owner": owner,
        "host": socket.gethostname(),
        "created_at": created_at,
    }
    (path / "pid").write_text(f"{pid}\n", encoding="utf-8")
    (path / "token").write_text(f"{token}\n", encoding="utf-8")
    (path / "identity").write_text(f"{identity.render()}\n", encoding="utf-8")
    (path / "owner").write_bytes(_canonical_json(payload) + b"\n")
    return _read_record(path, identity)


def _pid_is_dead(record: LockRecord) -> bool:
    if record.host != socket.gethostname():
        return False
    try:
        os.kill(record.pid, 0)
    except ProcessLookupError:
        return True
    except (OverflowError, PermissionError, OSError):
        return False
    return False


def _tombstone(path: Path, operation: str) -> Path:
    return path.with_name(
        f"{path.name}.{operation}.{os.getpid()}.{uuid.uuid4().hex}"
    )


def _claim_matches(record: LockRecord, claim: LockClaim) -> bool:
    return record.claim == claim


def _claim_result(
    state: str, detail: str, observed: TransitionResult, claim: LockClaim
) -> TransitionResult:
    if observed.state == "unsafe":
        return observed
    if observed.record is None:
        return TransitionResult("changed", "canonical directory is absent")
    if observed.record.identity != claim.identity:
        return TransitionResult("changed", "canonical directory identity changed")
    if not _claim_matches(observed.record, claim):
        return TransitionResult("not-owned", "complete owner record changed")
    return TransitionResult(state, detail, observed.record)


def acquire_lock(
    path: Path,
    pid: int,
    token: str,
    owner: str,
    *,
    before_mutex: Callable[[], None] | None = None,
) -> TransitionResult:
    """Acquire an absent lock; every complete existing record needs recovery."""
    _validate_new_owner(pid, token, owner)
    if before_mutex is not None:
        before_mutex()
    with transition_mutex(path):
        observed = _inspect_locked(path)
        if observed.state == "unsafe":
            return observed
        if observed.record is not None:
            if _pid_is_dead(observed.record):
                detail = (
                    f"complete owner pid {observed.record.pid} is dead; "
                    "explicit recovery is required because descendants may survive"
                )
            else:
                detail = f"owner pid {observed.record.pid} is not proven dead"
            return TransitionResult("busy", detail, observed.record)
        try:
            path.mkdir(mode=0o700)
            record = _write_record(path, pid, token, owner)
        except (OSError, RuntimeError, MalformedLock) as exc:
            return TransitionResult(
                "unsafe",
                f"new lock owner record is incomplete: {exc}",
            )
        return TransitionResult("acquired", "", record)


def break_stale_lock(
    path: Path,
    expected: LockClaim,
    *,
    before_mutex: Callable[[], None] | None = None,
) -> TransitionResult:
    """Delete exactly one observed lock whose complete owner is proven dead."""
    if before_mutex is not None:
        before_mutex()
    with transition_mutex(path):
        observed = _inspect_locked(path)
        checked = _claim_result("held", "", observed, expected)
        if checked.state != "held" or checked.record is None:
            return checked
        if not _pid_is_dead(checked.record):
            return TransitionResult(
                "live",
                f"owner pid {checked.record.pid} is not proven dead",
                checked.record,
            )
        tombstone = _tombstone(path, "stale")
        path.rename(tombstone)
        if directory_identity(tombstone) != expected.identity:
            raise RuntimeError("renamed stale lock changed identity")
        shutil.rmtree(tombstone)
        return TransitionResult(
            "broken", f"removed stale owner pid {checked.record.pid}"
        )


def _read_cancel(path: Path, record: LockRecord) -> bool:
    cancel = path / "cancel"
    if not os.path.lexists(cancel):
        return False
    text = _read_regular_text(cancel, limit=8192)
    try:
        payload = json.loads(text)
    except json.JSONDecodeError as exc:
        raise MalformedLock("cancellation record is not valid JSON") from exc
    if not isinstance(payload, dict) or set(payload) != _CANCEL_KEYS:
        raise MalformedLock("cancellation record has a noncanonical schema")
    _clean_text(payload.get("requester"), field="cancellation requester", limit=1000)
    _clean_text(
        payload.get("requested_at"), field="cancellation time", limit=100
    )
    claim = record.claim
    if (
        payload.get("schema") != 1
        or payload.get("identity") != claim.identity.render()
        or payload.get("pid") != claim.pid
        or payload.get("token") != claim.token
        or payload.get("owner_digest") != claim.owner_digest
    ):
        raise MalformedLock("cancellation record targets a different owner")
    return True


def validate_owned_lock(
    path: Path,
    expected: LockClaim,
    *,
    reject_cancel: bool = False,
    before_mutex: Callable[[], None] | None = None,
) -> TransitionResult:
    """Validate an exact complete owner claim under the transition mutex."""
    if before_mutex is not None:
        before_mutex()
    with transition_mutex(path):
        observed = _inspect_locked(path)
        checked = _claim_result("owned", "", observed, expected)
        if checked.state != "owned" or checked.record is None:
            return checked
        if reject_cancel:
            try:
                if _read_cancel(path, checked.record):
                    return TransitionResult(
                        "cancelled", "owned lock has a cancellation request"
                    )
            except MalformedLock as exc:
                return TransitionResult("unsafe", str(exc))
        return checked


def request_cancellation(
    path: Path,
    expected: LockClaim,
    requester: str,
    *,
    required_owner_prefix: str | None = None,
    before_mutex: Callable[[], None] | None = None,
) -> TransitionResult:
    """Request cancellation only from the exact complete owner observed earlier."""
    _clean_text(requester, field="cancellation requester", limit=1000)
    if required_owner_prefix is not None:
        _clean_text(
            required_owner_prefix,
            field="required owner prefix",
            limit=1000,
        )
    if before_mutex is not None:
        before_mutex()
    with transition_mutex(path):
        observed = _inspect_locked(path)
        checked = _claim_result("held", "", observed, expected)
        if checked.state != "held" or checked.record is None:
            return checked
        if (
            required_owner_prefix is not None
            and not checked.record.owner.startswith(required_owner_prefix)
        ):
            return TransitionResult(
                "not-cancellable",
                "complete owner is outside the permitted cancellation class",
                checked.record,
            )
        try:
            if _read_cancel(path, checked.record):
                return TransitionResult(
                    "cancel-requested", "cancellation was already requested"
                )
        except MalformedLock as exc:
            return TransitionResult("unsafe", str(exc))
        payload: dict[str, object] = {
            "schema": 1,
            "identity": expected.identity.render(),
            "pid": expected.pid,
            "token": expected.token,
            "owner_digest": expected.owner_digest,
            "requester": requester,
            "requested_at": datetime.now(timezone.utc)
            .isoformat()
            .replace("+00:00", "Z"),
        }
        temporary = path / f".cancel.tmp.{os.getpid()}.{uuid.uuid4().hex}"
        try:
            temporary.write_bytes(_canonical_json(payload) + b"\n")
            os.replace(temporary, path / "cancel")
            if directory_identity(path) != expected.identity:
                raise RuntimeError("cancelled lock changed directory identity")
            if _read_record(path, expected.identity).claim != expected:
                raise RuntimeError("cancelled lock changed complete ownership")
            if not _read_cancel(path, checked.record):
                raise RuntimeError("cancellation record could not be verified")
        finally:
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass
        return TransitionResult("cancel-requested")


def release_owned_lock(
    path: Path,
    expected: LockClaim,
    *,
    before_mutex: Callable[[], None] | None = None,
) -> TransitionResult:
    """Delete the canonical directory only while its complete claim is ours."""
    if before_mutex is not None:
        before_mutex()
    with transition_mutex(path):
        observed = _inspect_locked(path)
        checked = _claim_result("held", "", observed, expected)
        if checked.state != "held":
            return checked
        tombstone = _tombstone(path, "release")
        path.rename(tombstone)
        if directory_identity(tombstone) != expected.identity:
            raise RuntimeError("renamed owned lock changed identity")
        shutil.rmtree(tombstone)
        return TransitionResult("released")


def _add_claim_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("identity")
    parser.add_argument("pid", type=int)
    parser.add_argument("token")
    parser.add_argument("owner_digest")


def _claim_from_args(args: argparse.Namespace) -> LockClaim:
    if args.pid <= 0:
        raise ValueError("invalid runtime-lock pid")
    if not _TOKEN_RE.fullmatch(args.token):
        raise ValueError("invalid runtime-lock token")
    if not _DIGEST_RE.fullmatch(args.owner_digest):
        raise ValueError("invalid runtime-lock owner digest")
    return LockClaim(
        LockIdentity.parse(args.identity),
        args.pid,
        args.token,
        args.owner_digest,
    )


def _render_result(result: TransitionResult) -> str:
    record = result.record
    detail = result.detail.replace("|", "/").replace("\n", " ")
    if record is None:
        return f"{result.state}|-|-|-|-|{detail}"
    claim = record.claim
    return "|".join(
        [
            result.state,
            claim.identity.render(),
            str(claim.pid),
            claim.token,
            claim.owner_digest,
            detail,
        ]
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("new-token")
    identity = subparsers.add_parser("identity")
    identity.add_argument("path", type=Path)
    inspect = subparsers.add_parser("inspect")
    inspect.add_argument("path", type=Path)
    acquire = subparsers.add_parser("acquire")
    acquire.add_argument("path", type=Path)
    acquire.add_argument("pid", type=int)
    acquire.add_argument("token")
    acquire.add_argument("owner")
    stale = subparsers.add_parser("break-stale")
    stale.add_argument("path", type=Path)
    _add_claim_arguments(stale)
    release = subparsers.add_parser("release-owned")
    release.add_argument("path", type=Path)
    _add_claim_arguments(release)
    validate = subparsers.add_parser("validate-owned")
    validate.add_argument("path", type=Path)
    _add_claim_arguments(validate)
    validate.add_argument("--reject-cancel", action="store_true")
    cancel = subparsers.add_parser("request-cancel")
    cancel.add_argument("path", type=Path)
    _add_claim_arguments(cancel)
    cancel.add_argument("requester")
    cancel.add_argument("--owner-prefix")
    return parser


def run(args: argparse.Namespace) -> int:
    if args.command == "new-token":
        print(new_token())
        return 0
    if args.command == "identity":
        identity = directory_identity(args.path)
        if identity is None:
            return 1
        print(identity.render())
        return 0
    if args.command == "inspect":
        result = inspect_lock(args.path)
    elif args.command == "acquire":
        result = acquire_lock(args.path, args.pid, args.token, args.owner)
    else:
        claim = _claim_from_args(args)
        if args.command == "break-stale":
            result = break_stale_lock(args.path, claim)
        elif args.command == "release-owned":
            result = release_owned_lock(args.path, claim)
        elif args.command == "validate-owned":
            result = validate_owned_lock(
                args.path, claim, reject_cancel=args.reject_cancel
            )
        else:
            result = request_cancellation(
                args.path,
                claim,
                args.requester,
                required_owner_prefix=args.owner_prefix,
            )
    print(_render_result(result))
    if result.state in {
        "acquired",
        "broken",
        "cancel-requested",
        "held",
        "owned",
        "released",
    }:
        return 0
    if result.state == "unsafe":
        return 2
    return 1


def main(argv: Sequence[str] | None = None) -> int:
    try:
        return run(build_parser().parse_args(argv))
    except (MalformedLock, OSError, RuntimeError, ValueError) as exc:
        print(f"runtime_lock.py: error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
