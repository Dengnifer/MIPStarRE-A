#!/usr/bin/env python3
"""Check that this machine can run the project before anything is started.

One line per check, each PASS / WARN / FAIL with the exact command that fixes
it.  Nothing here installs, downloads or mutates anything, and no secret is
printed: proxy variables are reported by name only, and the functional key
probe is delegated to ``local/bin/session/probe-key.sh``.  The check list
follows the migration incidents recorded in the kit's bootstrap evidence:
binary discovery, API authentication and SSH transport are three separate
prerequisites, and ``elan show`` is never used because a stale toolchain
directory makes it error.

Usage:
    python3 scripts/preflight.py [--root .] [--json] [--no-probe]

Exit code 0 when no check FAILed, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

PASS, WARN, FAIL = "PASS", "WARN", "FAIL"

#: Free space on the repository filesystem, in GiB.  A Mathlib build plus its
#: cache is several GiB and the origin project ran a machine to 97 % full with
#: parallel copies of `.lake/packages`, so the floor is generous.
DISK_FAIL_GIB = 10.0
DISK_WARN_GIB = 25.0

#: Below these a full Mathlib build is painful but not impossible.
CORES_WARN = 4
RAM_WARN_GIB = 8.0

#: Proxy variables are reported by NAME only — their values routinely carry
#: credentials.
PROXY_VARS = (
    "HTTP_PROXY", "HTTPS_PROXY", "ALL_PROXY", "NO_PROXY", "FTP_PROXY",
    "http_proxy", "https_proxy", "all_proxy", "no_proxy", "ftp_proxy",
)

PLACEHOLDER_SLUG = "OWNER/REPO"


@dataclass
class Check:
    """One line of the report."""

    ident: str
    title: str
    status: str
    detail: str = ""
    fix: str = ""

    def as_dict(self) -> dict:
        return {"id": self.ident, "title": self.title, "status": self.status,
                "detail": self.detail, "fix": self.fix}


@dataclass
class Env:
    """Everything the checks read from the outside world."""

    root: Path
    config: dict = field(default_factory=dict)
    probe: bool = True


# ── small helpers ───────────────────────────────────────────────────────────


def run(cmd: list[str], timeout: float = 30.0, cwd: Path | None = None,
        env: dict | None = None) -> tuple[int, str, str]:
    """Run *cmd*; never raise.  Returns (rc, stdout, stderr); rc 127 = missing."""
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout,
            cwd=str(cwd) if cwd else None,
            env={**os.environ, **(env or {})},
        )
    except FileNotFoundError:
        return 127, "", f"{cmd[0]}: not found"
    except subprocess.TimeoutExpired:
        return 124, "", f"{cmd[0]}: timed out after {timeout:.0f}s"
    except OSError as exc:  # permission denied on a non-executable stub, …
        return 126, "", f"{cmd[0]}: {exc}"
    return proc.returncode, proc.stdout, proc.stderr


def elan_home() -> Path:
    return Path(os.environ.get("ELAN_HOME") or (Path(os.path.expanduser("~")) / ".elan"))


def which_where(name: str) -> tuple[str | None, bool]:
    """(path, found only outside PATH).

    The origin machine had `gh` installed under the user's own ``~/.local/bin``
    while PATH did not carry it, and `elan`/`lake` live in ``~/.elan/bin``,
    which an interactive profile adds but a non-interactive shell — the one a
    script runs in — does not.  Both are "installed but unusable", which is a
    different report from "missing".
    """
    found = shutil.which(name)
    if found:
        return found, False
    home = Path(os.path.expanduser("~"))
    for directory in (home / ".local" / "bin", elan_home() / "bin"):
        candidate = directory / name
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate), True
    return None, False


def which(name: str) -> str | None:
    return which_where(name)[0]


def off_path_fix(path: str) -> str:
    directory = str(Path(path).parent)
    return (f"{path} exists but PATH does not carry it, so scripts and non-interactive "
            f"shells will not find it. Add it: put   export PATH=\"{directory}:$PATH\"   "
            "in ~/.profile (or ~/.bashrc), and start the session's shell again")


def binary_check(ident: str, title: str, name: str, install_fix: str,
                 version_args: tuple[str, ...] = ("--version",),
                 missing_is_fatal: bool = True) -> Check:
    """One external tool: is it there, is it usable, does it answer?"""
    path, off_path = which_where(name)
    if not path:
        return Check(ident, title, FAIL if missing_is_fatal else WARN, "not found",
                     install_fix)
    if off_path:
        return Check(ident, title, WARN, f"{path} (not on PATH)", off_path_fix(path))
    if not version_args:
        return Check(ident, title, PASS, path)
    rc, out, err = run([path, *version_args], timeout=30)
    if rc == 0:
        return Check(ident, title, PASS, first_line(out or err) or path)
    return Check(ident, title, WARN, first_line(err or out) or f"exit {rc}",
                 f"`{name} {' '.join(version_args)}` did not answer; reinstall it")


def first_line(text: str, limit: int = 160) -> str:
    line = (text or "").strip().splitlines()
    out = line[0].strip() if line else ""
    return out[:limit]


def gib(num_bytes: float) -> float:
    return num_bytes / (1024 ** 3)


def load_config(root: Path) -> dict:
    """Read ``local/project.json`` — through the shared loader when it exists."""
    loader = root / "scripts" / "project_config.py"
    if loader.is_file():
        sys.path.insert(0, str(root / "scripts"))
        try:
            import project_config  # type: ignore  # noqa: PLC0415

            return project_config.load(root) or {}
        except Exception:  # pragma: no cover - the raw file is the fallback
            pass
    path = root / "local" / "project.json"
    if path.is_file():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            return {}
    return {}


def cfg_get(config: dict, dotted: str, default=None):
    node = config
    for part in dotted.split("."):
        if not isinstance(node, dict) or part not in node:
            return default
        node = node[part]
    return node if node not in (None, "") else default


# ── the checks ──────────────────────────────────────────────────────────────


def check_python(env: Env) -> Check:
    have = ".".join(str(n) for n in sys.version_info[:3])
    if sys.version_info >= (3, 10):
        return Check("python", "Python 3.10 or newer", PASS, f"python3 {have}")
    return Check(
        "python", "Python 3.10 or newer", FAIL, f"python3 {have}",
        "install Python 3.10 or newer and make sure `python3 --version` shows it; "
        "the tools here use only the standard library, so nothing else is needed",
    )


def check_git(env: Env) -> Check:
    path = which("git")
    if not path:
        return Check("git", "git", FAIL, "not found",
                     "install git (Debian/Ubuntu: sudo apt install git; macOS: xcode-select --install)")
    rc, out, _ = run([path, "--version"], timeout=15)
    return Check("git", "git", PASS if rc == 0 else FAIL, first_line(out) or path,
                 "" if rc == 0 else "reinstall git; `git --version` must work")


def check_git_identity(env: Env) -> Check:
    path = which("git")
    if not path:
        return Check("git-identity", "git commit identity", WARN, "git is missing", "")
    name = run([path, "config", "--get", "user.name"], cwd=env.root)[1].strip()
    mail = run([path, "config", "--get", "user.email"], cwd=env.root)[1].strip()
    if name and mail:
        return Check("git-identity", "git commit identity", PASS, "name and e-mail are set")
    return Check(
        "git-identity", "git commit identity", WARN,
        "user.name or user.email is unset, so the first commit of a new project would fail",
        'run: git config --global user.name "Your Name" '
        'and git config --global user.email "you@example.com"',
    )


def check_tmux(env: Env) -> Check:
    return binary_check(
        "tmux", "tmux", "tmux",
        "install tmux (Debian/Ubuntu: sudo apt install tmux; macOS: brew install tmux); "
        "the long-running main session lives in a tmux window",
        version_args=("-V",),
    )


def toolchain_name(root: Path) -> str:
    path = root / "lean-toolchain"
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return ""


def check_elan(env: Env) -> Check:
    return binary_check(
        "elan", "elan (Lean toolchain manager)", "elan",
        "install elan by hand from https://github.com/leanprover/elan/releases — "
        "download the archive for your platform, check it, run its installer, "
        "then open a new shell so its bin directory is on PATH. Nothing here pipes "
        "an installer into a shell for you",
    )


def check_toolchain(env: Env) -> Check:
    """Is the pinned toolchain installed?

    Deliberately not `elan show`: a stale ``~/.elan/toolchains/stable`` entry
    makes that command error out on a perfectly working installation.
    """
    want = toolchain_name(env.root)
    if not want:
        return Check("toolchain", "pinned Lean toolchain", WARN,
                     "no lean-toolchain file in the repository root",
                     "run this from the repository root, or restore lean-toolchain")
    elan = which("elan")
    installed: list[str] = []
    if elan:
        rc, out, _ = run([elan, "toolchain", "list"], timeout=30)
        if rc == 0:
            installed = [line.split(" ")[0].strip() for line in out.splitlines() if line.strip()]
    home = elan_home()
    dir_name = want.replace("/", "--").replace(":", "---")
    on_disk = (home / "toolchains" / dir_name).is_dir()
    if want in installed or on_disk:
        return Check("toolchain", "pinned Lean toolchain", PASS, want)
    return Check(
        "toolchain", "pinned Lean toolchain", WARN,
        f"{want} is not installed yet",
        f"run: elan toolchain install {want} "
        "(a few hundred megabytes; the first lake command would otherwise do it mid-build)",
    )


def check_lake(env: Env) -> Check:
    # No `--version`: on a fresh machine that call makes elan install the
    # pinned toolchain, which is a few hundred megabytes nobody asked for.
    return binary_check(
        "lake", "lake (Lean build tool)", "lake",
        "install elan; it provides lake, and a new shell picks it up from its bin directory",
        version_args=(),
    )


def check_mathlib_cache(env: Env) -> Check:
    """Can the Mathlib build cache be fetched?  The fetch itself is NOT run."""
    if not which("lake"):
        return Check("mathlib-cache", "Mathlib build cache", WARN, "lake is missing",
                     "install elan first; then run `lake exe cache get` in the repository root")
    manifest = env.root / "lake-manifest.json"
    if not manifest.is_file():
        return Check("mathlib-cache", "Mathlib build cache", WARN,
                     "no lake-manifest.json in the repository root",
                     "run this from the repository root")
    if (env.root / ".lake" / "packages" / "mathlib").is_dir():
        return Check("mathlib-cache", "Mathlib build cache", PASS,
                     "Mathlib package present; `lake exe cache get` keeps it warm")
    return Check(
        "mathlib-cache", "Mathlib build cache", WARN,
        "Mathlib is not unpacked yet (.lake/packages/mathlib is missing)",
        "run: lake exe cache get   (in the repository root, before the first build; "
        "this check never runs it for you). Never run `lake update`",
    )


def check_disk(env: Env) -> Check:
    try:
        free = gib(shutil.disk_usage(env.root).free)
    except OSError as exc:
        return Check("disk", "free disk space", WARN, str(exc), "")
    detail = f"{free:.1f} GiB free where the repository lives"
    fix = ("free space, or point paths.cache_root in local/project.json at a filesystem "
           "with more room; a Mathlib build plus its cache needs several GiB per checkout")
    if free < DISK_FAIL_GIB:
        return Check("disk", "free disk space", FAIL, detail, fix)
    if free < DISK_WARN_GIB:
        return Check("disk", "free disk space", WARN, detail, fix)
    return Check("disk", "free disk space", PASS, detail)


def check_cache_root(env: Env) -> Check:
    raw = cfg_get(env.config, "paths.cache_root", "~/.cache/paperlib-dev")
    path = Path(os.path.expanduser(raw))
    probe = path
    while not probe.exists() and probe != probe.parent:
        probe = probe.parent
    if os.access(probe, os.W_OK):
        state = "exists" if path.exists() else "will be created on first use"
        return Check("cache-root", "runtime state directory", PASS, f"{raw} ({state})")
    return Check(
        "cache-root", "runtime state directory", FAIL,
        f"{raw} is not writable",
        f"run: mkdir -p {raw}   — and if a session sandbox is denying it, allow writes "
        "to that directory; the locks and the state files live there, never in the repository",
    )


def read_ram_gib() -> float | None:
    meminfo = Path("/proc/meminfo")
    if meminfo.is_file():
        try:
            for line in meminfo.read_text(encoding="utf-8").splitlines():
                if line.startswith("MemTotal:"):
                    return float(line.split()[1]) / (1024 ** 2)
        except (OSError, ValueError, IndexError):
            return None
    rc, out, _ = run(["sysctl", "-n", "hw.memsize"], timeout=10)
    if rc == 0 and out.strip().isdigit():
        return gib(float(out.strip()))
    return None


def check_machine(env: Env) -> Check:
    cores = os.cpu_count() or 0
    ram = read_ram_gib()
    ram_text = f"{ram:.1f} GiB RAM" if ram else "RAM unknown"
    detail = f"{cores} cores, {ram_text}"
    if cores and cores < CORES_WARN or (ram is not None and ram < RAM_WARN_GIB):
        return Check("machine", "cores and memory", WARN, detail,
                     "a full Mathlib build on this machine will be slow; expect hours, "
                     "and keep only one full build running at a time")
    return Check("machine", "cores and memory", PASS, detail)


def check_latex(env: Env) -> Check:
    latexmk = which("latexmk")
    engine = which("xelatex")
    if latexmk and engine:
        return Check("latex", "LaTeX (latexmk + xelatex)", PASS, latexmk)
    missing = ", ".join(n for n, p in (("latexmk", latexmk), ("xelatex", engine)) if not p)
    return Check(
        "latex", "LaTeX (latexmk + xelatex)", WARN, f"missing: {missing}",
        "install a TeX distribution with latexmk and xelatex "
        "(Debian/Ubuntu: sudo apt install texlive-xetex texlive-science latexmk; "
        "macOS: install MacTeX) — needed from the blueprint stage on, not before",
    )


def pinned_texra_version(root: Path) -> tuple[str, str]:
    """(version, install command) as pinned in .github/allowed-tools.json."""
    path = root / ".github" / "allowed-tools.json"
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return "", ""
    match = re.search(r"pip install ([^\"',)]*texra-blueprint@([^\s\"',)]+))", text)
    if not match:
        return "", ""
    return match.group(2), "pip install " + match.group(1)


def check_blueprint_tools(env: Env) -> Check:
    leanblueprint = which("leanblueprint")
    rc, _, _ = run([sys.executable, "-c", "import plastex"], timeout=30)
    plastex = rc == 0
    _, install = pinned_texra_version(env.root)
    fix = install or "pip install leanblueprint plastex"
    if leanblueprint and plastex:
        return Check("blueprint-tools", "plastex + leanblueprint", PASS, leanblueprint)
    missing = ", ".join(n for n, ok in (("leanblueprint", bool(leanblueprint)),
                                        ("plastex", plastex)) if not ok)
    return Check("blueprint-tools", "plastex + leanblueprint", WARN, f"missing: {missing}",
                 f"run: {fix}   — needed from the blueprint stage on")


def installed_texra_version(binary: str) -> str:
    rc, out, err = run([binary, "--version"], timeout=20)
    text = out or err
    match = re.search(r"\d+\.\d+(?:\.\d+)?", text)
    if rc == 0 and match:
        return match.group(0)
    rc, out, _ = run([sys.executable, "-m", "pip", "show", "texra-blueprint"], timeout=40)
    if rc == 0:
        for line in out.splitlines():
            if line.lower().startswith("version:"):
                return line.split(":", 1)[1].strip()
    return ""


def check_texra(env: Env) -> Check:
    want, install = pinned_texra_version(env.root)
    binary = which("texra-blueprint")
    if not binary:
        return Check(
            "texra-blueprint", "texra-blueprint (paper-gap notes)", WARN, "not found",
            f"run: {install}" if install
            else "install texra-blueprint; the pin belongs in .github/allowed-tools.json",
        )
    have = installed_texra_version(binary)
    if not want:
        return Check("texra-blueprint", "texra-blueprint (paper-gap notes)", WARN,
                     f"installed {have or 'version unknown'}; no pin in .github/allowed-tools.json",
                     "record the version the project expects in .github/allowed-tools.json")
    if have and have.lstrip("v") == want.lstrip("v"):
        return Check("texra-blueprint", "texra-blueprint (paper-gap notes)", PASS,
                     f"{have} (pinned {want})")
    return Check(
        "texra-blueprint", "texra-blueprint (paper-gap notes)", WARN,
        f"installed {have or 'version unknown'}, pinned {want}",
        f"run: {install}" if install else f"install texra-blueprint {want}",
    )


def check_codex(env: Env) -> Check:
    """Binary discovery only — whether the key works is the next check."""
    return binary_check(
        "codex", "codex CLI (binary)",
        os.environ.get("MIPSTARRE_CODEX_BIN") or "codex",
        "install the codex CLI (npm install -g @openai/codex, or the release binary) "
        "and open a new shell so `codex --version` works",
    )


def check_codex_probe(env: Env) -> Check:
    """Functional key probe — delegated, because only it knows the key layout."""
    script = env.root / "local" / "bin" / "session" / "probe-key.sh"
    key = cfg_get(env.config, "session.main.key", "default")
    if not script.is_file():
        return Check("codex-probe", "codex answers (functional)", WARN,
                     "local/bin/session/probe-key.sh is not in this tree",
                     "check by hand that codex starts and answers one prompt")
    if not env.probe:
        return Check("codex-probe", "codex answers (functional)", WARN,
                     "skipped by --no-probe",
                     f"run: local/bin/session/probe-key.sh {key}")
    rc, out, err = run(["/bin/sh", str(script), str(key)], timeout=300, cwd=env.root)
    if rc == 0:
        return Check("codex-probe", "codex answers (functional)", PASS, f"key '{key}' answered")
    return Check(
        "codex-probe", "codex answers (functional)", FAIL,
        f"key '{key}': {first_line(err or out) or f'probe exited {rc}'}",
        f"run: local/bin/session/probe-key.sh {key}   and read its output. "
        "A quota or authentication error is an owner matter: the key is retired until "
        "the owner says otherwise",
    )


def gh_binary() -> str | None:
    return which(os.environ.get("MIPSTARRE_GH") or "gh")


def check_gh(env: Env) -> Check:
    return binary_check(
        "gh", "gh CLI (binary)", os.environ.get("MIPSTARRE_GH") or "gh",
        "install the GitHub CLI (see https://cli.github.com; or drop the release "
        "binary in ~/.local/bin, which this check also searches)",
    )


def check_gh_auth(env: Env) -> Check:
    """Authenticate by exercising the API, not by trusting `gh auth status`.

    An old client once rejected a perfectly valid fine-grained token, so the
    API read decides and the status command is only commentary.
    """
    path = gh_binary()
    if not path:
        return Check("gh-auth", "gh API authentication", FAIL, "gh is missing",
                     "install the GitHub CLI first")
    status_rc, _, _ = run([path, "auth", "status"], timeout=45)
    rc, out, err = run([path, "api", "user", "--jq", ".login"], timeout=45)
    login = first_line(out)
    if rc == 0 and login:
        note = "" if status_rc == 0 else \
            " (`gh auth status` disagrees; the API read is the evidence, an old gh can " \
            "reject a valid fine-grained token)"
        return Check("gh-auth", "gh API authentication", PASS, f"authenticated as {login}{note}")
    return Check(
        "gh-auth", "gh API authentication", FAIL,
        first_line(err) or "gh api user failed",
        "run: gh auth login   (or export GH_TOKEN with a token that may read and write "
        "issues and pull requests). Git transport over SSH is a SEPARATE prerequisite "
        "and does not authenticate the API",
    )


def check_gh_repo(env: Env) -> Check:
    slug = cfg_get(env.config, "project.github_slug", PLACEHOLDER_SLUG)
    if slug == PLACEHOLDER_SLUG:
        return Check("gh-repo", "GitHub repository reachable", WARN,
                     "no repository configured yet (still the placeholder)",
                     "run scripts/bootstrap_project.py --github-slug owner/repo … first")
    path = gh_binary()
    if not path:
        return Check("gh-repo", "GitHub repository reachable", FAIL, "gh is missing",
                     "install the GitHub CLI first")
    rc, out, err = run([path, "api", f"repos/{slug}", "--jq", ".full_name"], timeout=45)
    got = first_line(out)
    if rc == 0 and got.lower() == slug.lower():
        return Check("gh-repo", "GitHub repository reachable", PASS, got)
    return Check(
        "gh-repo", "GitHub repository reachable", FAIL,
        first_line(err) or f"expected {slug}, got {got or 'nothing'}",
        f"create {slug} on GitHub (the owner does this, once), or correct "
        "project.github_slug in local/project.json",
    )


def remote_url(root: Path) -> tuple[str, str]:
    """(remote name, url) — the `github` remote first, then `origin`."""
    git = which("git")
    if not git:
        return "", ""
    for name in ("github", "origin"):
        rc, out, _ = run([git, "remote", "get-url", name], cwd=root, timeout=20)
        if rc == 0 and out.strip():
            return name, out.strip()
    return "", ""


def check_ssh_github(env: Env) -> Check:
    git = which("git")
    name, url = remote_url(env.root)
    fix = ("add an SSH key to your GitHub account: ssh-keygen -t ed25519 -C 'this machine', "
           "then paste ~/.ssh/id_ed25519.pub at https://github.com/settings/keys, "
           "and test with: ssh -T git@github.com")
    quiet = {"GIT_TERMINAL_PROMPT": "0",
             "GIT_SSH_COMMAND": "ssh -o BatchMode=yes -o ConnectTimeout=10"}
    if url and git:
        rc, _, err = run([git, "ls-remote", "--heads", url], cwd=env.root,
                         timeout=60, env=quiet)
        if rc == 0:
            return Check("ssh-github", "Git transport to GitHub", PASS,
                         f"remote '{name}' answers")
        return Check("ssh-github", "Git transport to GitHub", FAIL,
                     first_line(err) or f"git ls-remote on remote '{name}' failed", fix)
    ssh = which("ssh")
    if not ssh:
        return Check("ssh-github", "Git transport to GitHub", WARN, "no ssh client found",
                     "install an ssh client, then " + fix)
    rc, out, err = run([ssh, "-o", "BatchMode=yes", "-o", "ConnectTimeout=10",
                        "-T", "git@github.com"], timeout=45)
    text = f"{out}\n{err}"
    if "successfully authenticated" in text.lower():
        return Check("ssh-github", "Git transport to GitHub", PASS,
                     "ssh to github.com works (no git remote configured yet)")
    return Check("ssh-github", "Git transport to GitHub", FAIL,
                 first_line(err or out) or "ssh to github.com did not authenticate", fix)


def check_proxy(env: Env) -> Check:
    """Report proxy variables by NAME — their values routinely carry credentials."""
    present = [name for name in PROXY_VARS if os.environ.get(name)]
    if not present:
        return Check("proxy", "proxy environment", PASS, "no proxy variables set")
    return Check(
        "proxy", "proxy environment", WARN,
        "set (values not shown): " + ", ".join(present),
        "make sure the proxy reaches github.com and arxiv.org, or unset those variables "
        "in the shell that starts the session",
    )


CHECKS = (
    check_python, check_git, check_git_identity, check_tmux, check_elan,
    check_toolchain, check_lake, check_mathlib_cache, check_disk,
    check_cache_root, check_machine, check_latex, check_blueprint_tools,
    check_texra, check_codex, check_codex_probe, check_gh, check_gh_auth,
    check_gh_repo, check_ssh_github, check_proxy,
)


def run_checks(root: Path, probe: bool = True) -> list[Check]:
    env = Env(root=root, config=load_config(root), probe=probe)
    results: list[Check] = []
    for func in CHECKS:
        try:
            results.append(func(env))
        except Exception as exc:  # a broken check must not hide the others
            results.append(Check(func.__name__, func.__name__, WARN,
                                 f"the check itself failed: {exc}", ""))
    return results


def render(results: list[Check]) -> str:
    width = max(len(c.ident) for c in results)
    lines = []
    for check in results:
        lines.append(f"{check.status:<4}  {check.ident:<{width}}  {check.title}"
                     + (f" — {check.detail}" if check.detail else ""))
        if check.status != PASS and check.fix:
            lines.append(" " * (width + 8) + f"fix: {check.fix}")
    counts = {state: sum(1 for c in results if c.status == state)
              for state in (PASS, WARN, FAIL)}
    lines.append("")
    lines.append(f"{counts[PASS]} pass, {counts[WARN]} warn, {counts[FAIL]} fail")
    if counts[FAIL]:
        lines.append("Not ready: fix every FAIL line above, then run this again.")
    elif counts[WARN]:
        lines.append("Ready to start. The WARN lines are things you will need later.")
    else:
        lines.append("Ready to start.")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="repository root (default: the checkout this script lives in)")
    parser.add_argument("--json", action="store_true", help="machine-readable output")
    parser.add_argument("--no-probe", action="store_true",
                        help="do not run the functional codex key probe")
    args = parser.parse_args(sys.argv[1:] if argv is None else argv)

    results = run_checks(args.root.resolve(), probe=not args.no_probe)
    failed = sum(1 for c in results if c.status == FAIL)
    if args.json:
        payload = {
            "root": str(args.root.resolve()),
            "ok": failed == 0,
            "summary": {state.lower(): sum(1 for c in results if c.status == state)
                        for state in (PASS, WARN, FAIL)},
            "checks": [c.as_dict() for c in results],
        }
        sys.stdout.write(json.dumps(payload, indent=2) + "\n")
    else:
        sys.stdout.write(render(results) + "\n")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
