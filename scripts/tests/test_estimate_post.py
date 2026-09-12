#!/usr/bin/env python3
"""`estimate.sh` and `estimate_post.py` are ONE interface; prove it.

The 2026-09-12-era `estimate.sh` invoked `estimate_post.py` with five options
that the parser does not define (`--timestamp`, `--in-pr`, `--open-prs`,
`--in-pr-source`, `--snapshot-generated`) and never passed the required
`--in-open-prs`, so `argparse` exited 2 on every cron tick.  The caller swallowed
that with `|| echo ... failed` and appended its `estimates.jsonl` row anyway: the
owner's only progress channel would have posted nothing for a whole run while the
cron log looked almost normal, and no test caught it because the existing tests
only grep `estimate.sh` for substrings.

So the test here is not "does the parser accept a hand-written vector" — it is
"does the parser accept the vector `estimate.sh` actually builds".  The vector is
READ OUT OF THE SHELL SCRIPT, so a future edit to either side that breaks the
pairing fails here.
"""

from __future__ import annotations

import io
import re
import shlex
import sys
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BIN_DIR = REPO_ROOT / "local" / "bin"
sys.path.insert(0, str(BIN_DIR))

import estimate_post  # noqa: E402

ESTIMATE_SH = REPO_ROOT / "results/telemetry/owner-tools/estimate.sh"

#: The shell values estimate.sh computes, with a plausible value each.  Every
#: name here must appear in the script's invocation; see `test_no_unknown_shell_value`.
SHELL_VALUES = {
    "ISSUE": "168",
    "TS": "2026-09-13 05:00Z",
    "PCT": "89",
    "DAYS": "2.1",
    "NOW": "21",
    "DENOM": "197",
    "MAIN": "60dbabef",
    "INPR": "9",
    "NPR": "21",
    "RATE": "14",
    "SNAP_AT": "2026-09-13T04:58:12Z",
    "POST": str(BIN_DIR / "estimate_post.py"),
}


def invocation() -> str:
    """The `python3 "$POST" ...` command line, as one logical line."""
    text = ESTIMATE_SH.read_text(encoding="utf-8")
    text = text.replace("\\\n", " ")                       # join continuations
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("python3 ") and '"$POST"' in stripped:
            return stripped
    raise AssertionError(f"no `python3 \"$POST\" ...` invocation found in {ESTIMATE_SH}")


def argv_from_estimate_sh() -> list[str]:
    """Exactly the argument vector estimate.sh builds, with the shell expanded."""
    command = invocation()
    for name, value in SHELL_VALUES.items():
        command = command.replace(f'"${name}"', shlex.quote(value))
        command = command.replace(f"${name}", shlex.quote(value))
    parts = shlex.split(command)
    assert parts[0] == "python3", parts[:2]
    return parts[2:]                                       # drop `python3 <script>`


class EstimatePostInterfaceTestCase(unittest.TestCase):
    def test_the_vector_estimate_sh_builds_is_accepted(self) -> None:
        argv = argv_from_estimate_sh() + ["--dry-run"]
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = estimate_post.main(argv)
        self.assertEqual(
            code, 0,
            "estimate.sh's own argument vector must not make estimate_post.py "
            f"exit {code}.\nvector: {argv}\nstderr: {err.getvalue()}")
        body = out.getvalue().strip("\n")
        self.assertIsNotNone(
            estimate_post.BODY_RE.match(body),
            f"the rendered body must be the two conforming lines, got:\n{body}")

    def test_no_unknown_shell_value_slips_into_the_vector(self) -> None:
        # A `$SOMETHING` this test does not know about would be passed through
        # literally and the assertion above would still pass by accident.
        argv = argv_from_estimate_sh()
        leftovers = [item for item in argv if "$" in item]
        self.assertEqual(leftovers, [],
                         "unexpanded shell values in the vector; add them to "
                         f"SHELL_VALUES: {leftovers}")

    def test_every_option_passed_is_defined_by_the_parser(self) -> None:
        options = {item for item in argv_from_estimate_sh() if item.startswith("--")}
        known = set()
        for action in estimate_post.build_parser()._actions:  # noqa: SLF001
            known.update(action.option_strings)
        self.assertEqual(sorted(options - known), [],
                         "estimate.sh passes options estimate_post.py does not define")

    def test_the_required_values_are_all_passed(self) -> None:
        options = {item for item in argv_from_estimate_sh() if item.startswith("--")}
        for required in ("--percent", "--days", "--open-sites", "--main",
                         "--in-open-prs", "--rate"):
            self.assertIn(required, options,
                          f"estimate.sh must pass {required}; without it main() "
                          "calls parser.error and exits 2")

    def test_the_provenance_clause_carries_the_snapshot(self) -> None:
        body = estimate_post.render(
            percent=89, days="2.1", open_sites=21, denominator=197,
            main="60dbabef", in_open_prs=9, rate=14, ts="2026-09-13 05:00Z",
            open_prs=21, in_pr_source="github-snapshot",
            snapshot_generated="2026-09-13T04:58:12Z")
        self.assertIn("9 proved in 21 open PRs (GitHub snapshot 2026-09-13T04:58:12Z)", body)
        self.assertIsNotNone(estimate_post.BODY_RE.match(body))

    def test_without_the_optional_values_the_old_shape_is_kept(self) -> None:
        body = estimate_post.render(
            percent=89, days="n/a", open_sites=21, denominator=197,
            main="60dbabef", in_open_prs=9, rate=0, ts="2026-09-13 05:00Z")
        self.assertIn("9 proved in open PRs", body)
        self.assertIsNotNone(estimate_post.BODY_RE.match(body))

    def test_angle_brackets_cannot_reach_the_sub(self) -> None:
        body = estimate_post.render(
            percent=1, days="n/a", open_sites=1, denominator=197, main="abcdef1",
            in_open_prs=0, rate=0, ts="2026-09-13 05:00Z", open_prs=1,
            in_pr_source="live", snapshot_generated="<script>x</script>")
        self.assertNotIn("<script>", body)
        self.assertIsNotNone(estimate_post.BODY_RE.match(body))

    def test_estimate_sh_reports_a_failed_post_loudly(self) -> None:
        body = ESTIMATE_SH.read_text(encoding="utf-8")
        self.assertIn("ESTIMATE NOT POSTED", body,
                      "a post that fails must say so; the old `|| echo ... failed` "
                      "read like a warning next to a successful-looking run")
        # The retired spellings may appear in a comment explaining the defect;
        # what must not carry them is the invocation itself.
        command = invocation()
        self.assertNotIn("--timestamp", command)
        self.assertIsNone(re.search(r"--in-pr\b(?!-source)", command),
                          "--in-pr is not an estimate_post.py option")


if __name__ == "__main__":
    unittest.main()
