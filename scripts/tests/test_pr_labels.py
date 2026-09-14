"""PR publication must classify changes without starting automation implicitly."""

from contextlib import ExitStack, redirect_stdout
import io
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "local" / "bin"))
import pr_open
from wf_util import LayerError


class PublicationLabelsTest(unittest.TestCase):
    def run_open(self, *, issue_labels=(), explicit=(), existing=None, dry_run=False):
        args = pr_open._parse_args([
            "--branch", "issue-42-pauli", "--issue", "42",
            "--title", "feat(QPBT): prove a lemma",
            *[arg for label in explicit for arg in ("--label", label)],
            *(["--dry-run"] if dry_run else []),
        ])
        with ExitStack() as stack:
            patched = {}
            for name, kwargs in {
                "lint_branch": {}, "require_diff": {"return_value": 1},
                "checked_push": {}, "pr_create": {"return_value": 99},
                "gh_common.pr_for_branch": {"return_value": existing},
                "gh_common.issue_view": {"return_value": {
                    "labels": [{"name": name} for name in issue_labels]}},
                "gh_common.list_labels": {"return_value": [
                    "formalization", "proof", "ci", "bug", "auto-fix-codex",
                    "needs-owner", "all-resolved", "scout", "tracking"]},
                "gh_common.api": {},
            }.items():
                patched[name] = stack.enter_context(mock.patch("pr_open." + name, **kwargs))
            stack.enter_context(redirect_stdout(io.StringIO()))
            try:
                result = pr_open.open_pr(args)
            except LayerError as exc:
                return exc, patched
            return result, patched

    def test_create_inherits_only_descriptive_issue_labels(self):
        result, calls = self.run_open(issue_labels=[
            "proof", "auto-fix-codex", "needs-owner", "all-resolved", "scout", "tracking"])
        self.assertEqual(result, 0)
        calls["gh_common.api"].assert_called_once_with(
            "issues/99/labels", method="POST", payload={"labels": ["proof"]},
            mutation=True, idempotent=True)
        calls["checked_push"].assert_called_once()

    def test_adopt_preserves_existing_labels_and_adds_explicit_and_inherited(self):
        result, calls = self.run_open(issue_labels=["proof"], explicit=["bug,proof"],
                                     existing={"number": 99, "body": "Closes #42",
                                               "labels": [{"name": "auto-fix-codex"}]})
        self.assertEqual(result, 0)
        label_call = calls["gh_common.api"].call_args_list[-1]
        self.assertEqual(label_call.args, ("issues/99/labels",))
        self.assertEqual(label_call.kwargs["method"], "POST")
        self.assertEqual(label_call.kwargs["payload"], {"labels": ["bug", "proof"]})
        calls["pr_create"].assert_not_called()

    def test_already_classified_pr_can_be_adopted_without_relabeling(self):
        result, calls = self.run_open(existing={"number": 99, "body": "Closes #42",
                                              "labels": [{"name": "formalization"}]})
        self.assertEqual(result, 0)
        self.assertFalse(any(c.args[0].endswith("/labels")
                             for c in calls["gh_common.api"].call_args_list))

    def test_unclassified_or_unknown_labels_refuse_before_push(self):
        for explicit in ([], ["auto-fix-codex"], ["not-a-repository-label"]):
            with self.subTest(explicit=explicit):
                result, calls = self.run_open(explicit=explicit)
                self.assertIsInstance(result, LayerError)
                calls["checked_push"].assert_not_called()
                calls["pr_create"].assert_not_called()
                calls["gh_common.api"].assert_not_called()

    def test_explicit_automation_label_is_deliberate_and_dry_run_never_writes(self):
        for dry in (False, True):
            result, calls = self.run_open(explicit=["ci", "auto-fix-codex"], dry_run=dry)
            self.assertEqual(result, 0)
            if dry:
                calls["checked_push"].assert_not_called()
                calls["gh_common.api"].assert_not_called()
            else:
                self.assertEqual(calls["gh_common.api"].call_args.kwargs["payload"],
                                 {"labels": ["auto-fix-codex", "ci"]})


if __name__ == "__main__":
    unittest.main()
