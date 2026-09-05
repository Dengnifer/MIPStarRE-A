#!/usr/bin/env python3
"""Regression tests for the consolidated PR review workflow."""

from __future__ import annotations

import re
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[2]
PR_CI = REPO_ROOT / ".github" / "workflows" / "pr-ci.yml"
PR_REVIEW = REPO_ROOT / ".github" / "workflows" / "pr-review.yml"
CODE_REVIEW_PROMPT = REPO_ROOT / ".github" / "prompts" / "claude-code-review-prompt.md"
PROSE_REVIEW_PROMPT = REPO_ROOT / ".github" / "prompts" / "blueprint-prose-review-prompt.md"
LOCAL_REVIEW = REPO_ROOT / "local" / "bin" / "review.sh"


def _job_block(text: str, job: str) -> str:
    match = re.search(rf"^  {re.escape(job)}:\n(?P<body>.*?)(?=^  [A-Za-z0-9_-]+:|\Z)", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"missing job {job}")
    return match.group("body")


class PRReviewWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.pr_ci = PR_CI.read_text(encoding="utf-8")
        cls.pr_review = PR_REVIEW.read_text(encoding="utf-8")
        cls.code_prompt = CODE_REVIEW_PROMPT.read_text(encoding="utf-8")
        cls.prose_prompt = PROSE_REVIEW_PROMPT.read_text(encoding="utf-8")
        cls.local_review = LOCAL_REVIEW.read_text(encoding="utf-8")

    def test_review_trigger_surface_includes_agents_file(self) -> None:
        self.assertIn("- 'AGENTS.md'", self.pr_ci)

    def test_gate_runs_and_fails_on_unsuccessful_pr_ci(self) -> None:
        gate = _job_block(self.pr_review, "gate")
        before_runs_on = gate.split("runs-on:", 1)[0]
        self.assertNotIn("if:", before_runs_on)
        self.assertIn("core.setFailed(`PR CI concluded ${wr.conclusion}", gate)
        self.assertIn("PR Review must not report success without a review", gate)

    def test_code_review_missing_token_is_not_a_green_skip(self) -> None:
        code_review = _job_block(self.pr_review, "code-review")
        self.assertIn('echo "::error::$REVIEW_PROVIDER token is not configured"', code_review)
        self.assertIn("exit 1", code_review)

    def test_prose_review_preserves_missing_token_soft_skip(self) -> None:
        prose_review = _job_block(self.pr_review, "prose-review")
        self.assertIn("id: provider-token", prose_review)
        self.assertIn('echo "skip=true" >> "$GITHUB_OUTPUT"', prose_review)
        self.assertIn("Skipping prose review", prose_review)
        self.assertIn("if: steps.provider-token.outputs.skip != 'true'", prose_review)

    def test_reviewers_derive_blueprint_spans_from_labels(self) -> None:
        for prompt in (self.code_prompt, self.prose_prompt):
            self.assertIn("scripts/blueprint_citations.py", prompt)
            self.assertIn("do not flag line drift", prompt)
        self.assertIn('BLUEPRINT_CITATION_PATH="scripts/blueprint_citations.py"',
                      self.local_review)
        self.assertIn('--files-from "$RUN_DIR/files.txt" --format markdown',
                      self.local_review)
        self.assertIn('name="blueprint-citations.md"', self.local_review)
        self.assertIn('case "$CITATION_RC" in', self.local_review)
        self.assertIn("refusing review without citation evidence", self.local_review)

    def test_blueprint_map_has_a_reserved_sanitized_attachment_budget(self) -> None:
        self.assertIn(
            'CITATION_MAX_BYTES="${MIPSTARRE_CITATION_MAX_BYTES:-30000}"',
            self.local_review,
        )
        self.assertIn(
            '--max-bytes "$CITATION_MAX_BYTES"',
            self.local_review,
        )
        self.assertIn(
            '--full-output "$BLUEPRINT_CITATION_MAP_RAW"',
            self.local_review,
        )
        self.assertIn(
            'sanitize_to "$BLUEPRINT_CITATION_MAP_BOUNDED" "$BLUEPRINT_CITATION_MAP"',
            self.local_review,
        )
        self.assertIn("truncated by review.sh attachment budget", self.local_review)
        self.assertIn('"$CITATION_MAX_BYTES" -ge 128', self.local_review)
        run_agent = self.local_review.split("run_agent() {", 1)[1].split(
            "# ensure_review_body", 1
        )[0]
        self.assertLess(
            run_agent.index('if [ -s "$BLUEPRINT_CITATION_MAP" ]'),
            run_agent.index('if [ -n "$ctx" ]'),
        )

    def test_fallback_uses_only_the_bounded_sanitized_citation_map(self) -> None:
        fallback = self.local_review.split("build_standalone() {", 1)[1].split(
            "# preserve_prior", 1
        )[0]
        self.assertIn('cat "$BLUEPRINT_CITATION_MAP"', fallback)
        self.assertNotIn("BLUEPRINT_CITATION_MAP_RAW", fallback)
        self.assertNotIn("BLUEPRINT_CITATION_MAP_BOUNDED", fallback)
        self.assertLess(
            fallback.index('name="blueprint-citations.md"'),
            fallback.index('name="diff.patch"'),
        )


if __name__ == "__main__":
    unittest.main()
