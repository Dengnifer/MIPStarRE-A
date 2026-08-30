# Protocol: issues and pull requests

Normative for the issue tree (`issues/`), the PR registry (`prs/`), and the
lifecycle automation in `local/bin/`. Read `local/protocols/meta.md` first for
how protocols evolve and what telemetry each stage owes.

The parent repository, [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE),
ran this lifecycle on GitHub: native issues with sub-issues and labels, pull
requests with branch protection, and three workflows —
`.github/workflows/issue-automation.yml`, `housekeeping.yml`, `pr-cleanup.yml`.
Those files are frozen here as reference and never execute. This document says
what replaces each of their mechanisms and, where the replacement looks
gratuitously strict, which incident it is paying for.

---

## 1. What is being replaced

| Parent mechanism | Local replacement |
|---|---|
| Issue forms, `.github/ISSUE_TEMPLATE/*.yml` | `issue_new.py --template {formalization,bug,tracking}` |
| `classify-outside` keyword pass (issue-automation.yml:97-220) | `issue_new.py` deterministic classification stage |
| `classify-trusted` model pass (issue-automation.yml:39-96) | not wired; hook documented in `issue_new.py` |
| `scout` Mathlib report (issue-automation.yml:221-334) | `issue_new.py` stage 3 → `local/bin/scout.sh` when it exists |
| `track` bookkeeping (issue-automation.yml:335-572) | `track.py`, invoked by the lifecycle scripts |
| `followups` mining (issue-automation.yml:573-624) | hook in `pr_merge.py` → `local/bin/followups.sh` |
| Native sub-issues (one parent, GraphQL) | `parent` / `children` frontmatter + `validate_tree.py` |
| `gh label list` as source of truth | `local/labels.yml` |
| Issue comments | marker-deduplicated bullets under `## Activity` |
| PR body normalization (pr-cleanup.yml) | `pr_open.py` skeleton + labels copy; prose hook unwired |
| Branch protection (required checks + review) | the gate in `pr_merge.py` |
| `standup` (housekeeping.yml:31-215) | `housekeeping.sh standup` |
| `stale-audit` (housekeeping.yml:216-309) | `housekeeping.sh stale-audit` = `export_issues.py` + `scripts/audit_stale_issues.py` |
| `linter-sweep` (housekeeping.yml:310-382) | `housekeeping.sh linter-sweep` |
| `readme-freshness` (housekeeping.yml:383-463) | `housekeeping.sh readme-freshness` |
| Four cron entries (housekeeping.yml:14-18) | on demand only (DESIGN.md:53) |

---

## 2. Data model

### 2.1 Issues

One file per issue at `issues/NNNN-slug.md`, id four-digit zero-padded and
allocated from `issues/.seq` under a lock. Frontmatter is exactly the schema of
DESIGN.md:97-100:

```yaml
---
id: "0042"
title: "Formalize the Pauli basis test soundness lemma"
state: "open"                 # open | closed
state_reason: null            # completed | not-planned | null
parent: "0007"                # at most one, or null
children: ["0043", "0044"]
labels: ["formalization", "qpbt-analysis"]
pinned: false
created: "2026-08-30T04:12:00Z"
updated: "2026-08-30T04:12:00Z"
agent_session: null
---
```

`parent` is a **scalar**. GitHub's native sub-issues allow one parent per issue
and the whole tracking computation depends on it; a list here is a validation
error, not a generalization.

The body carries the template's sections, then two machine-written sections in
this order, both terminal:

* `## Initial classification` — what the deterministic pass applied, and why;
* `## Activity` — the append-only log that replaces issue comments.

`## Activity` is always last. Every append is an end-of-file write, so nothing
in the human-authored part of the body is ever reflowed by automation.

Standup digests live at `issues/standup/YYYY-MM-DD.md` with `id:
standup-YYYY-MM-DD`. They are outside the tree proper: `validate_tree.py` does
not walk them and `export_issues.py` does not export them.

### 2.2 Pull requests

One directory per PR at `prs/NNNN-slug/`, id from `prs/.seq`, containing:

```
prs/0007-feat-quantum-soundness-bound/
├── pr.md            # frontmatter + body
├── ci/<sha>.json    # one manifest per CI run, written by local/bin/ci.sh
└── reviews/<sha>.md # one verdict per review, written by local/bin/review.sh
```

Frontmatter is exactly DESIGN.md:101-105 — `id, branch, issue, base, state,
head_sha, ci_status, review_state, fix_iterations, auto_fix, labels, created,
merged_commit`. There is **no `title` field**: the PR title is the body's `#`
heading, followed by the Motivation / Description / Testing skeleton required by
docs/CONTRIBUTING.md:36-58 and the link footer.

Both the CI status and the review state appear twice on purpose: as a summary in
frontmatter and as per-SHA evidence on disk. The merge gate requires both to
agree, because frontmatter is editable by hand and a summary that has drifted
from its evidence is exactly the failure mode a gate exists to catch.

### 2.3 Names

* Branches: `issue-<id>-<slug>`, or `codex/issue-<id>-<slug>` when an agent
  created them (DESIGN.md:106-107).
* Titles and slugs are bracket-free. `[` and `]` are rejected at creation.
* Fix commits keep the exact subject prefixes `[codex-auto-fix]` and
  `[codex-review-fix]`; the review gate's regex depends on them.

The `issue-(\d+)` fragment is load-bearing. `track.py` recovers a PR's linked
issue from the branch name with that regex, ported unchanged from
issue-automation.yml:463-466. A branch that omits its issue id is invisible to
every progress note downstream, which is why `pr_open.py` rejects it rather than
letting it fail silently at merge time.

The bracket rule is likewise not stylistic. docs/CONTRIBUTING.md:122-124:
"Avoid prefixes like `[Chapter 9] ...`: bot-generated branch names inherit those
characters, and `]` breaks part of the PR automation stack." A `:` in a title is
fine — `Tracking: ...` is the documented idiom and the classifier keys on it —
but a `:` in a *branch* is not, since `git check-ref-format` rejects it.

### 2.4 Labels

`local/labels.yml` is the taxonomy and the only source of truth. It ports
docs/CONTRIBUTING.md:285-360 with the LDT chapter labels replaced by QPBT names
(`qpbt-test`, `qpbt-analysis`) and the paper labels retargeted to
`paper-2001.04383` and `paper-1904.05870`.

Two rules, both from recorded parent-repo history:

* **Only labels in the file may be applied.** issue-automation.yml:172-179
  fetched the live repo labels before applying any, with the comment "so we
  don't fail on nonexistent labels". Here `issue_new.py` filters proposals
  against the taxonomy and `validate_tree.py` rejects anything else.
* **The `banned:` block is enforced.** `all-resolved` was retired when the track
  job started posting a note instead of a label (docs/CONTRIBUTING.md:217-219);
  `self-improvement`, `expansion-graph`, `quantum-foundations` and `automation`
  are dead taxonomy that survived in prose (docs/CONTRIBUTING.md:292-294); the
  `wolf-chN` names and the `2009.12982` paper id are drift imported from a
  sibling repository by workflow ci-sync (pr-cleanup.yml:1-2). Each carries its
  reason, printed at the point of failure.

---

## 3. The lifecycle

```
issue_new.py ─► classify ─► scout ─► branch ─► pr_open.py ─► ci.sh ─► review.sh
                                                                        │
                                                            autofix.sh ─┤
                                                                        ▼
                                                                  pr_merge.py
                                                                        │
                                              ┌─────────────────────────┼──────────────┐
                                              ▼                         ▼              ▼
                                       issue_close.py             track.py       followups.sh
```

### 3.1 Creation, classification, scouting — in that order

`issue_new.py` runs three stages in one process, and the order is the point.

The parent repository consolidated three workflows into one to fix an observed
race (issue-automation.yml:13-21):

> The scout run for a freshly opened issue was routinely cancelled:
> classification added labels seconds after open, every labeled event cancelled
> the in-flight scout run (per-issue concurrency with cancel-in-progress), and
> the label runs themselves skipped. Ordering the jobs inside one workflow
> removes the race.

Locally there are no events to race, but the *dependency* survives: scouting
decides whether to run by reading labels that classification writes. So the
pipeline is straight-line, and the scout stage re-reads the issue file from disk
rather than trusting an in-memory copy — the local form of the staleness fix at
issue-automation.yml:277-279 ("the payload's label list is stale").

Classification is deterministic: the keyword regexes of
issue-automation.yml:133-166, ported verbatim, plus alias matching for the
family and paper labels driven by `aliases:` entries in `labels.yml`. It reads
no credential and calls no model — preserving the deliberate separation at
issue-automation.yml:104, where the outside-reporter job was given no provider
secrets so that untrusted text never met one.

An unedited template body is not classified. Its placeholder prose names
"blueprint", "theorem" and "build", and classifying it would label every new
issue identically. Only the title, plus a body supplied with `--body-file`,
reaches the keyword pass.

### 3.2 Sub-issue attachment

`issue_new.py --parent <id>` writes both halves of the relationship — the
child's `parent` and the parent's `children` — each under its own lock. Nothing
else may write one half alone. `validate_tree.py` checks both directions,
because a half-written link produces a tracking parent whose counts are quietly
wrong rather than an error anyone sees.

### 3.3 Opening a PR

`pr_open.py --issue --branch --title` lints the branch, copies the issue's
labels onto the record (the mechanical half of pr-cleanup.yml), writes the
Motivation / Description / Testing skeleton, and appends the link footer.

`Addresses #N` keeps the issue open; `Closes #N` (or `Fixes #N`) auto-closes it
on merge (docs/CONTRIBUTING.md:61-62). The keyword is machine-read at merge
time, so the footer is never rewritten by any normalization step.

`track.py --pr-opened` then announces the PR on the linked issues' tracking
parents — except for `codex/` and `claude/` branches, where the announcement was
upstream owned by pr-cleanup (issue-automation.yml:480-482, pr-cleanup.yml:15-22)
and is left to that path here as well.

### 3.4 The merge gate

`pr_merge.py <id>` is the only script in this area that changes history. GitHub
enforced "required checks + required review" server-side; locally that authority
is this file, so it refuses by default and every override is named on the
command line.

All of the following must hold:

1. the record is `state: open`;
2. `head_sha` is recorded and equals the branch tip;
3. `ci_status: success` **and** a manifest at `prs/<id>/ci/<head_sha>.json`;
4. `review_state: APPROVED`, or `COMMENTED` with zero unchecked findings in
   `prs/<id>/reviews/<head_sha>-*.md` (the verdict files `review.sh` writes:
   `<head_sha>-code.md`, and `-prose.md` when blueprint files changed);
5. the fix loop is quiescent: no live-held fix lock for the branch
   (`locks/fix-<branch>.lock` with a running holder pid), and
   `fix_iterations` within the combined cap (default 5, `MIPSTARRE_FIX_CAP` —
   the same variable `autofix.sh` reads, so raising the cap moves both the
   loop and the gate together).

Condition 2 is what makes 3 and 4 mean anything. DESIGN.md:66-69 requires review
only after green CI **on the same head SHA**; a verdict recorded against an
earlier commit says nothing about what is being merged, so a new commit on the
branch invalidates both the CI manifest and the review verdict.

Condition 4's "unchecked findings" are markdown checkboxes: a review verdict
records each finding as `- [ ]`, and ticking a box is the reviewer's or author's
record that it was addressed or deliberately dismissed. A `COMMENTED` verdict
with an open box is a blocker; with none, it is an approval in all but name.

`review_state: blocked` is a distinct refusal. Per DESIGN.md:66-69 a failed CI
must yield `blocked`, never a silent skip, so the gate reports it as "CI failed,
so review was refused" rather than as a missing review.

When `LOCAL_REVIEW_ENABLED=false` no verdict can exist. The gate does not
silently waive the requirement: it refuses unless `--allow-unreviewed` is given,
and says so. Kill switches disable only on the literal string `false`; unset
means enabled (DESIGN.md:73-75).

On success, in order:

1. `git merge --no-ff` onto the base;
2. `git update-ref refs/remotes/origin/<base> refs/heads/<base>` — the hooks and
   every diff-based audit silently self-disable when `origin/main` does not
   resolve (DESIGN.md:84-85), and there is no remote here to maintain it;
3. record `state: merged`, `merged_commit`;
4. auto-close each `Closes`/`Fixes` issue as `completed`, each of which runs the
   closed path of `track.py`;
5. `track.py --pr-merged --exclude-issue <each auto-closed id>`;
6. follow-up mining hook, then the background cache warmer;
7. delete the branch and its worktree.

Step 5's exclusion is not an optimization. Upstream a merged PR reached the
tracking parent twice — once through the merged-PR path, once through the
auto-close that the merge fired — and the fix is recorded at
issue-automation.yml:449-452: "Closes/Fixes issues are excluded from progress
comments: their auto-close fires the issues/closed path, which handles the
tracking update." Locally both halves run in one process, so the exclusion has
to be passed explicitly or the parent gets two notes per child.

### 3.5 Closing and tracking

`issue_close.py <id> --reason {completed,not-planned}` sets both `state` and
`state_reason` and calls `track.py` **only** for `completed`.

GitHub counted any closed sub-issue as progress
(issue-automation.yml:392-396). The local counter counts only children that are
closed *and* completed, so `[closed/total]` is a count of resolved children and
a not-planned close withdraws from the numerator without touching the
denominator. Closing an issue as not-planned therefore never advances a tracking
parent toward its "ready to close" note.

`track.py` is pure bookkeeping — no model, no network:

* parent lookup and child counts from frontmatter, one parent maximum;
* `## Activity` appends deduplicated by a marker substring, the direct port of
  `commentOnce` (issue-automation.yml:403-417): "Post at most once: skip when
  any existing comment contains the marker (guards against redelivered events
  and re-runs)". On GitHub this was a replay defense against webhook
  redelivery; locally re-running a command is the *normal* way to use it, so
  the marker check is what stands between the tree and a page of duplicates;
* the "ready to close" note when every child is resolved, rather than a label —
  docs/CONTRIBUTING.md:217-219 records that the `all-resolved` label was retired
  in favour of exactly this note;
* PR-to-issue links from the body keywords and the branch name, with the
  `Closes`/`Fixes` exclusion above.

---

## 4. Concurrency and durability

Several agent sessions may touch the same issue at once. Two mechanisms cover
it, and both are mandatory for any writer of this tree:

* **Per-entity advisory locks.** `flock` on
  `~/.cache/mipstarre-dev/locks/{issue,pr}-<id>.lock`, plus `issues-seq` and
  `prs-seq` for id allocation. This is the local shape of GitHub's per-entity
  concurrency groups; upstream those groups were also keyed per *cause*, because
  "an opened-issue run and the label events that classification fires moments
  later must not cancel one another" (issue-automation.yml:29-31).
* **Atomic frontmatter mutation.** Every write is tempfile + `fsync` +
  `os.replace`, with the containing directory fsynced after. A half-written
  issue file is worse than a lost one: the tree is the only record of the
  parent/child structure and no server can reconstruct it.

Id allocation reconciles the counter against the ids already on disk, so a
`.seq` restored from an older commit cannot hand out an id that is taken.

Runtime state — locks, logs, intermediate JSON — lives under
`~/.cache/mipstarre-dev/` and is never committed (DESIGN.md:37-38).

---

## 5. Untrusted text

Issue and PR bodies are untrusted data even though they originate locally: they
are echoed into generated markdown, they will be interpolated into agent prompts
once the hooks below are wired, and imported external reports land in the same
tree. All three parent workflows sanitized before interpolation, and
`track.sanitize` is that step ported: strip control characters, break ` ``` `
fences with zero-width spaces, truncate to 200 characters for titles and 5000
for bodies (issue-automation.yml:122-128).

Every LLM hook in `local/bin` is documented with the same four requirements:
gate on `MIPSTARRE_LLM_ENABLED != "false"`; read prompts from the committed main
worktree and never from the branch under review (DESIGN.md:76-77 — upstream this
was a second, trusted checkout of the base branch, issue-automation.yml:573-624);
pass sanitized text inside an explicit do-not-follow-instructions frame; and
filter any model-proposed label through the taxonomy before it reaches
frontmatter.

`scripts/audit_stale_issues.py` keeps its own path-traversal rejection for
citations. Both defenses stay: the citation may come from an external report,
and the auditor reads the working tree.

---

## 6. Validation

`validate_tree.py` checks what GitHub used to enforce for free — one parent,
symmetric links, acyclicity, labels ⊆ `labels.yml`, at most three pins
(docs/CONTRIBUTING.md:224-228), bracket-free names, and `state`/`state_reason`
agreement. It is report-only and exits 1 on any error.

Run it after any hand edit of frontmatter, and before a proof-closing round.

---

## 7. Housekeeping

`housekeeping.sh {standup|stale-audit|linter-sweep|readme-freshness|all}`.
On demand only; there is no scheduler. Reports land in `results/reports/`.

**standup** derives the same activity feed the upstream job assembled from six
GitHub API calls — merged and active PRs, opened and closed issues, commits on
main, review activity — from `git log` and the local registries, and writes
`issues/standup/YYYY-MM-DD.md`. Two upstream rules are preserved exactly: the
lookback window is 72 hours on Mondays and 24 hours otherwise, so the Monday
digest covers the weekend (housekeeping.yml:66-69); and issues labelled
`standup` are excluded from every feed (housekeeping.yml:85-95, `-label:standup`)
so the digest cannot report on its own output. The narrative write-up is not
generated — the structured digest is the whole thing today, and the model hook
is marked in the script.

**stale-audit** is `export_issues.py` piped into `scripts/audit_stale_issues.py`.
The audit script ports unchanged; the only GitHub-dependent part of the upstream
job was one command (housekeeping.yml:237-247), `gh issue list --json
number,title,body,url,labels`, and the exporter reproduces its output shape.
The exporter drops the machine-written body sections, because the audit flags
backtick-quoted tokens that do not resolve to a Lean declaration and those
sections render label names in backticks — `formalization`, `blueprint`, `proof`
all match its identifier regex and none is a declaration.

**linter-sweep** is a full `lake build` teed to a log and summarized by
`scripts/lean_linter_warning_report.py`. It takes the machine-wide advisory
build lock (DESIGN.md:81-82) so it cannot race an agent build or the cache
warmer, and it is **excluded from `all`**: upstream it carried a 120-minute
timeout (housekeeping.yml:321) and it must never sit on a path someone runs
casually. Ask for it by name.

**readme-freshness** runs `scripts/audit_readme_freshness.py` unchanged.

Three of the four jobs are report-only, and that contract is documented in three
places upstream — most bluntly at docs/stale_issue_audit.md:143-144, "Do **not**
let the script close issues automatically. Flags are a starting point for human
review, not a decision." Nothing in `housekeeping.sh` closes, edits, or labels an
issue. `standup` is the sole writer and writes only its own digest.

The stale audit is meaningful only against committed code, so a dirty working
tree is reported before the run (docs/stale_issue_audit.md:157-159). The tool
exists because of a specific incident: issue #301 "stayed open long after its
named blockers ... had been resolved on `main`, and PR #647 had to do a
retroactive cleanup pass" (docs/stale_issue_audit.md:16-19).

---

## 8. Environment

| Variable | Effect |
|---|---|
| `MIPSTARRE_LLM_ENABLED` | `false` disables every model call; deterministic paths keep working |
| `LOCAL_REVIEW_ENABLED` | `false` means no verdict can exist; `pr_merge.py` then requires `--allow-unreviewed` |
| `MIPSTARRE_FIX_ITERATION_CAP` | combined fix-iteration cap (default 5) |
| `MIPSTARRE_CACHE_ROOT` | overrides `~/.cache/mipstarre-dev` |

All kill switches follow DESIGN.md:73-75: disabled only on the literal string
`false`; unset means enabled.

---

## 9. Not yet wired

Each is a marked hook that degrades to a clear message, never to a silent
no-op:

| Hook | Site | Behaviour today |
|---|---|---|
| LLM issue classification | `issue_new.py` | deterministic pass only |
| Mathlib scouting | `issue_new.py` → `local/bin/scout.sh` | notes that the script is absent |
| PR prose normalization | `pr_open.py` | skeleton and label copy only |
| Follow-up mining | `pr_merge.py` → `local/bin/followups.sh` | notes that follow-ups must be filed by hand |
| Cache warming | `pr_merge.py` → `local/bin/cache-warmer.sh` | notes that the hot cache is now stale |
| Standup narrative | `housekeeping.sh standup` | structured digest only |

When a hook is wired, amend this section and record the change in
`local/protocols/EVOLUTION.md` with its cause.
