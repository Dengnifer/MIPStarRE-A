# Issue-tree study: LionSR/MIPStarRE#449 vs Dengnifer/MIPStarRE-A#47 (2026-09-04, Opus subagent, read-only)

Owner question: should track A learn from the upstream issue tree? Verdict: adopt the chapter/chain parent layer and, beyond upstream, GitHub issue dependencies (blocked_by) for readiness; implemented under #159.

Evidence gathered. Writing the report.

## 1. Upstream tree mechanism: native GitHub sub-issues, depth 3

The worked example, `LionSR/MIPStarRE#449` (closed):

```
{"n":449,"state":"closed","title":"Track paper-wide LDT formalization progress",
 "labels":["formalization","2009.12982","chapter-tracking","tracking"],
 "ms":null,"sub":{"completed":24,"percent_completed":100,"total":24}}
GET /issues/449/parent -> 404 "No parent issue found"   # it is a root
```

Its 24 children split into **chapter trackers that are themselves parents** and flat leaves:

```
101|closed|sub=3/3 |Ch 2 — The Test (test_definition.tex)
102|closed|sub=10/10|Ch 3 — Preliminaries (preliminaries.tex)
104|closed|sub=6/6 |Ch 5 — Main Induction Step (inductive_step.tex)
110|closed|sub=14/14|Ch 11 — Pasting (ld-pasting.tex)
422|closed|sub=17/17|Complete formalization of thm:main-formal
451|closed|sub=5/5 |Track remaining bridge-hypothesis-style provisional formalization
589|closed|sub=0/0 |Migrate legacy chapter trackers (#101-110, #422) to native tasklist format
```

Depth 3 confirmed: `#449 → #110 → {#298,#299,#300,#351,#395,#570,#586,#687,#693,#695,#705,#707,#890,#900}`.

The `#449` body states the contract explicitly: *"Native GitHub tracking is configured through issue relationships: the items below are attached as sub-issues of this parent. The body is a human-readable index only."* No milestones exist upstream at all (`/milestones?state=all` is empty); scope is carried by labels (`chapter-tracking`, `tracking`, `2009.12982`, `pasting`, `main-induction`). Upstream currently has **4 open issues** total.

Migration precedent `#589` gives the rationale: *"The tracking workflow only has actionable structure when the issue body contains child references in native tasklist form… Without that, the workflow cannot keep chapter trackers in sync when sub-issues close or PRs merge."*

## 2. What the tree encodes — and what it does not

It encodes **containment** (chapter/paper-section ownership, and therefore file ownership), **size** (`sub_issues_summary.total`), and **status roll-up**. It does **not** encode dependency order or readiness. Decisive evidence: `GET /repos/LionSR/MIPStarRE/issues/449/dependencies/blocked_by` returns `[]` — the endpoint is live, and unused. Prerequisites upstream live in prose, exactly as ours do.

## 3. Their automation consumes roll-up only

`.github/workflows/issue-automation.yml` (the consolidated successor to `tracking-issue-sync.yml`):

```js
async function getParent(issueNumber) { ... parent { number title state labels(first:30){nodes{name}} } ... }
async function subIssueCounts(parentNumber) { ... }
async function noteIfAllResolved(parent, closed, total) {
  await commentOnce(parent.number, 'ready to close',
    'All sub-issues in this tracking issue are complete; the mathematical scope described here is ready to close.');
}
// trackingIssuesReferencingPR: github.rest.issues.listForRepo({state:'open', labels:'tracking'})
```

"Ready" upstream means *ready to close* (all children done), never *ready to start*.

## 4. Our side

`Dengnifer/MIPStarRE-A#47` — labels `qpbt-analysis,proof,tracking`, **`sub_issues_summary` 19/50 (38%)**. We already use native sub-issues, and already have depth 2: `#77` (Magic Square rigidity) is `1/5` over `#101–#105`. `#47`'s body already mandates it: *"Give every proof packet its own GitHub sub-issue, branch, and worktree."*

Gaps: `#122, #126, #146, #156` return `404 No parent issue found` — unattached. And prerequisites are prose only:

- `#106`: "#97 must merge first for the generic conditional-linearity and graph-distribution laws."
- `#110`: "#106 and #107 must merge first for the low-degree and Pauli parameter interfaces."
- `#133`: "#131 supplies the incoming error `3 * ε`… final instantiation waits for #99."

Tooling is already aligned: `issue_new.py --parent` is documented as *"a native sub-issue link (`POST issues/<parent>/sub_issues`)"*; `local/protocols/issues-prs.md:14-16` makes the sub-issue relation normative ("one parent per issue"); `pr_merge.py` gate 7 requires "every issue the PR body closes … has no open sub-issue left". No script anywhere computes ready packets — `grep` over `local/bin/` finds no readiness logic.

## Recommendation

**(a) Adopting the upstream tree alone would NOT automate "ready packets."** Their tree is containment, and their automation only rolls completion upward. Copying it buys accurate `completed/total` per chapter and a self-maintaining index, but an operator would still hand-read our dependency prose. The genuinely valuable finding is separate: `GET /repos/Dengnifer/MIPStarRE-A/issues/106/dependencies/blocked_by` returns `[]`, not 404 — **GitHub issue dependencies are live on our plan and unused.** That, not the tree, is what makes readiness computable.

**(b) Concrete migration, two orthogonal moves.** (1) *Depth*: create per-chain parents under `#47` mirroring `#101–#110` (Games / Test / Observables / Combining / Extraction), then `POST /repos/Dengnifer/MIPStarRE-A/issues/<parent>/sub_issues` with `{"sub_issue_id": <numeric id>}` — the API takes the issue **id**, not its number, so each attach needs a prior `GET`; re-parenting the 50 existing children of `#47` needs `"replace_parent": true`. Attach the orphans `#122,#126,#146,#156`. (2) *Prerequisites*: `POST /issues/<n>/dependencies/blocked_by` with `{"issue_id": <id>}`, transcribed from the existing "must merge first" bullets (`#106←#97`; `#110←#106,#107`; `#133←#131,#99`). The lane launcher then queries: for each open leaf in `#47`'s subtree, read `blocked_by`; **ready iff every blocker is closed**. Keep the prose bullets as commentary only, demoted like upstream's "human-readable index only".

**(c) Costs and risks.** API cost is negligible (~2 calls per attach, ~90 total, against 5000/h), but a polling daemon does one `blocked_by` read per open leaf per tick — cache or ETag it. The real costs are protocol-shaped: a readiness rule is a new normative clause in `local/protocols/issues-prs.md`, requiring an EVOLUTION.md entry; and because it touches `local/bin/` plus protocols it is a workflow-layer PR, so the two-round review rule applies. `blocked_by` is not in `gh_common.py`'s surface, so it becomes a new hard GitHub dependency with no offline fallback (the protocol forbids shadow records). Note we would be moving *ahead of* upstream, not copying them — upstream never adopted dependencies, so the pattern is unproven in this codebase family.

**(d) Verdict.** Adopt the upstream tree shape partially and the dependency edges fully. The chapter/chain parent layer is cheap, matches conventions our protocol and `issue_new.py` already encode, and fixes a real defect — `#47` is a flat 50-child bag with four orphans and a hand-maintained table that has already drifted. But it does not by itself buy automated dispatch; only `dependencies/blocked_by` does, and it is available. Recommend one workflow-layer PR that (i) inserts five chain parents and re-parents all packets, (ii) transcribes the prose prerequisites into `blocked_by` edges, (iii) adds a `ready` subcommand computing closed-blockers, with the prose Dependencies sections explicitly demoted to commentary and an EVOLUTION entry recording the new source of truth.