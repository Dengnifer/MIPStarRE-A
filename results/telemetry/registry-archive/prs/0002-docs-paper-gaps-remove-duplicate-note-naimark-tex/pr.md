---
id: "0002"
branch: "issue-0003-remove-naimark-duplicate"
issue: "0003"
base: "main"
state: "merged"
head_sha: "0c8322c366b63a6a362d75f18f0d0028714d7494"
ci_status: "success"
review_state: "APPROVED"
fix_iterations: 0
auto_fix: true
labels: ["bug", "cleanup", "documentation"]
created: "2026-08-30T05:57:37Z"
merged_commit: "c744e92a45536cb074e51741191dbf5355147ae0"
---

# docs(paper-gaps): remove duplicate note naimark.tex

### Motivation

`docs/paper-gaps/naimark.tex` is byte-identical to
`docs/paper-gaps/naimark-dilation.tex` (same Git blob at the merge base) —
a leftover from the 2026-05 rename of the note. The stage-3 blueprint PR's
CI surfaced it: `texra-blueprint paper-gaps check` rejects the old filename
(empty topic under the `naimark` source key). The `[paper_gaps.aliases]`
entry `naimark = "naimark-dilation"` in `texra-blueprint.toml` already
keeps references to the old slug resolving, so the duplicate file serves
no purpose. See issue #0003.

### Description

Delete `docs/paper-gaps/naimark.tex`. The live note remains
`docs/paper-gaps/naimark-dilation.tex`; no reference to the deleted path
exists in the tree, and no Lean declaration, source-labelled theorem, or
blueprint entry changes.

### Testing

`texra-blueprint --root . paper-gaps check` exits 0 in the branch worktree
(previously: one `::error` for the filename); `local/bin/ci.sh 0002`
conclusion success; `grep -rn "paper-gaps/naimark.tex"` finds no
remaining references.

---
Closes #0003
