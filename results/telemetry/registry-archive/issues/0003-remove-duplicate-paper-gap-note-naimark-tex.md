---
id: "0003"
title: "Remove duplicate paper-gap note naimark.tex"
state: "closed"
state_reason: "completed"
parent: null
children: []
labels: ["bug", "cleanup", "documentation"]
pinned: false
created: "2026-08-30T05:57:34Z"
updated: "2026-08-30T06:17:44Z"
agent_session: null
---

### File(s) affected

`docs/paper-gaps/naimark.tex` (duplicate), `docs/paper-gaps/naimark-dilation.tex`
(live note), `texra-blueprint.toml` (alias registry, unchanged).

### Description

`naimark.tex` and `naimark-dilation.tex` are byte-identical (same Git blob) —
a leftover from the 2026-05 rename recorded in `texra-blueprint.toml`'s
`[paper_gaps.aliases]` (`naimark = "naimark-dilation"`). The checker rejects
the old filename:

```
::error::paper-gap note 'naimark.tex' is not named <key>_<topic>.tex with a
registered source key and a nonempty topic
```

Surfaced by PR #0001's CI paper-gaps step (the parent repository's
path-gated CI apparently never re-ran the whole-tree check after the rename,
so the defect stayed latent).

### Mathematical source, if relevant

Not applicable — no mathematical content changes; the retained note still
documents the Naimark-dilation discussion for
`references/ldt-paper/orthonormalization.tex:36-63`.

### Expected behavior

Exactly one note file, `naimark-dilation.tex`; old references resolve via
the alias; `texra-blueprint --root . paper-gaps check` exits 0.

### Lean toolchain

`leanprover/lean4:v4.32.0` (irrelevant to this documentation fix).

## Initial classification

Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): No automatic label was clear from the title or body.

## Activity

- 2026-08-30T06:17:44Z — Issue closed as completed — closed by the merge of PR #0002.
