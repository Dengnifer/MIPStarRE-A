---
id: "0001"
title: "Tracking: QPBT formalization"
state: "open"
state_reason: null
parent: null
children: ["0002", "0004", "0005", "0006"]
labels: ["formalization", "qpbt-test", "tracking"]
pinned: false
created: "2026-08-30T03:03:48Z"
updated: "2026-08-31T01:34:08Z"
agent_session: null
---

### Mathematical area

<!-- required -->
Which section, theorem family, or construction does this issue organize?

### Mathematical objective

<!-- required: state the theorem family or proof stage, with sources.
     Replace the placeholders with real paths (see `ls references/*/`). -->
Sources:
- `references/<paper-mirror>/<section>.tex:NNN`, label `lem:...`.
  Paraphrase: ...
- `blueprint/src/chapter/<chapter>.tex:NN`, label `lem:...`.

### Sub-issues to attach

<!-- Prose index only. The relationship itself lives in frontmatter: attach a
     child with `issue_new.py --parent <this id>`, which writes both halves. -->
- #
- #

### Mathematical notes

Dependencies, theorem labels, source locations, or order constraints.

## Initial classification

Applied by `local/bin/issue_new.py` (deterministic keyword pass, no model): `formalization`, `qpbt-test`, `tracking`

The deterministic pass added `formalization`; after reviewing the mathematical source, add `scout` to request a Mathlib report.

## Activity

- 2026-08-30T03:06:41Z — PR #0001 (*docs(blueprint): QPBT chapters and dependency graph*) has been opened to address #0002.
- 2026-08-30T19:46:25Z — PR #0001 (*docs(blueprint): QPBT chapters and dependency graph*) has been merged, making progress on #0002. [0/3 sub-issues closed]
- 2026-08-30T19:59:25Z — #0002 (*Blueprint: QPBT chapters and dependency graph*) is now resolved. [1/3 sub-issues closed]
- 2026-08-31T01:34:08Z — PR #0003 (*feat(QPBT): minimal skeleton — thm:pauli statement and definition closure*) has been opened to address #0006.
