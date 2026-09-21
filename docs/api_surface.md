# API surface

**Empty — the project fills this in.** A short map of the declarations that
worker sessions are expected to reuse, so that a prover or a scout does not
re-derive something the project already has.

`local/personas/prover.md` and `local/personas/scout.md` send sessions here
before they search.

Keep it to one screen per area:

## `<area>` — `<LeanRoot>/<path>/`

| Declaration | What it gives you | Where |
|---|---|---|
| `<name>` | <one line> | `<LeanRoot>/<path>.lean:<line>` |

Rules:

- Only declarations that are stable and meant to be reused. This is not a
  generated index of everything; a full index is what `lake exe checkdecls` and
  the generated documentation are for.
- One line each. If it needs a paragraph, it needs a docstring instead.
- When a declaration listed here is renamed or removed, fix this page in the
  same pull request — a stale entry sends a session looking for something that
  is not there, which is worse than no page.
