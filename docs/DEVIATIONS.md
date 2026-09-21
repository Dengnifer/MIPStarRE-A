# Deviations from the printed source

**Empty — the project fills this in.** This page says, in one place and in
plain mathematical language, where the formalization departs from the papers it
cites, and why. It is the companion to the per-note evidence under
[`paper-gaps/`](paper-gaps/) and to the register those notes are summarized in.

Criterion C7 of
[`../local/protocols/completion.md`](../local/protocols/completion.md) requires
it (a track registers it in `artifact_files`), and criterion C6 holds it to the
truth.

Write one section per deviation, in this shape:

## `<blueprint label>` — `<short title>`

- **What the paper prints.** The statement as printed, quoted where the exact
  wording matters, with its locator.
- **What the formalization states instead.** The Lean statement, in words and
  then as a declaration name.
- **Why.** One of: the printed statement is false as printed (link the gap
  note); the printed proof does not establish it (link the note); a faithful
  formal encoding requires it; a definition in the source is ambiguous and the
  formalization fixes one reading.
- **What it costs.** Whether every downstream use in the paper still goes
  through, and where that was checked.

Kinds of deviation that must be listed even when they feel harmless:

- an existential constant that the paper leaves implicit and the formalization
  quantifies explicitly;
- a hypothesis the paper states once for a section and the formalization
  repeats on each statement;
- a bound whose shape differs from the printed one, even when it is equivalent;
- any statement kept as a definition that *states* a printed claim without
  asserting it, because the claim is not established.

An empty section here with a non-empty gap register is a contradiction; a
reviewer will find it.
