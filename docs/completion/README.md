# Completion data

Per-track files that criterion C4 of
[`../../local/protocols/completion.md`](../../local/protocols/completion.md)
reads.

**Empty so far.** One file per track, registered as
`tracks.<name>.leanok_exemptions` in
[`../../local/project.json`](../../local/project.json), conventionally
`docs/completion/<track>-leanok-exemptions.md`.

## The `\leanok` exemption table

C4 requires that every blueprint node under the track is either marked
`\leanok` — formalized and proved — or listed here with a written reason. The
table is the escape hatch, and it is deliberately uncomfortable to use: each row
is a public statement that something the blueprint describes is not formalized.

| Node | Why it is exempt | Revisit when |
|---|---|---|
| `<label>` | `<one sentence: prose-only motivation, a definition duplicated for exposition, a statement the source leaves open>` | `<the condition that would remove the exemption, or "never">` |

Rules:

- A node is never exempt because it is hard, or because nobody got to it. Those
  are open work, and they belong in the tracker, not here.
- "Revisit when" is filled in or the row says `never` and explains why.
- The gate fails when this file is registered and missing, so a track that
  needs no exemptions still ships the file with an empty table and a sentence
  saying every node is marked.
