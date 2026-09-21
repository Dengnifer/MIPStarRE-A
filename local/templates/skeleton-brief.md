# Template — a skeleton brief

A **skeleton brief** is the document that turns one chapter of the blueprint
into a binding issue contract before anybody writes Lean. It is written by one
worker, reviewed independently, adjudicated by the main session, and only then
turned into an issue. Stage 4.2 of
[`../protocols/bootstrap.md`](../protocols/bootstrap.md).

The brief's job is to make the implementation boring: every declaration named,
every statement fixed, every allowed hole listed. A brief that leaves the
statement to the implementer produces a pull request nobody can review against
anything.

Write it to `local/briefs/<issue>-<slug>-brief.md`.

---

## Template

```markdown
# Skeleton brief — {{CHAPTER_LABEL}}: {{CHAPTER_TITLE}}

**Track** {{TRACK}} · **Lean root** {{LEAN_ROOT}} · **Blueprint chapter**
{{CHAPTER_FILE}} · **Source** {{SOURCE_LOCATORS}} · **Issue** {{ISSUE}}

## 1. Scope

{{ONE_PARAGRAPH: what this packet delivers and what it deliberately does not}}

## 2. Blueprint nodes covered

| Node | Kind | Source locator | Lean declaration | May be `sorry`? |
|---|---|---|---|---|
| `{{NODE_LABEL}}` | {{KIND}} | `{{LOCATOR}}` | `{{LEAN_NAME}}` | {{YES_NO}} |

Every node in this table gets a `\lean{}` link in the chapter; every node that
stays unproved keeps `\notready` until its Lean side exists.

## 3. Module layout

| Module | Contents |
|---|---|
| `{{LEAN_ROOT}}/{{SUBPATH}}/Defs.lean` | {{WHAT}} |
| `{{LEAN_ROOT}}/{{SUBPATH}}/Theorems.lean` | {{WHAT}} |

New imports allowed: {{IMPORTS}}. No module in this packet may narrow an
import that a statement closure depends on.

## 4. Statements, exactly

For each declaration, the signature it must have, in Lean, with the hypotheses
written out:

```lean
{{SIGNATURE}}
```

{{WHY_THIS_SHAPE: the source sentence it encodes, quoted where the wording
matters — the quantifier order, a side condition, an exponent}}

## 5. Definitions this packet must introduce

| Name | What it is | Source | Why the library does not already have it |
|---|---|---|---|
| `{{DEF}}` | {{WHAT}} | `{{LOCATOR}}` | {{WHY}} |

## 6. Faithfulness constraints

- {{CONSTRAINT: a hypothesis that may not be strengthened, a conclusion that
  may not be weakened, a definition that must match the source's}}
- No bridge, residual, witness or hypothesis bundle may be added to make a
  statement provable. If a statement cannot be stated faithfully, stop and
  report; do not condition it.
- Where the source is wrong, the corrected statement is used and
  `docs/paper-gaps/{{GAP_KEY}}-{{SLUG}}.tex` is written in the same pull
  request.

## 7. Acceptance criteria

- [ ] `lake build` green.
- [ ] `lake exe checkdecls blueprint/lean_decls` resolves every `\lean{}` of
      section 2.
- [ ] Every declaration of section 4 exists with exactly that signature.
- [ ] Every hole is a `sorry` in proof position; no project `axiom`, no
      `native_decide`, no `unsafe`, no `@[extern]`.
- [ ] Each declaration's docstring names its blueprint label and its source
      locator.
- [ ] {{PACKET_SPECIFIC_CRITERION}}

## 8. Out of scope

{{LIST: what a reviewer must not ask for in this pull request, and where it
belongs instead}}

## 9. Budget

At most {{HOURS}} hours of worker time and {{LINES}} changed lines. Reaching
either limit means stop, commit what stands, record the state and report — not
push through.
```

<!-- EXAMPLE — invented, for shape only.

# Skeleton brief — ch04: tail bounds for weakly dependent sums

**Track** main · **Lean root** WeakDep · **Blueprint chapter**
blueprint/src/chapter/ch04_tail_bounds.tex · **Source**
references/wd-paper/04_tail_bounds.tex:1-338 · **Issue** 41

## 1. Scope

State the three tail bounds of section 4 and the mixing coefficient they are
phrased in, with every proof `sorry`. No proofs, no inequalities specialized to
the paper's later parameter choices; those are packet 42.

## 2. Blueprint nodes covered

| Node | Kind | Source locator | Lean declaration | May be `sorry`? |
|---|---|---|---|---|
| `def:alpha-mixing` | definition | `…/04_tail_bounds.tex:22-39` | `WeakDep.alphaMixing` | no (it is a definition) |
| `lem:block-decoupling` | lemma | `…/04_tail_bounds.tex:74-121` | `WeakDep.block_decoupling` | yes |
| `thm:tail` | theorem | `…/04_tail_bounds.tex:198-241` | `WeakDep.tail_bound` | yes |

## 4. Statements, exactly

```lean
theorem WeakDep.tail_bound {n : ℕ} (X : Fin n → Ω → ℝ) (hb : ∀ i, ∀ ω, |X i ω| ≤ 1)
    (α : ℕ → ℝ) (hα : WeakDep.alphaMixing X α) (t : ℝ) (ht : 0 < t) :
    ℙ {ω | t ≤ |∑ i, X i ω|} ≤ 2 * Real.exp (-t ^ 2 / (4 * n)) + n * α 1
```

The `n * α 1` term is the paper's, not a convenience: section 4's proof pays it
once per block and the printed statement keeps it (line 233). Do not drop it and
do not replace `α 1` by a supremum.

## 7. Acceptance criteria

- [ ] `lake build` green.
- [ ] The three declarations exist with exactly the signatures of section 4.
- [ ] Every hole is a `sorry` in proof position.
- [ ] `alphaMixing` is a definition with no `sorry` anywhere in its closure.

## 9. Budget

At most 3 hours and 400 changed lines.

-->
