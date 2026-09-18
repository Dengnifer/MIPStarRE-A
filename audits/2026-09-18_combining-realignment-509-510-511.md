# Combining realignment: the three `Apply.lean` extended-line sites (509/510/511)

Date: 2026-09-18. Branch `issue-511-combining-error-realignment-20260918`.
Scope: `MIPStarRE/QPBT/Combining/Apply.lean`, the gap note
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`, the gap register, and the
blueprint chapter `blueprint/src/chapter/ch15_qpbt_combining.tex`.

Authorized by the main session's dispositions for issues 511 and 510 recorded in
`~/.cache/mipstarre-dev/watchdog/opus-requests.txt`, and by the meta session.
This document is an audit of a statement change, not a claim that the source
lemma has been proved.

## What the three sites were

All three carried `sorry` on `github/main` at `2e253049`.

- `exists_extendedLinesWitness_ofPointsWitness` (line 73, `sorry` at 80), issue
  509, closed by its obstruction pull request without a proof.
- `exists_extendedLinesWitness` (line 107, `sorry` at 115), issue 510, likewise.
- `exists_extendedLinesWitness_established_ofPointsWitness` (line 149, `sorry`
  at 157), issue 511, open, docstring carrying an explicit `**Unfaithful:**`
  marker.

The first and the third were false as stated, for the same reason: each chose a
single polynomial line-error function and then quantified over an *arbitrary*
supplied scalar point error `δQ` and over every point witness at that error,
while the line error in the conclusion does not mention `δQ`. The refutation is
the deterministic quadratic point family at `ε = 0` given in prose at
`docs/paper-gaps/qpbt_combined-lines-error-term.tex:214-320`: its axis-line
defect stays bounded below as `q` grows, while any `IsPolyErr₂` bound tends to
zero there. The second was not refuted; what blocks it is the printed error
form itself.

## The realignment table

| declaration | old statement | new statement | paper locator | relation to paper | callers | leanok placement |
| --- | --- | --- | --- | --- | --- | --- |
| `exists_extendedLinesWitness_ofPointsWitness` | `∃ δcombine, IsPolyErr₂ δcombine ∧ ∀ P ε δQ S (points : CombinedPointsWitness S δQ), Nonempty (ExtendedLinesWitness S points (δcombine (m²ε) (md/q)))`; `sorry` | **removed** | `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034` (`lem:qld-4-13`) | was false as stated (arbitrary `δQ` omitted from the conclusion); the printed error expression it carried is also carried by `exists_extendedLinesWitness`, so nothing about the paper is lost | none in `MIPStarRE`, none in `blueprint`; only historical `audits/` prose and the gap note, all retained | had none, and none is added |
| `exists_extendedLinesWitness` | `∃ δQ, IsPolyErr δQ ∧ ∃ δcombine, IsPolyErr₂ δcombine ∧ ∀ P ε S, ∃ points : CombinedPointsWitness S (δQ ε), Nonempty (ExtendedLinesWitness S points (δcombine (m²ε) (md/q)))`; `sorry` | **unchanged**, `sorry` retained as a source-gap declaration; docstring rewritten to say so and to name issue 598 | same | the printed error form `poly(m²ε, md/q)`, read in the `IsPolyErr₂` sum sense; established by neither source route | none in `MIPStarRE`; blueprint node `lem:qld-4-13` | `lem:qld-4-13` carries **no** `\leanok` and keeps `\notready` — unchanged |
| `exists_extendedLinesWitness_established_ofPointsWitness` | `∃ C, 0 < C ∧ ∃ δcombine, IsPolyErr₂ δcombine ∧ ∀ P ε δQ S (points : CombinedPointsWitness S δQ), Nonempty (ExtendedLinesWitness S points (C·m·δcombine ε (md/q)))`; `sorry` | takes `(δQ : ℝ → ℝ) (hδQ : IsPolyErr δQ)` first, then `∃ C, 0 < C ∧ ∃ δcombine, IsPolyErr₂ δcombine ∧ ∀ P ε S (points : CombinedPointsWitness S (δQ ε)), Nonempty (ExtendedLinesWitness S points (C·m·δcombine ε (md/q)))`; **proved** | same; error form from the first printed route, `14_..._test.tex:1140-1173` (Claims 17-1 to 17-3) | formalization-only conditional auxiliary; not the source lemma — the error form is the established `C·m·poly(ε, md/q)`, and the carrier is the directly indexed one | none on `main` before this change; after it, `exists_extendedLinesWitness_established` | new conditional node `lem:qld-4-13-established-given-points` with statement-level and proof-level `\leanok`, for the conditional assertion only |
| `exists_extendedLinesWitness_established` | as on `main`, proved inline | **statement byte-identical**; proof now supplies the point family and applies the repaired conditional companion | same | unchanged | `exists_globalPairWitness` (`Apply.lean`), unchanged | `lem:qld-4-13-established`, both marks, unchanged; its proof `\uses` now names the conditional node |

## The domain repair

The repaired signature is the issue-389 repair one level up. The precedent is
`exists_combinedLinesWitness_ofPointsWitness`
(`MIPStarRE/QPBT/Combining/Lines.lean:93`), which after issue 389 takes
`(deltaQ : ℝ → ℝ) (hdeltaQ : IsPolyErr deltaQ)` before choosing the line error
and assumes `points : CombinedPointsWitness S (deltaQ ε)`. The repaired
extended-line auxiliary has exactly that shape.

Two properties of the repair matter for faithfulness.

1. The point error now enters the hypothesis through `deltaQ ε`, so the
   counterexample family is no longer in the domain: a deterministic quadratic
   point family at zero strategy error is not `IsPolyErr`-controlled in the
   required sense. The statement is no longer false for the reason recorded in
   the gap note.
2. The established dimension factor `C * m` is **kept explicit** in the
   conclusion. It is not absorbed into `deltaCombine`, and the proof instantiates
   `C := 1`, so the declaration asserts exactly the bound the first route
   delivers, with the `m` prefactor visible.

No new estimate was introduced. The proof is the proof that already stood behind
`exists_extendedLinesWitness_established` on `main`, with the two steps that
construct the point family removed: `exists_combinedLinesWitness_ofPointsWitness`
for the paired lines, `subline_joint_overlap_near_one_at` and
`exists_combining_polynomial_bound` for the scalar collection,
`exists_subLineWitness` for the subline witness, and both opposite-placement
comparisons. `exists_extendedLinesWitness_established` is then a four-line
derivation from the repaired conditional form, which is why its statement did not
have to change and its consumer did not have to be touched.

## The deleted declaration

`exists_extendedLinesWitness_ofPointsWitness` was removed, not repaired, because
the repair makes it a duplicate. Applying the same domain repair to it leaves a
statement that differs from the repaired
`exists_extendedLinesWitness_established_ofPointsWitness` only in the error
expression, and the printed error expression it carried is already carried by the
existential declaration `exists_extendedLinesWitness`, which is retained. Keeping
both would have produced two supplied-point auxiliaries with the same domain, one
of them unprovable for a reason that has nothing to do with the supplied points.

The caller check preceding the removal was
`git grep -n -w exists_extendedLinesWitness_ofPointsWitness github/main -- MIPStarRE blueprint docs audits scripts local`.
It returns: the declaration itself; three `audits/` documents from 12 and 14
September; and one paragraph of the gap note. No Lean declaration and no
blueprint node consumed it. The `audits/` documents are historical records and
are left untouched. The gap note paragraph — the refutation and the provenance —
is retained in place, with its tense corrected and a forward reference to the new
realignment section.

## The printed error form stays open

This is the part that is *not* resolved, and it is recorded as such rather than
worked around.

`exists_extendedLinesWitness` keeps the printed error form `poly(m²ε, md/q)` and
keeps its `sorry`. Of the two options the main session authorized for issue 510,
this branch takes the second — keep the printed-form declaration as a
sorry-carrying source-gap declaration and route Lean consumers through the
established form — because it is the option with **no** downstream churn: every
Lean consumer already routed through `exists_extendedLinesWitness_established`
(`exists_globalPairWitness` is the only one), so nothing had to be rerouted, and
the blueprint node `lem:qld-4-13` keeps its `\lean{}` tag, its `\notready`, and
its absence of `\leanok`. Restating the declaration at the established error
would instead have made it a duplicate of `exists_extendedLinesWitness_established`,
would have removed the printed assertion from Lean entirely, and would have forced
the source-labelled blueprint node to point at a statement that is not the
source's.

The source theorem is therefore neither marked proved nor hidden by deletion. The
obstruction `not_exists_combining_quarter_power_bound`
(`MIPStarRE/QPBT/Combining/ErrorObstruction.lean:36`) still blocks absorbing the
first route's `m·ε^(1/4)` term into the printed arguments, so a different
estimate would be required; no speculative estimate was begun here.

Live tracking is restored by the new issue 598, "source gap: printed
combined-lines error form (509/510)". Issues 509 and 510 stay closed and are not
reopened; 598 states what remains open, what is already settled, and what would
count as done. It is referenced from the gap note, from the gap register row, from
the docstrings of `exists_extendedLinesWitness` and of both established
declarations, and from the blueprint remark `rem:qld-4-13-source-defects` and the
comment block of `lem:qld-4-13`.

## Downstream audit

Consumers, by `git grep` over `MIPStarRE`, `blueprint`, `docs`, `audits`:

- `exists_extendedLinesWitness_established` is consumed by `exists_globalPairWitness`
  (`Apply.lean:263` on `main`). Its statement is unchanged, so this consumer is
  unchanged and its proof was not edited.
- `exists_globalPairWitness` is consumed downstream of this chapter; unchanged.
- The two removed/repaired auxiliaries had no Lean consumers at all.
- No `leanok` was added for anything unproved. The `\leanok` placements touched
  are: the new conditional node `lem:qld-4-13-established-given-points` (statement
  and proof), which is proved; `lem:qld-4-13-established`, whose marks and
  statement are unchanged; and `lem:qld-4-13`, which continues to carry no mark.

Blueprint honesty check: `lem:qld-4-13` still states the source lemma with the
printed error form, still carries `\notready`, and its remark now says in one
sentence that the printed form is an open source gap tracked by issue 598 and that
every formalized consumer uses the established form. The new conditional node
states its hypothesis (a polynomially controlled point family) and says in its own
text that the unrestricted form is false, so the node cannot be misread as covering
arbitrary supplied points.

## Proof integrity

- No `sorry`, `admit`, `axiom`, or `native_decide` is introduced. The single
  remaining `sorry` in the file is the retained source-gap declaration
  `exists_extendedLinesWitness`, at `Apply.lean:80` after the edit, with the gap
  wording in its docstring.
- `#print axioms` was run from a probe file outside the worktree on every newly
  proved and every re-proved declaration; results are in the pull request body.
- No statement was weakened to make anything pass. The one statement that changed
  was strengthened in its hypothesis and unchanged in its conclusion apart from the
  substitution of `deltaQ ε` for the free `δQ`; the change moves it *towards* the
  paper, which supplies the point family from `lem:qld-4-10` with
  `δQ = poly(ε)` and retains that error through Claim 17-1.

## Coordination

Open pull request 587 ("Preserve finite quadratic POVM obstruction", branch
`issue-511-preserve-quadratic-obstruction-20260918`) touches
`MIPStarRE/QPBT/QuadraticPointObstruction.lean`, `MIPStarRE/QPBT.lean`, an audit,
and the same gap note. Its gap-note hunks rewrite lines 291-313 of the version on
`main`, the paragraph on what is independently verified in Lean. None of the hunks
on this branch fall inside that range or within three lines of it: the nearest are
at 225-228 and at 486. Its Lean files are not touched here, and its pending
integration is not affected — the realignment does not depend on it and does not
displace it.
