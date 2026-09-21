# Comparator validation after recovery, 2026-09-21

MAIN validated the frozen recovered staged tree
`9e681b196dd70bef743de35de5f402237d2a2f72` in the issue-662 worktree.
HEAD remains `d9a380b8`, MERGE_HEAD remains `418e0271`, and PR 663's public
head remains `a942ecb5`. No source edit, commit or publication occurred during
these checks.

## Completed checks

- Canonical `warm-worktree.sh --build`: success, 9326 jobs, 933 seconds,
  finished at 11:03:37 UTC under the machine-wide full-build lock. Log:
  `/home/drx/.cache/mipstarre-dev/logs/worktree-build-20260921T104804Z-682081.log`.
- Direct Lean check of `MIPStarRE/QPBT/Test/AxiomAudit.lean`: success. All
  thirteen audited declarations, including the four comparator targets,
  depend exactly on `propext`, `Classical.choice`, and `Quot.sound`.
- The staged tree hash was unchanged before and after validation.

This is working-tree evidence. Canonical PR CI on a published final commit and
independent review remain required.

## Failed drift checks

Both checks used the recovered branch's checker and configuration with its
freshly rebuilt metadata, through an explicit --root argument.

LDT regeneration differs by one missing blank line before the footer namespace
at expected-file line 761. The requirement is byte-identical LDT output; fix
the assembly boundary and retain the established LDT expected copy.

QPBT regeneration differs in four generated modules:

- Algebra/FieldBasis.lean;
- Test/Completeness.lean;
- Quantum/FiniteMatrix/Basic.lean;
- Quantum/Measurement.lean.

The expected files updated immediately after cache recovery had been extracted
using stale declaration ranges and names from the main snapshot. Comparing
against the fresh build reveals clipped proof bodies and incorrect source
ranges, not merely formatting drift. The branch source itself builds and
passes the axiom audit. The expected tree must be regenerated only from the
fresh metadata and then independently elaborated; the earlier successful
challenge build does not validate this later recovered expected tree.

MAIN preserved a fresh 31-file generated candidate, without changing the
repository, at `/tmp/issue662-postbuild-challenge-20260921T1104Z` using
`--challenge qpbt --write`. It has not yet been elaborated or compared against
the current library. No acceptance is claimed for it.

## Remaining work

Fix the LDT assembly separator, regenerate/review the QPBT expected tree from
the freshly built source, check both generators and elaborate the actual new
challenge. Complete the preserved merge and publish through normal hooks.
Then run canonical CI and fresh review, followed by a comparison against the
coherent current library revision in a disposable independent checkout.
The known private-auxiliary comparison problem, final official landrun/nanoda
verification, merged-main pin and C5 record remain required. Adapt the
completion gate's expected-copy registry to the split tree without reducing
the four-target coverage requirement.
