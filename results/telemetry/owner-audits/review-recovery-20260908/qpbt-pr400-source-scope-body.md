### Motivation
- Recover the useful Z-correlation estimate associated with #387 and distinguish its auxiliary distribution and real-part conclusion from source Claims 17-1 and 17-3 in `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`.

### Description
- Prove `subline_Z_term_near_one` from the existing point, line, and directly indexed subline witnesses. The public statement and universal fourth-root bound are unchanged; its proof uses `C = 2`.
- Preserve the Claim 17-1 real-part proof and the existing Claim 17-2 statement and proof hole. Reuse the completed-pair norm and uniform affine-point support lemmas.
- Keep the source-labelled blueprint claims pending. Separate auxiliary entries explicitly state the direct carrier, completed evaluations, witness hypotheses, and real-part conclusions. Record the missing source distribution transport and complex overlap estimate in `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and the statement-integrity audit.
- Correct the adjoint-square calculation, constants, prefix truncation, ambient-point fiber description, and Z-only module documentation. No source theorem is weakened or supplied with a new bridge assumption.

### Testing
- `lake build MIPStarRE.QPBT.Combining.Claims` and final single-file Claims elaboration passed. The only remaining Claims warning is the original Claim 17-2 proof hole; the first and third estimates use only `propext`, `Classical.choice`, and `Quot.sound`.
- Blueprint rendering after bibliography generation, declaration synchronization, all 1654 declaration links, source-header integrity, paper-facing proof-debt, paper-gap style/reference checks, and installed-hook checks passed. The gap note compiles to PDF with one inherited unresolved citation in its unchanged soundness discussion.
- The global blueprint axiom-closure audit passed: no proof-level `leanok` declaration depends on `sorryAx`.
- Full exact-head CI and independent review are required after publication of the repaired head.
- All prior C1/C3 proof, review, compiler-drain, and publication costs remain charged. B8 remains 13 attempts and 26509 working seconds. This is a distinct bounded source-scope repair allowance.
- Source author exclusions: root `01a076bc-f4ad-7813-805b-c8b4dac71a14`, `01a08101-a7eb-7891-bd8e-2f96cc325389`, `01a08135-8ad7-7de1-808b-091ee156c60a`, and repair author `01a082a2-e8d7-7ab3-a512-e4afeec3b820`.

---
Addresses #387
