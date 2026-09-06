<!-- qpbt-decomposition:20260906-independent-extraction -->
Main has split mathematically independent algebra into two source-grounded
packets to honor the owner's useful-concurrency priority:

- #239 exclusively owns tauDotProj_isProj and sum_tauDotProj_eq_one in
  Extraction/Defs.lean, plus the corresponding dot-projector blueprint node.
- #240 exclusively owns marginalPoly_isProjective and the pulled-apart
  observable product-form/Hermitian/involution/corrected-commutation proofs
  in Extraction/Observables.lean and their matching blueprint nodes.

These source-level scopes use merged Pauli/measurement APIs; they do not
construct a global witness or rely on its missing existence theorem. They
run in two separate warmed worktrees from published maina61ee55. Their new
proofs still require actual kernel validation and the normal CI/review gates.

The original #120/#121 packets keep their remaining targets and parent
dependencies. Do not dispatch duplicate writers for these delegated targets.
Integration waits for the actual subpacket merges; global-pair construction
and final source-level extraction are not claimed complete. The completed
scout evidence is scout-120-20260906-02.last.md in primary telemetry; it also
records the stale-cache limitation and independent swap-unitarity route.
