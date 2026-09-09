# PR269 preservation across the actual PR195 base

Session: `orc-257-20260906-05`, continuing the existing issue257 episode.
Repaired parent: `6ca89e8280e7b41c5950d252fc8d962890ab5e80`.
Incoming PR195 merge: `928328ff4d45e5fdc2844b120329a2c241a3a58a`.
Previous merge base: `b7705e02ef143e605981839009646c509f7df2ca`.
Primary `gh_common.py` independently confirmed PR195 merged at the incoming
SHA and PR269 open at the repaired parent before this refresh.

## Exact source and test preservation

The staged merge entries below equal the repaired parent's entries, including
file modes. The two shell scripts have mode `100755`; all other entries have
mode `100644`.

| Path | Preserved Git blob |
| --- | --- |
| `local/README.md` | `74fc4486c2c45dcc5aa9b57b39a83ba6e6487cf1` |
| `local/bin/account_router.py` | `9ab621f8495e73e57b4b3545cd25c9d4686be8a1` |
| `local/bin/dispatch.sh` | `15cd10bced3b4a4641d0a32cd473d9791b63209b` |
| `local/bin/review.sh` | `b9c1c8a55fc0b13bae29e0c13825f4e4e684b4d2` |
| `local/bin/useful_queue.py` | `8cd494cd275ae4c50402386e2c35cf6730333a91` |
| `local/briefs/257-useful-admission-queue.md` | `9da93b9f7269438dec2337a4ebb4d9c1ba8994c6` |
| `local/protocols/EVOLUTION.md` | `07e73103e05fadadd54a67a08e1ffb935680eefd` |
| `local/protocols/useful-queue.md` | `0567c941ad85e15f1ab07cf5be570bd5b76097e0` |
| `scripts/tests/test_dispatch.py` | `8a075edf67a382a49f842b36fb1af53dc37d0ddd` |
| `scripts/tests/test_github_workflow.py` | `744c614ac328457f2224219ab1afda33f97f3549` |
| `scripts/tests/test_useful_queue.py` | `a8262e43830f7e4a539437b356d2c4169e00b730` |

The complete nontelemetry Git patch, excluding `results/telemetry/**`, is
byte-identical before and after the base refresh. Its SHA-256 is
`814f233b4d6c6518af061d0ac3a4cbb83794de4e6b00924782fa330eeb1f026c`.
The cumulative patch remains 970 additions + 29 deletions = 999 lines.
No implementation change or infrastructure override was made.

## Incoming source and history

All seven incoming-only changed paths equal PR195's blobs, with mode `100644`:

| Path | Incoming Git blob |
| --- | --- |
| `MIPStarRE/QPBT/Observables/WinImplications.lean` | `2e0184e2a09b2bc2d2d62afd33135fad619a01e0` |
| `MIPStarRE/QPBT/Observables/WinImplications/Approx.lean` | `44c3b4449554174fc437a68010d067d904204950` |
| `MIPStarRE/QPBT/Observables/WinImplications/ApproxLines.lean` | `348ea9cd9a4a2c2ddb0b75a0da536eac265212b9` |
| `MIPStarRE/QPBT/Observables/WinImplications/Commuting.lean` | `659fb4229fde15915f8821d196223a34b705d045` |
| `MIPStarRE/QPBT/Observables/WinImplications/Interchange.lean` | `009bd276e3c71379cfea2a2c2de00746b9914002` |
| `MIPStarRE/QPBT/Observables/WinImplications/MagicSquare.lean` | `bd149e3fb2ac14f7c983648ac686f05ee85da075` |
| `blueprint/src/chapter/ch14_qpbt_observables.tex` | `11f989238a0968429c80448b466b49487b72dddf` |

The only merge conflict was `results/telemetry/events.md`. Each parent's
complete sequence of byte-preserving lines is an ordered subsequence of the
resolved file. Every other existing telemetry blob equals both parents.
The pending-index merge-loss guard passed. This document adds evidence only.
The full telemetry-inclusive patch changes, so source preservation is not a
claim of automatic review carry-forward eligibility.

## Accounting and handoff

The original episode remains cumulative: failed sessions -01/-02, the original
577-test run, consolidated 555-test runs, session -03, and F1-F3 repair session
-04 are retained. Primary session registry rows 792/809/812 and the prior
`orc-257-20260906-04-handoff.md` provide the historical accounting. The nominal
two-hour window was already exceeded; this session performs only the requested
bounded base refresh, checked publication, and detached exact-head CI.

Publication and CI outcomes must be read from this session's final handoff and
the canonical CI manifest/statuses. CI uses the normal 14400-second lock wait.
Main owns the second independent normal review and terminal disposition after
green CI. This session starts no model review, subagent, merge daemon, deployment,
or provider probe and does not reset time, review, or source-line budgets.
