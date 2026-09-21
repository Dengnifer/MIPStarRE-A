# Comparator review findings and repair, 2026-09-21

Independent review [5266355928](https://github.com/Dengnifer/MIPStarRE-A/pull/663#pullrequestreview-5266355928)
is bound to PR663 at `a534c7f97ba34fd561ae03134f90b81ee4e395c1` and requests
changes for two findings. The reviewer checked the complete final diff,
including its PR660 parent. It confirmed the four required raw-effect target
statements, the31-file Mathlib-only challenge and its four intended target
proof holes, and93 focused tests. These facts do not resolve either finding
or establish official comparator acceptance.

## Original LDT Baseline

The original byte-preservation requirement concerns the whole PR. MAIN
independently read the fixture blobs and obtained:

| Fixture source | Bytes | SHA-256 |
|---|---:|---|
| Published main and PR660 parent418e0271 | 41017 | `cbe5642bb88db75f86bd79936896e684aa407a02108d8259ead71a0738783e73` |
| PR663 at a534c7f9 | 41328 | `02959aacbc4493c29a5c1dd5c22e7d56b8b4c595a1c56a6fbf5e0f2b20e68080` |

Earlier publication receipts said that LDT was unchanged when comparing the
intermediate branch state with its publication. That was too narrow to prove
the original contract. The existing global QPBT alignment instances had
already changed the LDT closure earlier in the branch. A passing regeneration
check against that changed fixture is not evidence of baseline preservation.
Retain the earlier observations as history with this scope correction.

The repair removes the two unnecessary global instances from
`MIPStarRE/Quantum/FiniteMatrix/Basic.lean`. MAIN independently verified that the
repaired file is byte-identical to PR660's file. The author reported a clean
single-file Lean check. The staged source tree is
`512a2d13b4e2329c10e02e029d5d1a0ee8f295bd`, with MIPStarRE subtree
`587d10e0d77526bbc80c85f3f56d26ab9939dc70`. The source-ready receipt is
`/tmp/main-pr663-review-fix-source-ready-20260921.json`.

MAIN verified the frozen Lean/build inputs and started the canonical locked
full build at12:13:48 UTC, without forcing a cache reset or writing the hot
cache. Its detached wrapper PID was1036629, verified live while modules built.
The wrapper checks that Lean/build inputs remain equal to the frozen tree
before and after the build. Logs:

- `/tmp/main-build663-ldt-restore-20260921.log` and matching `.exit` receipt.
- `~/.cache/mipstarre-dev/logs/worktree-build-20260921T121348Z-1036642.log`.

The build is still running at this record. Fresh-metadata regeneration must
restore the exact original LDT bytes and regenerate the QPBT tree before
publication. An independent baseline regression is being prepared. No green
CI from a534c7f9 is transferred to the unpublished repair.

## Documentation Finding

The checked-in comparator documentation still describes the historical
two-target result as current, gives obsolete closure counts and names the
removed Python configuration module. The repair must state all four targets
and the split layout, preserve any historical result only with its exact pin
and scope, and say that all-four closure equality, private-auxiliary equality,
official real-landrun/nanoda acceptance and the merged-main pin are pending.

## Unexpected Model On Resume

MAIN attempted to reuse the knowledgeable publication author through
`resume_agent`. The original thread had been Sol/ultra, but its new turn at
12:09:41.627 UTC was recorded as Astra/ultra. The requested instruction to retain
Sol did not preserve the tool's model override. The runtime compatibility check
caught this; MAIN closed the thread and observed its shutdown at12:11:33.149.
No retrospective hardness justification is assigned.

The111.522-second continuation used the same space-3 key and the one authorized
native slot. Its useful staged source repair was preserved. Observed usage is
the new cumulative counter minus the previous task's terminal counter, retaining
the previous1182.847 seconds and all other costs without double counting. The
last usage observation preceded shutdown by1.692 seconds, so any unreported
final usage remains unknown. Full measurements are in `sessions.jsonl`.

The replacement is a fresh explicit Sol/ultra thread,
`01a0c3e2-8639-7681-ae10-9707a3e0076a`, whose actual runtime model was checked.
It owns documentation and Python test preparation only; Lean/build inputs stay
frozen. Its start is12:13:17.818 UTC, checkpoint12:19:17.818, and deadline
12:25:17.818. It will return rather than occupy the model slot waiting on the
build. The queued packaging repair can then use that slot. Future Sol work must
use a fresh explicit-model spawn unless model-preserving resume is actually
supported and verified; an old thread's original model is insufficient evidence.

## Successful Rebuild And Temporary Regeneration

The locked build finished at12:27:43 UTC:835 seconds,9326 jobs, exit0. The
before/after source guard passed. MAIN then checked all13 QPBT standard-axiom
assertions and the blueprint audit:1837 declarations passed, none failed, with
no proof-level `sorryAx` dependency.

MAIN regenerated temporary candidates from the fresh compiled metadata between
12:31:10 and12:31:34 UTC. Both write-only generator calls passed and the wrapper
returned0. The candidate directory is
`/tmp/issue662-reviewfix-postbuild-20260921.GwMDUg`, with a31-file QPBT tree and
a41017-byte LDT file whose hash is exactly the original `cbe5642b...e73` above.
This supplies the previously missing whole-PR baseline evidence. It does not
yet update the checked-in fixture, elaborate the new QPBT candidate or publish
the repair. Log: `/tmp/main-regenerate663-review-fix-20260921.log`.

The documentation helper finished after487.332 seconds and was closed. Its
33/34 preparation-test result correctly left the original-baseline test failing
until the generated file is adopted. It changed only the two comparator
documents and the existing drift-test file. Its final step suggesting that all
publication wait for official merged-main verification is clarified by MAIN:
source repair publication, CI, independent review and service merge precede
the final official verification. No acceptance requirement is removed.

The sole current native author is now
`01a0c3ee-22f8-7c30-94db-3445834aa131`, verified Sol/ultra, fixing PR659's
domain-suffix scanner defect. It started12:25:58.837 UTC, with checkpoint
12:35:58.837 and deadline12:40:58.837. The prepared663 publication task waits
for that slot. All current and predecessor costs remain in `sessions.jsonl`.
