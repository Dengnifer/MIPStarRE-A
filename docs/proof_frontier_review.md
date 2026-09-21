# Proof frontier review

**Empty — the project fills this in.** A dated, periodic review of where the
proof effort actually stands: which statements are proved, which are stated and
open, which are blocked on a source gap, and which are blocked on a missing
library result.

`docs/CONTRIBUTING.md`, `docs/anti_patterns.md` and
`docs/pr_review_management.md` link here for the current picture, so the file
exists from the first day.

Shape:

## `<yyyy-mm-dd>` — frontier

| Area | Proved | Stated, open | Blocked | Blocked on |
|---|---|---|---|---|
| `<chapter or subtree>` | `<n>` | `<n>` | `<n>` | `<source gap / library gap / another packet>` |

Then, in prose: the two or three places where the effort is actually stuck, and
what would unstick each one. A frontier review that only counts is a report
nobody acts on.

The mechanical half of these numbers comes from the repository's own audits and
from `scripts/completion_gate.py`; the judgement half is the point of writing
the page by hand.
