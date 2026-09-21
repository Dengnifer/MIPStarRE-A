## {{TIMESTAMP}} — {{TITLE}}

<!-- Appended to the running handoff file (never committed). Two writers use this
     form: the operator, when it changes the layout or resumes the project, and the
     outgoing main session, when it stands down. Fill every heading or write "none";
     an empty heading reads as "forgotten", "none" reads as "checked". -->

- Why this section exists: {{REASON}}
- Layout from here on: {{LAYOUT}}

### State of the work

- In flight, one line each: the item's number, its branch, the commit head, the worktree it lives in, and whether it is pushed.
- Reviewed / gated / staged / waiting for a fresh review: which item is in which of those states.
- Local work that is NOT pushed anywhere: where it is and what would be lost.
- Detached jobs still running: process id, log file, and what their result is for.
- Claims still held, and by whom.

### Judgement

- Decisions that are open, and what the outgoing session would decide.
- What is known to be broken or uncertain, stated plainly.
- The first two tasks the next session should pick up, most important first.

### Layout and limits

- Which key carries the main session, which keys carry workers, and the caps in force.
- What must NOT be done (an interlock, a quiet window, a retired key), and why.
