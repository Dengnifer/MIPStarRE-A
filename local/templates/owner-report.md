# Template — a report to the owner

Reports are in plain everyday language, outcome first. The owner wants to know
what is happening and whether anything needs them, not how the machinery works.

**Say** "passed the automatic checks", not "CI green on the exact head";
"waiting for the independent review", not "no review bound to this head";
"out of date because the main branch moved", not "stale". No script names, file
paths, gate numbers or commit ids unless they ask. Few numbers. Offer detail
instead of including it.

**Length.** A status report is five to eight lines. A closing report is at most
fifteen. If it is longer, it is a document, and the owner did not ask for one.

**When.** At stage boundaries, on a pause, on a resume, when something needs
them, and when the project is done. Not on a schedule.

---

## A. Status report

```
{{ONE_SENTENCE: what the state is, in the owner's terms}}

- Running: {{WHAT_IS_RUNNING, in plain words}}
- Done since last time: {{ONE_OR_TWO_THINGS}}
- Stuck: {{WHAT_AND_WHY_IN_EVERYDAY_WORDS, or "nothing"}}
- You: {{WHAT_THE_OWNER_MUST_DO, or "nothing for now"}}
```

## B. Request for help — this goes at the TOP, before anything else

Two to four lines. What you need, the exact steps or the single word to reply,
when, and what happens if they do nothing.

```
{{WHAT_I_NEED, one line}}
{{THE_EXACT_STEP: the command to run in a real terminal, what to type, or the
single word to reply}}
{{WHEN_IT_IS_NEEDED}} — {{WHAT_HAPPENS_IF_THEY_DO_NOTHING}}
```

Ask only when the risk goes beyond the project's development: the owner's
files, the machine or its accounts, spending money, acting outside this
repository. Everything inside project development is decided, done, recorded
and mentioned in one line.

## C. Closing report

```
{{ONE_SENTENCE: where the project ended up}}

- What is finished: {{PLAIN_LIST}}
- What is left: {{PLAIN_LIST, with an honest estimate or "unknown"}}
- What is running now: {{OR "nothing — everything has stopped cleanly"}}
- Where it is written down: {{ONE_POINTER, e.g. "the progress issue"}}
- To pick it up again: {{ONE_SENTENCE}}
```

<!-- EXAMPLE — invented, for shape only.

A. Status report

The main theorem is proved and merged; what is left is packaging.

- Running: one session driving the work and two helpers, all healthy.
- Done since last time: the last two proof gaps closed, and the independent
  re-check of the statement now accepts three of the four headline results.
- Stuck: nothing. The fourth result is waiting for a rebuild that takes about
  an hour.
- You: nothing for now.

B. Request for help

I need permission to create the second GitHub repository that holds the
independent statement check.
Reply "yes" or "no".
Needed before I can finish; without it everything else still completes, but the
project cannot be declared done.

C. Closing report

Everything has landed cleanly and nothing is running.

- What is finished: all proofs, the automatic end-of-project checks, and the
  independent re-check of every headline statement.
- What is left: attaching the snapshot to a submission, which is yours to do.
- What is running now: nothing — everything stopped cleanly at the time you set.
- Where it is written down: the progress issue has the final summary.
- To pick it up again: say the word and I will start a session from the last
  section of the project's own state file.

-->
