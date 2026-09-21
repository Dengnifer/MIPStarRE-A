# EVOLUTION — the protocol-amendment ledger

Every change to a file under `local/protocols/` or to `AGENTS.md` appends an
entry here. This file is the primary record of how this project's working rules
changed and why; it is research data, and it is append-only.

## The rule

An amendment needs a **trigger**: a dated incident in
`results/telemetry/events.md`, a telemetry observation, or a decision by the
owner. No trigger, no amendment. The procedure is
[`meta.md`](meta.md) §"Amendment procedure"; the short form is:

1. record the friction in `events.md` (symptom → diagnosis → fix → lesson);
2. draft the protocol edit;
3. append an entry here with the four fields below;
4. commit the edit and this entry together;
5. when the change alters a guard — a lock, a cap, a gate, a kill switch —
   update every enforcement point in the same commit.

Entry form:

```
## YYYY-MM-DD — <short title>

**Trigger.** <the events.md entry, telemetry line or owner decision>
**Change.** <files touched + what changed, in a sentence or two>
**Expected effect.** <what should be different afterwards, observably>
**Outcome.** <filled in later, when it is known; "pending" until then>
```

A protocol is normative until it is amended. An agent that finds one wrong does
not deviate silently: it follows the protocol, or it stops, and it proposes the
amendment.

---

## 2026-09-21 — kit extraction: this repository becomes paper-agnostic

**Trigger.** Owner decision, 2026-09-21: turn the machinery of a finished
formalization project into a kit that can be pointed at any paper.

**Change.** The repository was stripped of one project's mathematics, records
and identity, and the reusable half was made configurable:

- the paper's Lean sources, blueprint chapters, paper mirrors, audits, briefs
  and run records were removed; the append-only telemetry registries kept their
  paths and lost their rows;
- project identity moved into `local/project.json` (library name, Lean root,
  track, repository slugs, cache root, issue numbers, session layout, keys),
  read by `scripts/project_config.py` and `local/bin/session/config.sh`;
- the session layer that was previously out of repository — launching and
  briefing a main session, delivering messages to it, keeping its goal loop
  alive, watching keys, pausing, standing down, handing over — was brought in
  under `local/bin/session/` and `local/bin/service/`, with unit tests;
- three protocol documents were written from that layer's operating history:
  `meta-session.md` (the supervising session's playbook), `main-cycle.md` (the
  main session's standing cycle) and `bootstrap.md` (the stage plan from an
  arXiv URL to a running project);
- the previous project's amendment ledger and its retired queue protocol were
  moved to `docs/origin/` as history. **`docs/origin/` is evidence, not law:**
  nothing there is normative for a project built from this kit, and no rule may
  be cited from it;
- the inherited protocols were made paper-agnostic in the same pass, keeping
  every rule and dropping only what identified one project.
  `local/protocols/ci.md`, `review.md`, `site.md`, `sessions.md`, `autofix.md`,
  `issues-prs.md`, `build-cache.md` and `meta.md` now write the runtime root as
  `$MIPSTARRE_CACHE_ROOT` (`paths.cache_root` of `local/project.json`) instead
  of one machine's literal path, and name the owner-inbox and progress issues,
  the key names, the worker models and the Lean root through the configuration
  instead of the origin's issue numbers, key labels, model names and module
  paths; where a rule was paid for by an incident, the reason stays and the
  origin's numbers go. `completion.md` §6 publishes the per-track field table
  as a form and points at `local/audit-registers.json` for the audit
  exemptions; `local/protocols/main-cycle.md`, `meta-session.md` and
  `bootstrap.md` were corrected against the scripts they invoke (flag by flag,
  from each script's own `--help`), and now name the worker-slot interlock, the
  stand-down and relaunch hand-back path, and the machine bring-up step;
  `AGENTS.md` had its toolchain line, its "Local Operations" section and its
  proof-filling order made generic;
  `local/templates/chapter-plan.example.json` was rewritten into a plan that
  `local/bin/tracker_tree.py` accepts, and `docs/comparator.md` into the empty
  record form that `scripts/completion_gate.py` parses.

**Expected effect.** A stranger can clone this repository at the extraction
commit, open a session in it, name a paper, and reach a running project by
following files in the repository alone — without the original author's
memory.

**Outcome.** Pending. The tool tests ship with the kit and the bootstrap path
has a dry-run mode; the path has **not** yet been run end-to-end on a second
paper. The first project built from this kit is the experiment, and its first
amendments belong in this ledger underneath.
