### Motivation
- Close #232 by moving the temporary two-account router into the dispatcher,
  and subsume #231's missing model identity without a separate PR.

### Description
- Reuse #231 commit `6ae352b` (cherry-picked as `8bcee45`) and retain its tests.
- Reserve per-account capacity atomically, clean stale PID markers, preserve
  resume affinity, and record the selected account and explicitly pinned model.
- Prefer registry models in comparisons; document routing and timeout overflow.
- Operator follow-up **after merge**: replace the runtime shim with its v1
  behavior (multi-agent off only), using
  `~/.cache/mipstarre-dev/owner-bin/codex.v1-20260904`, and set watchdog
  `max-codex` back to the sum of `max-codex-primary` and `max-codex-second`
  (19 with default caps). Do not run the old routing shim alongside dispatcher
  routing: it can override the selected account and invalidate telemetry.
- No runtime shim, credential, configuration, lane script, or merge daemon
  changes are included. Independent lane CI/review and daemon merge remain required.

### Testing
- `python3 -m unittest scripts.tests.test_dispatch -q`: focused routing and
  dispatcher regression tests: 24 passed, including astra mathfix selection.
- Normal pre-commit hook: all 486 `scripts/tests` tests passed.
- `bash -n` passed for dispatch, review, and autofix; `git diff --check` passed.
- Fake CLI fixtures verify account environments, model metadata, and cleanup
  without starting an agent or contacting a provider.
- Lean validation is not applicable: no Lean or blueprint files change.

---
Closes #232
Closes #231
