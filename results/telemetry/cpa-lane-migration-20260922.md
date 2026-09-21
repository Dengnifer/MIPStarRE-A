# Owner-authorized lane migration

Main executed bash /tmp/main-migrate-lanes-to-cpa.sh after both active space-3
workers failed with429 and before the comparator task was complete. The helper
observed429 twice, marked space-3 retired at2026-09-21T16:02:42Z, verified cpa200,
and printed MIGRATED at16:02:45Z. It set keyrot/cpa limit2 and caps2/0/2.
No meta assistance, native delegation, proxy or subscription was used. Space-3
must not be used again without an explicit owner quota-renewal instruction.
CPA is now the only key for main and at most two detached lane workers.

Interrupted sessions, both exit1 with unknown usage:

- blueprint-666-20260922-01, thread01a0c4a6-a919-7093-976a-5b57b4325c59:
  757 seconds. The four dirty documentation files in PR669's worktree remain.
- reviewer-pr671-20260922-01, thread01a0c4b0-94cf-7001-ac24-3fe7f8be47f8:
  161 seconds. Sourcea3683e9b remains clean. There is no completed review or
  machine-parseable verdict to publish from this failed session.

Fresh dispatch.sh --continue-from sessions were admitted after MIGRATED:

- blueprint-666-20260922-02, thread01a0c4b6-b53a-7543-ad50-a9f9f7bb7db9,
  cpa marker/node2886556. Remaining443 of the original1200 repair seconds.
- reviewer-pr671-20260922-02, thread01a0c4b9-cf4c-7c91-8e85-3c977ee9a4fe,
  cpa marker/node2898964. Remaining1039 of the original1200 review seconds.

Both markers were observed under keyrot/cpa; no space-3 marker was read as
authority to reuse that retired key. The continuation validator binds each
terminal predecessor, same issue, checkpoint ancestor, shared anchor, charged
seconds and attempt count. Handoffs and budgets are
/tmp/main-cpa-{fix669,review671}-migration-{handoff,budget}-20260922.json.
This is a continuation of the third source-episode review, not a fourth
completed review or a reset of earlier663/660 history. All earlier author,
repair and reviewer charges remain independently recorded.

The reviewer continuation first hit two pre-model prompt-size refusals at the
unchanged120000-byte cap. Both logs are preserved. The complete authoritative
diff remains in the canonical review directory and is required reading; it is
no longer redundantly inlined. The inherited663 reviews remain attached, and
the660 reviews remain available by their explicit path. No limit or safeguard
was raised and no model ran during those two preflights.

Progress Log27 comment5763629454 records the migration. The real external
comparator run35621468975 was still compiling at16:07:12Z. It is preliminary:
source671 is not service-merged and no final merged-main pin or acceptance
record exists. Its model-free monitor remains active. PR670 has green CI but
awaits its prepared independent source-adoption review after a real vacancy.

Any cpa quota/auth failure now requires one27 report of every in-flight item
and goal pause. No further key fallback is authorized.
