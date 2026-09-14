# Owner-authorized fresh-primary effort check — 2026-09-06

At06:33UTC the owner requested a bounded check of literal Astra API effort
`ultra`, with `max` and `xhigh` controls, freshly reading the rotated primary
authentication, tiny responses and fan-out off. This was a probe exception,
not a production effort/routing policy change. Main executed three sequential
requests at06:42:24–06:42:31UTC, outside the effort-rewriting CLI shim.

Sanitized primary evidence:
`../model-comparison/fresh-primary-effort-probe-20260906-0633.json`.
The auth-file mtime was06:25:50.728251UTC and unchanged across all three fresh
in-memory reads. No credentials, headers or response/error bodies were archived.
Literal outgoing `ultra` receivedHTTP400 with no completion-effort metadata;
`max` and `xhigh` receivedHTTP200 and matching completion-effort metadata.
No `medium` completion was observed for the rejected ultra request.

This distinguishes local serialized outgoing effort from returned metadata,
and both from unverified backend compute. It does not test the official Ultra
UI mode. Installed CLI0.153.4 was recorded but not used for these requests;
the configured primary relay was unchanged, and provider version is unknown.
No retries, additional model sessions or worker restarts were needed.
