Completed exactly two requests on ghz using `gpt-6-astra`, literal `reasoning.effort=ultra`, and `max_output_tokens=64`.

| Credential | HTTP | Elapsed |
|---|---:|---:|
| Relay | 400 | 0.963 s |
| Space | 400 | 1.737 s |

Both returned `invalid_value` for `reasoning.effort`:

> Invalid value: 'ultra'. Supported values are: 'none', 'minimal', 'low', 'medium', 'high', 'xhigh', and 'max'.

Neither returned completion effort. No retries occurred.

[Sanitized result](/tmp/qpbt-meta-20260905-230133/both-key-ultra-results-20260906.json) includes UTC timestamps, auth-file mtimes, and configured endpoints. This does not establish backend compute equivalence or test an official UI mode.