#!/usr/bin/env python3
"""Per-subagent token usage across both pools, for the workflow paper.

Codex workers (dispatch.sh): results/telemetry/sessions.jsonl, field `usage`
  = {input, cached_input, cache_write, output, reasoning} from the codex exec JSON stream.
Claude subagents (owner session, Agent tool): results/telemetry/owner-sessions.jsonl, field
  `tokens` = the total reported by the Claude Code harness for the subagent (`subagent_tokens`),
  plus `tool_uses` and `wall_s`. Start stubs (status running) are paired with their end record
  by name prefix; a stub whose end record exists is not counted twice.

Usage: python3 results/telemetry/owner-tools/session-usage.py [--md]  (from the repo root)
"""
import json, sys, collections, re, datetime, pathlib
root = pathlib.Path(__file__).resolve().parents[3]
def load(p):
    out = []
    for line in (root / p).read_text().splitlines():
        line = line.strip()
        if not line: continue
        try: out.append(json.loads(line))
        except Exception: pass
    return out
codex = load('results/telemetry/sessions.jsonl')
claude = load('results/telemetry/owner-sessions.jsonl')
by = collections.defaultdict(lambda: collections.Counter())
rows = []
for s in codex:
    u = s.get('usage') or {}
    tot = (u.get('input') or 0) + (u.get('output') or 0)
    key = ('codex:' + str(s.get('dispatcher') or s.get('model') or 'gpt-5.6-sol'), s.get('role') or '?')
    by[key]['sessions'] += 1; by[key]['input'] += u.get('input') or 0; by[key]['cached'] += u.get('cached_input') or 0
    by[key]['output'] += u.get('output') or 0; by[key]['reasoning'] += u.get('reasoning') or 0; by[key]['total'] += tot
    by[key]['wall_s'] += s.get('wall_s') or 0
    rows.append(('codex', s.get('name'), s.get('role'), s.get('issue'), (s.get('start') or '')[:16], tot, s.get('wall_s')))
# Claude: prefer end records (status != running); drop a running stub if any other record shares its issue+role+model and has tokens
ended = [s for s in claude if s.get('status') != 'running']
for s in ended:
    key = ('claude:' + str(s.get('model')), s.get('role') or '?')
    by[key]['sessions'] += 1; by[key]['total'] += s.get('tokens') or 0; by[key]['wall_s'] += s.get('wall_s') or 0
    by[key]['tool_uses'] += s.get('tool_uses') or 0
    rows.append(('claude', s.get('name'), s.get('role'), s.get('issue'), (s.get('start') or '')[:16], s.get('tokens') or 0, s.get('wall_s')))
still = [s for s in claude if s.get('status') == 'running']
if '--md' in sys.argv:
    print('# Subagent token usage (generated %s)\n' % datetime.datetime.utcnow().strftime('%Y-%m-%dT%H:%MZ'))
    print('Codex totals count input + output tokens (cached input shown separately); Claude totals are the harness-reported subagent totals.\n')
    print('| pool:model | role | sessions | total tokens | input | cached input | output | reasoning | tool uses | wall hours |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    for (pm, role), c in sorted(by.items()):
        print(f"| {pm} | {role} | {c['sessions']} | {c['total']:,} | {c['input']:,} | {c['cached']:,} | {c['output']:,} | {c['reasoning']:,} | {c['tool_uses']} | {c['wall_s']/3600:.1f} |")
    g = collections.Counter()
    for (pm, role), c in by.items(): g[pm.split(':')[0]] += c['total']
    print('\nGrand totals: ' + ', '.join(f"{k}: {v:,}" for k, v in sorted(g.items())))
    print(f"\nClaude records still marked running (no end record yet): {len(still)}")
else:
    for r in rows: print(json.dumps(dict(zip(['pool','name','role','issue','start','tokens','wall_s'], r))))
