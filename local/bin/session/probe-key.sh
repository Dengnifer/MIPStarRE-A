#!/usr/bin/env bash
# probe-key.sh <key-name> [model] — ask a configured key's own endpoint one tiny
# question and report only the HTTP code and a redacted tail of the answer.
#
# Provenance: the origin project's meta-probe-key.sh, generalized.  This is the
# only evidence the kit accepts that a key works or is dead: pane text and
# worker logs are hints (a reviewer can quote an error string out of a diff),
# a direct probe is proof.  No proxy is used, and the key is never printed.
#
#   exit 0  HTTP 200            exit 2  no key/endpoint in the key's home
#   exit 75 any other answer    exit 3  usage
set -u
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lib.sh"

usage() { cat >&2 <<'EOF'
usage: probe-key.sh <key-name> [model] [--timeout S] [--tail N]
  <key-name>  a key NAME from the project configuration (keys.<name>);
              its CODEX_HOME must already hold config.toml and auth.json.
  [model]     model id to ask; defaults to the configured main model.
EOF
exit 3; }

KEY=""; MODEL=""; TIMEOUT=60; TAIL=300
while [ $# -gt 0 ]; do
  case "$1" in
    --timeout) TIMEOUT="${2:?}"; shift 2 ;;
    --tail) TAIL="${2:?}"; shift 2 ;;
    --dry-run) KIT_DRY_RUN=1; shift ;;
    -h|--help) usage ;;
    -*) usage ;;
    *) if [ -z "$KEY" ]; then KEY="$1"; elif [ -z "$MODEL" ]; then MODEL="$1"; else usage; fi; shift ;;
  esac
done
[ -n "$KEY" ] || usage
[ -n "$MODEL" ] || MODEL="$KIT_MAIN_MODEL"

HOME_DIR="$(kit_key_home "$KEY")"

if kit_is_dry; then
  printf 'DRY probe key=%s model=%s home=%s\n' "$KEY" "${MODEL:-<cli default>}" "$HOME_DIR"
  exit 0
fi

[ -d "$HOME_DIR" ] || { printf 'probe %s: no such CODEX_HOME directory\n' "$KEY"; exit 2; }
URL="$(grep -m1 '^[[:space:]]*base_url' "$HOME_DIR/config.toml" 2>/dev/null | cut -d'"' -f2 | sed 's:/*$::')"
[ -n "$URL" ] || { printf 'probe %s: no base_url in the key home config.toml\n' "$KEY"; exit 2; }
SECRET="$(python3 -c 'import json,sys
try:
    print(json.load(open(sys.argv[1])).get("OPENAI_API_KEY", ""))
except Exception:
    print("")' "$HOME_DIR/auth.json" 2>/dev/null)"
[ -n "$SECRET" ] || { printf 'probe %s: no key in the key home auth.json\n' "$KEY"; exit 2; }

# a probe must never travel through a proxy: it would report the proxy's health
unset http_proxy https_proxy HTTP_PROXY HTTPS_PROXY all_proxy ALL_PROXY

if [ -n "$MODEL" ]; then
  PAYLOAD="{\"model\":\"$MODEL\",\"input\":\"Reply with ok.\",\"max_output_tokens\":16}"
else
  PAYLOAD="{\"input\":\"Reply with ok.\",\"max_output_tokens\":16}"
fi

BODY="$(curl -s -m "$TIMEOUT" --noproxy '*' -o - -w '\nHTTP%{http_code}' "$URL/responses" \
  -H "Authorization: Bearer $SECRET" -H 'Content-Type: application/json' \
  -d "$PAYLOAD" 2>/dev/null)"
CODE="$(printf '%s' "$BODY" | tail -n 1 | sed 's/^HTTP//')"

# print the answer with the key removed FIRST, then shortened
printf '%s' "$BODY" | KIT_PROBE_SECRET="$SECRET" python3 -c '
import os, sys
text = sys.stdin.read()
secret = os.environ.get("KIT_PROBE_SECRET", "")
if secret:
    text = text.replace(secret, "<redacted>")
sys.stdout.write(text[-int(sys.argv[1]):].lstrip("\n"))
sys.stdout.write("\n")
' "$TAIL"

printf 'probe key=%s model=%s keylen=%s HTTP%s\n' "$KEY" "${MODEL:-<cli default>}" "${#SECRET}" "${CODE:-000}"
[ "$CODE" = 200 ] && exit 0
exit 75
