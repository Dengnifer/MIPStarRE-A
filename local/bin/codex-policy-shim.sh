#!/usr/bin/env bash
# codex-policy-shim.sh — the in-repo argument guard for a dispatched worker.
#
# It enforces three things and invents nothing:
#   * fan-out stays off (`features.multi_agent`, `agents.max_concurrent_threads_per_session`
#     are forced, whole `features=`/`agents=` table overrides are refused);
#   * the reasoning effort of the dispatch may not be rewritten from the command line;
#   * the model must be one the project configures (local/project.json, read through
#     local/bin/model_policy.py).  No model name is written in this file: with no model
#     configured, every explicit `-m` is refused and codex runs on its own default.
# A routine selection additionally needs a dispatcher reservation, so that a worker
# cannot take a rotation slot the account router did not hand out.
#
# The machine-wide PATH shim for key rotation is a different tool:
# local/bin/service/codex-shim.
set -euo pipefail
script_dir="$(dirname -- "$(readlink -f -- "${BASH_SOURCE[0]}")")"

# The models this project configures, as a space-padded string for a case match.
allowed=" $(python3 "$script_dir/model_policy.py" --list-models 2>/dev/null | tr '\n' ' ' || true)"
check_model() { case "$allowed" in *" $1 "*) return 0 ;; esac
  echo "model '$1' is not configured for this project" >&2; exit 4; }

args=(); task=0
effort="${MIPSTARRE_REQUESTED_EFFORT:-${KIT_WORKER_EFFORT:-ultra}}"
model="${MIPSTARRE_CODEX_MODEL:-auto}"
while [ "$#" -gt 0 ]; do
  argument="$1"; shift
  if [ "$argument" = -- ]; then args+=(-- "$@"); task=1; break; fi
  case "$argument" in
    --enable|--enable=*)
      feature="${argument#--enable=}"
      if [ "$argument" = --enable ]; then feature="${1:?missing feature}"; shift; fi
      case "$feature" in *multi_agent*) echo 'fan-out must remain disabled' >&2; exit 4 ;; esac
      args+=(--enable "$feature"); continue ;;
    -m|--model)
      model="${1:-}"; check_model "$model"; shift; continue ;;
    --model=*)
      model="${argument#--model=}"; check_model "$model"; continue ;;
    -m?*)
      attached_model="${argument#-m}"; attached_model="${attached_model#=}"
      check_model "$attached_model"; model="$attached_model"; continue ;;
    -c|--config)
      value="${1:?missing config value}"; shift ;;
    --config=*) value="${argument#--config=}" ;;
    -c?*) value="${argument#-c}"; value="${value#=}" ;;
    *) args+=("$argument"); continue ;;
  esac
  normalized="${value//[[:space:]]/}"
  normalized="${normalized//\"/}"; normalized="${normalized//\'/}"
  case "$normalized" in
    features=*|agents=*) echo 'whole feature/agent table overrides are forbidden' >&2; exit 4 ;;
    model=*)
      model="${normalized#model=}"; check_model "$model"; continue ;;
    model_reasoning_effort=*)
      case "${normalized#*=}" in
        "$effort") ;;
        *) echo "effort must be $effort" >&2; exit 4 ;;
      esac
      continue ;;
    features.multi_agent=*|agents.max_concurrent_threads_per_session=*)
      continue ;;
  esac
  args+=(-c "$value")
done

policy_args=(--role "${MIPSTARRE_DISPATCH_ROLE:-orc}" --job-class "${MIPSTARRE_JOB_CLASS:-general}"
  --model "$model" --effort "$effort")
[ -z "${MIPSTARRE_HARDNESS_REASON:-}" ] ||
  policy_args+=(--hardness-reason "$MIPSTARRE_HARDNESS_REASON")
selection="$(python3 "$script_dir/model_policy.py" "${policy_args[@]}")" || exit 4
pair="$(printf '%s' "$selection" | python3 -c \
  'import json,sys; s=json.load(sys.stdin); sys.stdout.write((s["model"] or "") + chr(10) + s["classification"] + chr(10))')"
model="${pair%%$'\n'*}"
classification="${pair#*$'\n'}"

# Routine work runs on the cheap slot the dispatcher hands out; without a reservation
# the worker is not one the account router counted.
if [ "$classification" = routine ]; then
  reservation="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/accounts/${MIPSTARRE_DISPATCH_ACCOUNT:-invalid}/${MIPSTARRE_DISPATCH_PID:-invalid}"
  [ -f "$reservation" ] || { echo 'a routine dispatch requires dispatcher admission' >&2; exit 4; }
fi

if [ "$task" -eq 1 ] && [ "${#args[@]}" -gt 0 ]; then
  last=$(( ${#args[@]} - 1 ))
  args[$last]="Complete this task in the current session. Do not use collaboration tools or spawn subagents.

${args[$last]}"
fi

# The real codex: never a hard-coded install path.
real="${MIPSTARRE_CODEX_BIN:-}"
if [ -z "$real" ]; then
  stripped=""
  IFS=':' read -r -a parts <<< "$PATH"
  for p in "${parts[@]}"; do
    if [ "$p" = "$script_dir" ]; then continue; fi
    stripped="${stripped:+$stripped:}$p"
  done
  real="$(PATH="$stripped" command -v codex 2>/dev/null || true)"
fi
[ -n "$real" ] || { echo 'cannot find codex on PATH (set MIPSTARRE_CODEX_BIN)' >&2; exit 4; }

forced=()
if [ -n "$model" ]; then forced+=(-m "$model"); fi
if [ -n "$effort" ]; then forced+=(-c "model_reasoning_effort=\"$effort\""); fi
forced+=(-c 'features.multi_agent=false' -c 'agents.max_concurrent_threads_per_session=1')
exec "$real" "${forced[@]}" "${args[@]}"
