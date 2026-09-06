#!/usr/bin/env bash
set -euo pipefail
mode_file="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/watchdog/account-mode"
mode=primary
if [ -f "$mode_file" ]; then mode="$(cat "$mode_file")"; fi
case "$mode" in primary|both) ;; *) echo 'invalid account mode' >&2; exit 4 ;; esac
if [ "$mode" = primary ] && [ "${CODEX_HOME:-$HOME/.codex}" != "$HOME/.codex" ]; then
  echo 'primary-only policy: preserve the old thread; use a checkpoint continuation' >&2
  exit 4
fi
args=(); task=0; effort=max
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
      [ "${1:-}" = gpt-6-astra ] || { echo 'gpt-6-astra required' >&2; exit 4; }
      shift; continue ;;
    -m?*)
      model="${argument#-m}"
      [ "${model#=}" = gpt-6-astra ] || { echo 'gpt-6-astra required' >&2; exit 4; }
      continue ;;
    --model=*)
      [ "$argument" = --model=gpt-6-astra ] || exit 4
      continue ;;
    -c|--config)
      value="${1:?missing config value}"; shift ;;
    --config=*|-c?*) value="${argument#*=}"; [ "$argument" != "${argument#-c}" ] && value="${argument#-c}" ;;
    *) args+=("$argument"); continue ;;
  esac
  normalized="${value//[[:space:]]/}"
  normalized="${normalized//\"/}"; normalized="${normalized//\'/}"
  case "$normalized" in
    features=*|agents=*) echo 'whole feature/agent table overrides are forbidden' >&2; exit 4 ;;
    model=*) [ "$normalized" = model=gpt-6-astra ] || exit 4; continue ;;
    model_reasoning_effort=*)
      case "${normalized#*=}" in
        max|xhigh) effort="${normalized#*=}" ;;
        ultra) effort=max ;;
        *) echo 'effort must be max or xhigh (legacy ultra maps to max)' >&2; exit 4 ;;
      esac
      continue ;;
    features.multi_agent=*|agents.max_concurrent_threads_per_session=*)
      continue ;;
  esac
  args+=(-c "$value")
done
if [ "$task" -eq 1 ] && [ "${#args[@]}" -gt 0 ]; then
  last=$(( ${#args[@]} - 1 ))
  args[$last]="Complete this task in the current session. Do not use collaboration tools or spawn subagents.

${args[$last]}"
fi
exec "$HOME/.local/bin/codex" -m gpt-6-astra -c "model_reasoning_effort=\"$effort\"" \
  -c 'features.multi_agent=false' -c 'agents.max_concurrent_threads_per_session=1' "${args[@]}"
