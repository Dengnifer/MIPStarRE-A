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
args=(); task=0; effort=ultra; model="${MIPSTARRE_CODEX_MODEL:-auto}"
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
      model="${1:-}"
      case "$model" in gpt-6-astra|gpt-5.6-sol) ;; *) exit 4 ;; esac
      shift; continue ;;
    --model=*)
      model="${argument#--model=}"
      case "$model" in gpt-6-astra|gpt-5.6-sol) ;; *) exit 4 ;; esac
      continue ;;
    -m?*)
      attached_model="${argument#-m}"; attached_model="${attached_model#=}"
      case "$attached_model" in gpt-6-astra|gpt-5.6-sol) ;; *) exit 4 ;; esac
      model="$attached_model"
      continue ;;
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
      model="${normalized#model=}"
      case "$model" in gpt-6-astra|gpt-5.6-sol) ;; *) exit 4 ;; esac
      continue ;;
    model_reasoning_effort=*)
      case "${normalized#*=}" in
        ultra) ;;
        *) echo 'effort must be ultra' >&2; exit 4 ;;
      esac
      continue ;;
    features.multi_agent=*|agents.max_concurrent_threads_per_session=*)
      continue ;;
  esac
  args+=(-c "$value")
done
script_dir="$(dirname -- "$(readlink -f -- "${BASH_SOURCE[0]}")")"
model="$(python3 "$script_dir/model_policy.py" --role "${MIPSTARRE_DISPATCH_ROLE:-orc}" \
  --job-class "${MIPSTARRE_JOB_CLASS:-general}" --model "$model" \
  --effort "$effort" --field model --external --worktree "${MIPSTARRE_DISPATCH_WORKTREE:-$PWD}" \
  ${MIPSTARRE_JOB_SPEC:+--job-spec "$MIPSTARRE_JOB_SPEC"})" || exit 4
if [ "$model" = gpt-5.6-sol ]; then
  reservation="${MIPSTARRE_CACHE_ROOT:-$HOME/.cache/mipstarre-dev}/accounts/${MIPSTARRE_DISPATCH_ACCOUNT:-invalid}/${MIPSTARRE_DISPATCH_PID:-invalid}"
  [ -f "$reservation" ] || { echo 'Sol requires dispatcher admission' >&2; exit 4; }
fi
if [ "$task" -eq 1 ] && [ "${#args[@]}" -gt 0 ]; then
  last=$(( ${#args[@]} - 1 ))
  args[$last]="Complete this task in the current session. Do not use collaboration tools or spawn subagents.

${args[$last]}"
fi
exec "$HOME/.local/bin/codex" -m "$model" -c "model_reasoning_effort=\"$effort\"" \
  -c 'features.multi_agent=false' -c 'agents.max_concurrent_threads_per_session=1' "${args[@]}"
