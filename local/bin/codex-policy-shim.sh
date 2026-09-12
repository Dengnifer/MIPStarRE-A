#!/usr/bin/env bash
#
# codex-policy-shim.sh — the PATH shim's policy half.
#
# ONE RULE, load-bearing: this shim never rewrites the model it was asked for.
# It asks local/bin/model_policy.py which model the published policy selects and
# runs exactly that.  An owner-wide switch ("all workers on the hard model") is
# a model-policy override — `models.override` in the run brief, or the runtime
# knob $MIPSTARRE_CACHE_ROOT/watchdog/model-override — so the selection is made
# in one place and travels into the session's model-policy snapshot and into
# results/telemetry/sessions.jsonl.
#
# The deployed shim on ghz carried, on 2026-09-12, a line of the form
#   if [ "$model" = <cheap> ]; then model=<hard>; fi   # owner: all workers astra
# That rewrite is deleted and must not come back: with it, sessions.jsonl
# recorded the policy's model while the session ran another one, and the whole
# Sol:Astra ratio audit became unreadable (events.md 2026-09-12, "telemetry
# inaccuracy").  A run-wide model decision belongs in the policy layer, where it
# is recorded as `override_mode` / `override_source` on every row it affects and
# excluded from the ratio rather than read as a violation.
#
# The shim also refuses to widen anything: fan-out stays off, effort stays
# `ultra`, and whole `features`/`agents` table overrides are rejected.
#
set -euo pipefail
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
policy_args=(--role "${MIPSTARRE_DISPATCH_ROLE:-orc}" --job-class "${MIPSTARRE_JOB_CLASS:-general}"
  --model "$model" --effort "$effort" --field model)
[ -z "${MIPSTARRE_HARDNESS_REASON:-}" ] ||
  policy_args+=(--hardness-reason "$MIPSTARRE_HARDNESS_REASON")
# The single selection point. Whatever comes back is what runs: no rewrite here,
# no second opinion, and an override is already folded into this answer.
model="$(python3 "$script_dir/model_policy.py" "${policy_args[@]}")" || exit 4
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
