#!/usr/bin/env bash
# Moved: the lane runner is now local/bin/service/lane.sh (parameterised, tested).
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../local/bin/service" && pwd -P)/lane.sh" "$@"
