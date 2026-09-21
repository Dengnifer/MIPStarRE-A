#!/usr/bin/env bash
# Moved: the merge runner is now local/bin/service/merge.sh (parameterised, tested).
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../local/bin/service" && pwd -P)/merge.sh" "$@"
