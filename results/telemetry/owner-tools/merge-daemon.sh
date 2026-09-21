#!/usr/bin/env bash
# Moved: the merge queue is now local/bin/service/merge-daemon.sh (four versions newer).
exec "$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../local/bin/service" && pwd -P)/merge-daemon.sh" "$@"
