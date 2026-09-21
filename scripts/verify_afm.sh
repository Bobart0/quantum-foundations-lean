#!/usr/bin/env bash
set -euo pipefail
exec "$(dirname "$0")/verify_publication.sh" "$@"
