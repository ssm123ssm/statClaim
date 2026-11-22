#!/usr/bin/env bash
# Start the studio whenever the Codespace starts. Codespaces forwards its port and opens it in
# a browser tab, with Lean, which make setup installed. The log is in .statclaim/studio.log.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .statclaim
setsid nohup uv run --locked python studio/server.py --port 4180 > .statclaim/studio.log 2>&1 < /dev/null &
