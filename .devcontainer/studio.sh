#!/usr/bin/env bash
# Start the studio, with Lean, unless it is already running. The Codespace runs this when it
# starts and again when the editor connects, so the studio comes up while the editor is there
# to forward its port and open it. Each start is appended to .statclaim/studio.log.
set -euo pipefail
cd "$(dirname "$0")/.."
port=4180
running() { curl -sf "http://127.0.0.1:$port/api/capabilities" > /dev/null; }
if running; then
  echo "StatClaim Studio is running at http://localhost:$port"
  exit 0
fi
mkdir -p .statclaim
printf '\n== %s: starting the studio\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> .statclaim/studio.log
setsid nohup uv run --locked python studio/server.py --port "$port" \
  >> .statclaim/studio.log 2>&1 < /dev/null &
for _ in $(seq 90); do
  if running; then
    echo "StatClaim Studio is running at http://localhost:$port"
    exit 0
  fi
  sleep 1
done
echo "StatClaim Studio did not start. The end of .statclaim/studio.log:" >&2
tail -n 20 .statclaim/studio.log >&2
exit 1
