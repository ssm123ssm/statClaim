#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
make setup
make editor-package
mkdir -p playground
if [[ ! -f playground/welcome.stat ]]; then
  cp examples/playground.stat playground/welcome.stat
fi
uv run --locked statproof doctor
printf '\nReady: open playground/welcome.stat and run StatProof: Show Claims.\n'
