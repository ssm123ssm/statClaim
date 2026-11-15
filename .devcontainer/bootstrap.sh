#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
make setup
make editor-package
mkdir -p playground
if [[ ! -f playground/welcome.stat ]]; then
  cp examples/playground.stat playground/welcome.stat
fi
for example in planning one_sample one_sample_result confidence_interval three_outcomes two_stage two_stage_posterior; do
  if [[ ! -f "playground/$example.stat" ]]; then
    cp "examples/$example.stat" "playground/$example.stat"
  fi
done
uv run --locked statproof doctor
printf '\nReady: open playground/welcome.stat and run StatProof: Show Claims.\n'
