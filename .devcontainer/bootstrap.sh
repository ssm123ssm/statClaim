#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
make setup
make editor-package
mkdir -p playground
if [[ ! -f playground/welcome.stat ]]; then
  cp examples/playground.stat playground/welcome.stat
fi
for example in planning unequal_allocation one_sided non_inferiority one_sample one_sample_result confidence_interval difference_interval three_outcomes two_stage two_stage_posterior two_stage_search two_stage_result t_test log_rank mixed_endpoints interim_look confirmatory_trial recycling trial_models declared_test cited_power lower_is_better shared_assignment declared_design randomisation cluster_trial; do
  if [[ ! -f "playground/$example.stat" ]]; then
    cp "examples/$example.stat" "playground/$example.stat"
  fi
done
uv run --locked statclaim doctor
printf '\nReady: open playground/welcome.stat and run StatClaim: Show Claims.\n'
