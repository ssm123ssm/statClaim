# Quickstart

## In the browser

[Create a Codespace](https://codespaces.new/ssm123ssm/statClaim). Setup downloads
the pinned Lean toolchain and Mathlib cache, so the first start takes several
minutes. A workspace extension is installed on attachment. Reload the window
if `.stat` support has not appeared. Codespaces uses your GitHub quota.

Open `playground/welcome.stat`. It is your scratch copy and is ignored by git.
Edit the null to `proportion_difference(model=study, value=1/10)` and inspect
the diagnostic. Restore equality, then run **StatClaim: Verify Current File**.

Other files in `playground/`:

| File | Shows |
| --- | --- |
| `planning.stat`, `unequal_allocation.stat` | Power and sample size for two arms |
| `one_sided.stat` | A one-sided two-arm test from planning to analysis |
| `non_inferiority.stat` | A non-inferiority test with a margin |
| `one_sample.stat`, `one_sample_result.stat` | Planning and analysing a single-arm study |
| `confidence_interval.stat`, `difference_interval.stat` | Confidence intervals for one proportion and for a difference |
| `three_outcomes.stat` | Several endpoints with Bonferroni |
| `two_stage.stat`, `two_stage_posterior.stat` | Designs with an interim stop |
| `two_stage_search.stat` | Finding an optimal or minimax two-stage design |
| `two_stage_result.stat` | Analysing the data from a two-stage study |
| `t_test.stat` | A continuous outcome with a cited t-test |
| `log_rank.stat` | A time-to-event outcome with the cited log-rank test |
| `interim_look.stat` | An interim analysis with the error level split across looks |
| `confirmatory_trial.stat` | An interim look and ordered endpoints in one plan |
| `recycling.stat` | Co-primary endpoints with recycling, gating secondary endpoints |
| `trial_models.stat` | A mixed model and a logistic regression as cited tests |
| `declared_test.stat` | An analysis StatClaim does not know, declared by name |
| `cited_power.stat` | Approximate power for cited tests, by calculation only |
| `lower_is_better.stat` | An outcome where lower is better, declared and checked |
| `mixed_endpoints.stat` | A proved and a cited test under one error bound |

## Without Lean

Checking contracts, explanations, reports, cited claims and approximate power
needs only Python 3.12 or newer. Install the package and work in any folder:

```sh
pip install statclaim
statclaim check my_study.stat
statclaim report my_study.stat
```

The package contains the program only. The example files are in the
[`examples/`](../examples) folder of the repository, and in the source archive
on PyPI. Download one, such as `examples/t_test.stat`, to start from it.

Proved and conditional claims need Lean, which lives in a checkout of the
repository. Without one, such a claim stays open with a message that says so.
`statclaim doctor` reports what your installation can do; outside a checkout
it says that Lean was not checked and exits with code 1.

To add Lean, clone the repository and run `make setup` in it. You can then
keep working in your own folder and point at the checkout:

```sh
statclaim check my_study.stat --project path/to/statClaim
```

## Local VS Code

Run `make setup`, then `make editor-package`. Install
`extensions/vscode/dist/statclaim.vsix` with **Extensions: Install from VSIX**.
Open this repository as the workspace and trust it. For extension development,
install npm dependencies and press F5; see [editor guide](editor.md).

## Inspect values

The Explorer **StatClaim Claims** view displays requirements and matching
evidence. **StatClaim: Verify Current File** writes its structured report to
the StatClaim output channel. From a terminal:

```sh
uv run --locked statclaim check playground/welcome.stat --json
```

The report includes bindings such as `status` and `evidence`. Evidence is optional
and appears only after successful verification. Editing marks earlier results
as historical. `compile` checks the plan without running Lean or writing results.

```sh
uv run --locked statclaim compile examples/fisher.stat
uv run --locked statclaim catalogue --json
```

If setup fails, run `uv run --locked statclaim doctor` and include the output
in an issue. See [development](development.md) for tests and container setup.
