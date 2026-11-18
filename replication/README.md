# Replication materials

Every published result here can be checked from a clean checkout with one command.

| Command | Needs | Time | Checks |
| --- | --- | --- | --- |
| `make replicate` | Python (`uv sync --locked`) | about 3 minutes | Every pinned output below, except the Lean proofs |
| `make replicate-lean` | Also the Lean setup from the quickstart (`make setup`) | about 12 minutes | The same, and proves every Simon design and the Lean-backed worked designs again |
| `make replicate-update` | Python | about 3 minutes | Nothing: it rewrites the pinned outputs after a deliberate change |

Times were measured on an Apple laptop. `make replicate` prints each step's time and
fails if any output differs from the pinned one. CI runs it on every push. It runs
`replication/run.py`; each step is also a script you can run alone.

| Step | Script | Pinned output | Time |
| --- | --- | --- | --- |
| Error-injection evaluation | `evaluate.py` | `results.md`, `results.json` | under 1 s |
| Simon (1989): exact values and optimality | `simon.py` | `simon_results.md`, `simon_results.json` | about 3 min |
| Power for cited tests against base R | `power.py` | `power_results.md` | under 1 s |
| Worked designs without Lean | `examples.py` | statuses recorded in the script | under 1 s |
| Lean only: every Simon design proved again | `simon.py --fresh` | statuses in `simon_proofs.json` | about 8 min |
| Lean only: worked designs with Lean | `examples.py --lean` | statuses recorded in the script | under 1 min |

## Error-injection evaluation

`scenarios.py` holds 33 scenarios. Each takes a valid study file and injects one
common specification error. `evaluate.py` runs them and writes what StatClaim
reports to [results.md](results.md) and `results.json`.

Each scenario ends in one of five outcomes:

| Outcome | Meaning |
| --- | --- |
| rejected | The file is invalid, with a diagnostic at the cause. |
| unresolved | The file is valid but the claim is refused until a requirement is met. |
| calculated | An exact calculation shows that the stated target is not met. |
| surfaced | Nothing is flagged, but the report lists the assumption that is violated. |
| invisible | Nothing is flagged and nothing in the report points at the problem. |

The last two are the limits of the approach, and they are part of the result.
StatClaim reads a declaration. It cannot see that a file says "fixed" when the
data were checked along the way, or that an outcome is not normal.

A scenario states its expected outcome. The run fails if any scenario behaves
differently, so the table cannot drift from the software. To add a scenario,
append a `Scenario` to `SCENARIOS` and run `make replicate-update`.

## Re-checking Simon (1989)

`simon1989.json` holds the 102 two-stage designs tabulated by Simon (1989).
`simon.py` asks three questions of each and writes
[simon_results.md](simon_results.md):

1. Does it meet its stated Type I error and power, in exact arithmetic?
2. Does an exhaustive search of designs up to 120 participants return it?
3. Can Lean prove its error bound for every response rate at or below the null,
   and its power at the alternative?

`make replicate` answers questions 1 and 2. For question 3 it reads the pinned
certificates in `simon_proofs.json`. `make replicate-lean` proves every design
again from scratch into a temporary file and compares each status and proved
statement with the pinned file. To add proofs to the pinned file instead, run
`uv run python replication/simon.py --lean`; it skips designs already proved and
resumes where it stopped.

## Power for cited tests

`power.py` runs each case in `tests/fixtures/power_r.json` through a `.stat` file
and `calculate(meets(...))`, and writes [power_results.md](power_results.md). The R
values come from base R's `power.t.test` and `power.prop.test`; regenerate them
with `Rscript tests/fixtures/power_r.R`. R is not needed to replicate.

## Worked designs

| File | Shows | Lean |
| --- | --- | --- |
| `examples/confirmatory_trial.stat` | An interim look and ordered endpoints in one plan | yes |
| `examples/mixed_endpoints.stat` | A proved and a cited test under one error bound | yes |
| `examples/tutorial/11_bayesian_rule.stat` | A 95% posterior rule with a 5.8% false-positive rate | yes |
| `examples/tutorial/12_continuous_outcome.stat` | The assumptions behind a plain t-test | no |
| `examples/cited_power.stat` | Approximate power for three cited tests | no |

`examples.py` runs each and compares the file's status and every request's status
with those it records. Run `statclaim report <file>` on any of them for its
assumption table.
