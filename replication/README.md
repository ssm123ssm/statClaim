# Replication materials

Everything here runs from a clean checkout with Python only, in a few seconds.

## Error-injection evaluation

`scenarios.py` holds 31 scenarios. Each takes a valid study file and injects one
common specification error. `evaluate.py` runs them and writes what StatClaim
reports to [results.md](results.md) and `results.json`.

```sh
uv run python replication/evaluate.py          # regenerate the results
uv run python replication/evaluate.py --check  # confirm they are current
```

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
differently, so the table cannot drift from the software.

To add a scenario, append a `Scenario` to `SCENARIOS` and rerun.

## Re-checking Simon (1989)

`simon1989.json` holds the 102 two-stage designs tabulated by Simon (1989).
`simon.py` asks three questions of each and writes
[simon_results.md](simon_results.md):

1. Does it meet its stated Type I error and power, in exact arithmetic?
2. Does an exhaustive search of designs up to 120 participants return it?
3. Can Lean prove its error bound for every response rate at or below the null,
   and its power at the alternative?

```sh
uv run python replication/simon.py          # questions 1 and 2, about 3 minutes
uv run python replication/simon.py --lean   # also question 3, about 20 minutes
```

The Lean run needs the Lean setup from the quickstart. It records each
certificate in `simon_proofs.json` and resumes where it stopped.

## Worked designs

| File | Shows |
| --- | --- |
| `examples/confirmatory_trial.stat` | An interim look and ordered endpoints in one plan |
| `examples/mixed_endpoints.stat` | A proved and a cited test under one error bound |
| `examples/tutorial/11_bayesian_rule.stat` | A 95% posterior rule with a 5.8% false-positive rate |
| `examples/tutorial/12_continuous_outcome.stat` | The assumptions behind a plain t-test |

Run `statclaim report <file>` on any of them for its assumption table. The
first two also need Lean for `statclaim check`.
