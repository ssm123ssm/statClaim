# StatProof

Compute a two-sided Fisher exact test using exact integer and rational arithmetic,
and track the formal obligations needed for a Lean-backed statistical guarantee.
The [project brief](statistical_design_checker_project_brief.md) defines the scope.

**Working now:** the probability-ordered Fisher calculation, inclusive rejection
at `alpha = 1/20`, input validation, JSON reports, and a Lean-checked generic
finite-distribution p-value validity theorem. The complete binomial-model theorem
and the Python-to-Lean correspondence remain unresolved. Reports identify the
calculation as exact computation and do not issue a formal certificate.

## Run the test

From this project folder, after setup:

```sh
uv run --locked statproof test examples/fixed_sample.toml \
  --control-successes 10 --treatment-successes 25
```

This example declares 100 observations in each arm. The p-value is approximately
`0.00850357147862395534`, and the specified rule rejects equal proportions at
`0.05`. JSON output preserves the exact numerator and denominator alongside a
display approximation, the table, assumptions, decision, evidence type, and
outstanding formal obligations. Failure to reject is reported as
`do_not_reject_null`, not acceptance of the null.

To change sample sizes, copy and edit the declaration:

```toml
[design]
module = "two_arm_binomial"
n_control = 100
n_treatment = 100
stopping = "fixed"
```

To use the calculation from Python:

```python
from statproof.fisher import fisher_exact

result = fisher_exact(
    n_control=10,
    n_treatment=14,
    control_successes=1,
    treatment_successes=11,
)
assert str(result.p_value) == "41/14858"
assert result.reject_null
```

The API computes the fixed-sample statistic and decision; it does not validate
real-world sampling assumptions. See the [exact test specification](docs/exact-test-spec.md)
for probability ordering, tie handling, boundary cases, and proof scope.

## Unsupported stopping modification

```sh
uv run --locked statproof test examples/data_dependent_stopping.toml \
  --control-successes 10 --treatment-successes 25
```

This computes the fixed-margin statistic but returns `decision: null` and an
unresolved obligation for the modified stopping procedure. A numerical threshold
comparison does not establish its Type I error guarantee.

`statproof inspect DESIGN.toml` lists the design's obligations without executing
the test. Neither command invokes Lean or issues a verification certificate.

| Command outcome | Exit code |
| --- | ---: |
| `test`: completed fixed-sample calculation, either decision | `0` |
| `test`: unsupported stopping rule; `inspect`: unresolved obligations | `1` |
| Malformed declaration, invalid data, or argument error | `2` |

## Development setup

Prerequisites: [uv](https://docs.astral.sh/uv/getting-started/installation/),
[elan](https://lean-lang.org/install/manual/), Git, and Make. Run from this folder:

```sh
make setup
uv run --locked statproof doctor
make check
```

Python 3.12 is selected by `.python-version`; `uv.lock` records Python dependency
versions. `uv sync` creates the local `.venv`. Lean and Mathlib are pinned to
`v4.35.0`; `lake-manifest.json` records exact dependency commits. First setup
downloads Lean, Mathlib sources, and the needed precompiled library files.

For ordinary development, use `uv sync --locked` and `lake build`. When changing
Lean dependencies, deliberately run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update`
and review the manifest changes. Add new imports to `make setup`'s cache command
as the proof library grows.

`make check` runs Python linting, formatting, tests, the Lean build, a basic
source-placeholder guard, and an axiom listing for the generic theorem. The guard
is a development check, not a complete audit of all trusted components.

For the optional live comparison with R (requires `Rscript`):

```sh
make reference-check
# Regenerate the small set of stored R reference results:
uv run --locked python scripts/compare_with_r.py --write-fixtures
```

The default test suite uses stored reference results and does not require R.
`make demo` runs the fixed-sample example.

## Layout

- `src/statproof/`: exact calculation, declarations, reports, and CLI.
- `StatProof/`: foundational definitions and the generic finite p-value theorem.
- `docs/exact-test-spec.md`: mathematical and executable specification.
- `docs/development.md`: completed work and remaining proof obligations.
- `examples/`: fixed-sample and modified-stopping declarations.
- `tests/`: exact combinatorial, reference, input, and reporting checks.
- `.github/workflows/check.yml`: Python checks and Lean build for a future remote.

Git is initialized locally; no remote or public release is configured. A project
license still needs to be selected before an open-source release.
