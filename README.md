# StatProof

Compute a two-sided Fisher exact test using exact integer and rational arithmetic,
and track the formal obligations needed for a Lean-backed statistical guarantee.
The [project brief](statistical_design_checker_project_brief.md) defines the scope.

**Working now:** the probability-ordered Fisher calculation, inclusive rejection
at `alpha = 1/20`, input validation, JSON reports, and a Lean-checked Fisher Type I
error theorem under the independent-binomial null model. The theorem covers every
common success probability in `[0, 1]`, including both endpoints. The `verify`
command now has Lean certify individual computed results and retain replayable
certificate bundles. The Python program as a whole is not formally verified.

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

## Verify the result with Lean

```sh
uv run --locked statproof verify examples/fixed_sample.toml \
  --control-successes 10 --treatment-successes 25
```

Or run `make verify-demo`. Lean independently checks the exact p-value, observed
table probability, support bounds, decision, and model error bound. A successful
report contains `status: "verified"`, `certificate_issued: true`, and a certificate
directory under `.statproof/certificates/`. Sampling assumptions remain explicit.

To choose the directory and recheck the bundle later:

```sh
uv run --locked statproof verify examples/fixed_sample.toml \
  --control-successes 10 --treatment-successes 25 \
  --output .statproof/my-example
uv run --locked statproof check-certificate .statproof/my-example
```

The output directory must not already exist. Bundles retain canonical inputs,
generated proof source, its compiled artifact, a backend transcript, source and
artifact hashes, exact dependency pins, and a property-specific certificate.
Replay checks the bindings and reruns Lean; file hashes alone do not prove a claim.

Run these commands from the source project, or provide `--project /path/to/statProof`.
The Python wheel also requires that source project and its Lean setup for verification.
`--timeout 120` sets the per-command backend timeout in seconds. A failed or
timed-out check remains unresolved and issues no certificate. See the
[certificate guide](docs/certificates.md) for scope and reproducibility details.

## Unsupported stopping modification

```sh
uv run --locked statproof test examples/data_dependent_stopping.toml \
  --control-successes 10 --treatment-successes 25
```

This computes the fixed-margin statistic but returns `decision: null` and an
unresolved obligation for the modified stopping procedure. A numerical threshold
comparison does not establish its Type I error guarantee.

`statproof inspect DESIGN.toml` lists the design's obligations without executing
the test. Reports reference `StatProof.fisher_typeI_error_le`, while explicitly
marking its application to this Python execution as unresolved. Neither command
invokes Lean or issues a verification certificate; use `verify` for that check.
`verify` also withholds certificates for the data-dependent stopping example.

| Command outcome | Exit code |
| --- | ---: |
| `test`: completed fixed-sample calculation, either decision | `0` |
| `verify` or `check-certificate`: all required checks passed | `0` |
| `test`: unsupported stopping rule; `inspect`: unresolved obligations | `1` |
| Verification failure, timeout, altered bundle, or unsupported stopping rule | `1` |
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

`make check` runs Python linting, formatting, tests, the Lean build, concrete Lean
examples, a source-placeholder guard, and a transitive check of the main theorems'
axioms. The check permits only `propext`, `Classical.choice`, and `Quot.sound`;
unexpected assumptions, including proof placeholders, fail CI. Real Lean
integration tests check issuance, replay, incorrect candidates, and tampering.
`make python-check` runs the Python-only suite; `make integration-check` runs the
checks that invoke Lean.

See the [proof walkthrough](docs/formal-proof.md) for the theorem statement,
how the proof fits together, and its remaining application boundaries.

For the optional live comparison with R (requires `Rscript`):

```sh
make reference-check
# Regenerate the small set of stored R reference results:
uv run --locked python scripts/compare_with_r.py --write-fixtures
```

The default test suite uses stored reference results and does not require R.
`make demo` runs the fixed-sample example.

## Layout

- `src/statproof/`: exact calculation, declarations, proof generation, certificate
  issuance/replay, reports, and CLI.
- `StatProof/`: finite p-value validity, hypergeometric normalization, the
  independent-binomial model, the Fisher error-bound theorem, and the per-result bridge.
- `docs/certificates.md`: commands, certificate contents, trust, and replay behavior.
- `docs/exact-test-spec.md`: mathematical and executable specification.
- `docs/development.md`: completed work and remaining proof obligations.
- `examples/`: fixed-sample and modified-stopping declarations.
- `tests/`: exact combinatorial, reference, input, reporting, and Lean example checks.
- `.github/workflows/check.yml`: Python checks and Lean build for a future remote.

Git is initialized locally; no remote or public release is configured. A project
license still needs to be selected before an open-source release.
