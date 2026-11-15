# StatProof

Verify a declared fixed two-arm binomial design's Fisher Type I error guarantee
before collecting data. Optionally calculate and certify observed test results
using exact integer and rational arithmetic.
The [project brief](statistical_design_checker_project_brief.md) defines the scope.

**Working now:** the probability-ordered Fisher calculation, inclusive rejection
at a configurable exact alpha (default `1/20`), JSON reports, and a Lean-checked Fisher Type I
error theorem under the independent-binomial null model. The theorem covers every
common success probability in `[0, 1]`, including both endpoints. `verify-design`
issues a design-level certificate without observations. `verify-result` (also
available as `verify`) certifies individual computed results. `verify-family`
composes two Fisher analyses into a strong familywise error guarantee using
Bonferroni, with explicit marginal-law contracts. All three retain replayable
certificate bundles. The Python program as a whole is not formally verified.

## Write a statistical file

The file-language prototype now runs alongside the Lean and TOML interfaces:

```text
use models.two_arm_binomial
use sampling
use tests.fisher

let study = two_arm_binomial(n_control=100, n_treatment=100)
let plan = fixed(model=study)
let null = equal_proportions(model=study)
let analysis = fisher(design=plan, null=null, alpha=1/20)
let claim = typeI(analysis)
let verification = verify(claim)
```

After setup, run:

```sh
uv run --locked statproof compile examples/first_class.stat
uv run --locked statproof check examples/first_class.stat
uv run --locked statproof check examples/fisher.stat
uv run --locked statproof check examples/two_outcomes.stat
uv run --locked statproof modules
```

The first command compiles a typed execution plan, checks known requirements,
and displays the intended claims without calculations, Lean, or artifact writes.
The other `check` commands explicitly execute calculations and verification,
issuing replayable certificates for supported claims. `check --elaborate-only`
remains an alternative spelling of the fast path. Invalid declarations and unmet
requirements have source locations. Each execution retains its source, typed
objects, named result values, and per-request results. Claims and results can be
aliased or collected in lists; reusing a result does not rerun its operation.
See the [file-language guide](docs/stat-language.md) for grammar, optional
observations, report scope, replay, and the comparison with Lean.

## Try the IDE

A stdio LSP and a minimal VS Code extension provide diagnostics, completion,
hover, field access, go-to-definition, and a Claims view using the same compiler.
Editing never invokes Lean. Run **StatProof: Show Claims** to inspect requirements,
assumptions, and matching evidence. See [public fields and the Claims view](docs/fields-and-claims.md)
and `examples/fields.stat` for typed projections such as `verification.status`
and optional `verification.evidence.certificate.file`.
The explicit **StatProof: Verify Current File** command saves and checks a source
snapshot, with a versioned status that becomes stale after edits.

```sh
npm --prefix extensions/vscode ci --ignore-scripts
code --new-window "$PWD"
```

Select **Run and Debug → StatProof Extension** and press **F5**. Open a `.stat`
example in the new development window. See the [editor guide](docs/editor.md)
for isolated launch, exact usage, testing, configuration, and limitations.

## Verify a design before data

The language also checks analysis/hypothesis compatibility while editing. For
example, declaring `proportion_difference(study, value=0.10)` and passing that null
to `fisher` reports the unsupported null form with expected/declared meanings and
guidance. See [hypothesis contracts](docs/hypothesis-contracts.md) and
`examples/hypothesis_mismatch.stat`. Exactly zero equality difference is accepted
as the existing equal-proportions null; inequality at zero remains distinct.

After setup, run from this project folder:

```sh
uv run --locked statproof verify-design examples/fixed_sample.toml
```

Or run `make design-demo`. This loads the declared positive sample sizes and fixed
plan, constructs the shared Lean model and analysis, checks sampling compatibility,
and instantiates the uniform Type I error theorem. It does not request observations,
calculate a p-value, or return a test decision.

Successful output has `verification_scope: "design"`, `status: "verified"`, and
`certificate_issued: true`. The certificate names only the design-level properties
and assumptions. It establishes neither power nor coverage nor that the real
study follows the declared model. The null is a condition under which the error
bound holds, rather than a claim that the null is true in the real study.

To save and replay the design certificate:

```sh
uv run --locked statproof verify-design examples/fixed_sample.toml \
  --output .statproof/my-design
uv run --locked statproof check-certificate .statproof/my-design
```

For the same workflow written in Lean, see `examples/DesignGuarantee.lean` and run
`make design-objects-demo`. Observations and per-result checks are optional later steps.

## Choose alpha

Add an optional analysis table to a single-design declaration:

```toml
[analysis]
alpha = "1/40"
```

Use an exact string, such as `"1/40"` or `"0.025"`; numeric TOML floats are
rejected. Levels from zero through one are supported. Omitting the table keeps
the default `1/20`. Both the rejection decision and the proved bound use this
setting. The p-value itself is unchanged. Run the 2.5% design example with:

```sh
make alpha-demo
```

The Lean equivalent is `examples/ConfigurableAlpha.lean`. The
[Lean guide](docs/lean-objects.md) explains how the level enters the analysis and provider.

## Compose two analyses

`examples/two_outcomes.toml` declares two Fisher analyses, each at `1/40`, and
requests a probability of any false rejection of at most `1/20`:

```sh
make family-demo
# Or choose a certificate directory and replay it:
uv run --locked statproof verify-family examples/two_outcomes.toml \
  --output .statproof/my-family
uv run --locked statproof check-certificate .statproof/my-family
```

The certificate has `verification_scope: "family"`. It proves a conditional
guarantee for every joint probability law with the declared binomial marginals.
It does not infer the actual joint sampling law. Independence between outcomes
is unnecessary; each outcome still requires independent binomial arms.
The guarantee covers every configuration of true and false endpoint nulls.

`examples/two_outcomes_overallocated.toml` instead assigns 5% to each test while
requesting 5% overall. `verify-family` reports an unmet allocation requirement
and issues no certificate. This does not prove that its actual familywise error
exceeds 5%; the requested Bonferroni contract has not been satisfied.

Run `make composition-demo` for the Lean version. See the
[multiple-testing guide](docs/multiple-testing.md) for declarations, proofs, and scope.

## Optionally run the test

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
uv run --locked statproof verify-result examples/fixed_sample.toml \
  --control-successes 10 --treatment-successes 25
```

Or run `make verify-demo`. The original `verify` command is an alias for this
result workflow. Lean independently checks the exact p-value, observed
table probability, support bounds, decision, and model error bound. A successful
report contains `status: "verified"`, `certificate_issued: true`, and a certificate
directory under `.statproof/certificates/`. Sampling assumptions remain explicit.

To choose the directory and recheck the bundle later:

```sh
uv run --locked statproof verify-result examples/fixed_sample.toml \
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

`statproof inspect DESIGN.toml` lists design-level obligations without requiring
observations. It references the shared object's model theorem and leaves formal
verification unresolved until `verify-design` runs. The fast `test` command
similarly leaves its calculation's formal status unresolved until `verify-result`.
Neither inspection nor calculation invokes Lean or issues a certificate.
Both verification modes withhold certificates for the data-dependent stopping
example. For a design-only demonstration, run:

```sh
uv run --locked statproof verify-design examples/data_dependent_stopping.toml
```

| Command outcome | Exit code |
| --- | ---: |
| `test`: completed fixed-sample calculation, either decision | `0` |
| `verify-design`, `verify-family`, `verify-result` / `verify`, or replay: checks passed | `0` |
| `test`: unsupported stopping; `inspect` / `inspect-family`: unresolved obligations | `1` |
| Verification failure, timeout, altered bundle, or unsupported stopping rule | `1` |
| Malformed declaration, invalid data, or argument error | `2` |

## Development setup

The first shared statistical objects are now available in Lean. Run
`make objects-demo` to check the complete Fisher example built from models,
sampling plans, analyses, observations, claims, and typed certificates. See the
[Lean object guide](docs/lean-objects.md) and the
[parallel language comparison plan](docs/core-object-model.md).

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
