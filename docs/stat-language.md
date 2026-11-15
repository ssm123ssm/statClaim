# The statistical file-language prototype

Version `0.1.0` provides a small declaration grammar over the existing statistical
objects and Lean backend. Keep using the Lean interface alongside it: both routes
are supported while we compare their usability and extension requirements.

## First file

Save the following as `study.stat`, or use `examples/fisher.stat`:

```text
use models.two_arm_binomial
use sampling
use tests.fisher

let study = two_arm_binomial(n_control=100, n_treatment=100)
let plan = fixed(model=study)
let null = equal_proportions(model=study)
let analysis = fisher(design=plan, null=null, alpha=1/20)

verify typeI(analysis)
```

After the usual project setup, run from the project directory:

```sh
# Fast inspection of types, requested claims, and known contract obligations:
uv run --locked statproof check examples/fisher.stat --elaborate-only

# Run the actual Lean verification and issue a certificate:
uv run --locked statproof check examples/fisher.stat

# Discover the available constructors:
uv run --locked statproof modules
```

`--elaborate-only` performs no numerical calculations, builds, or certificate
writes. A successful elaboration is not a proof. Ordinary `check` executes the
requests after the entire file has parsed and type-checked successfully.

The output states the precise properties established, assumptions, and certificate
directory. `typeI(analysis)` requests the bound at the analysis's declared alpha,
uniformly over the equal-proportions null. It does not assert that this null is
true in the study. Alpha and sample sizes are exact inputs; observations are optional.

## Grammar

The grammar has four statement forms:

```text
use module.name
let name = expression
verify claim_expression
calculate claim_expression
```

Expressions are references, calls, lists, integers, exact decimals or rational
numbers, and double-quoted strings. Calls accept positional arguments followed
by named arguments. For example, `two_arm_binomial(100, 100)` is equivalent to
the named call above. Calls and lists can span lines and have trailing commas.
Comments start with `#`. Statements are separated by newlines; there are no
semicolons, assignments after declaration, loops, arbitrary arithmetic, Python
evaluation, or raw Lean escapes.

```text
let threshold = 0.025       # exactly 1/40, not a binary floating-point value
let analysis = fisher(plan, null, alpha=threshold)
```

Binding names are immutable, and references must follow their declarations.
Unknown modules, unimported constructors, unknown names, wrong argument types,
invalid counts, invalid levels, and mismatched model/null combinations have
line-and-column diagnostics. There is no automatic forward-reference resolution.
Names are ASCII identifiers; module names may contain dots. Strings use JSON
escapes. Rational denominators must be nonzero; levels must be in `[0,1]`.

## Typed objects and meaning

| Module | Constructors and claims |
| --- | --- |
| `models.two_arm_binomial` | `two_arm_binomial(n_control, n_treatment)`, `equal_proportions(model)` |
| `sampling` | `fixed(model)`, `adaptive(model)` |
| `tests.fisher` | `fisher(design, null, alpha)`, `observe(analysis, control_successes, treatment_successes)`, `typeI(analysis)`, `result(observation)` |
| `multiplicity.bonferroni` | `bonferroni(analyses, alpha, joint_law)`, `familywise(family)` |

The intermediate representation distinguishes models, sampling plans, hypotheses,
analyses, observations, families, and claim requests. Its source map retains
declaration and argument locations and named dependencies. The only supported
hypothesis constructor currently denotes equality of arm probabilities; it does
not turn a hypothesis into an assumed fact.

The supported binomial model descriptions are matched structurally by their sizes.
Reusing a model or plan reuses its distributional specification. It does not prove
that real observations follow it or introduce independence between outcomes.
General equivalence of arbitrary future models is outside this prototype.

## Compose outcomes

`examples/two_outcomes.stat` adds:

```text
use multiplicity.bonferroni
let primary_outcome = fisher(design=plan, null=null, alpha=1/40)
let secondary_outcome = fisher(design=plan, null=null, alpha=1/40)
let outcomes = bonferroni(
    analyses=[primary_outcome, secondary_outcome],
    alpha=1/20,
    joint_law="binomial_marginals",
)
verify familywise(outcomes)
```

```sh
uv run --locked statproof check examples/two_outcomes.stat
```

The named analyses occupy two endpoint slots under the declared marginal-law
contract. Dependence between endpoints is unrestricted. The guarantee counts
rejections of true endpoint nulls for every joint parameter configuration. Each
endpoint still requires the independent-binomial law within its two arms.
See the [multiple-testing guide](multiple-testing.md) for the precise theorem.

The first adapter supports exactly two named Fisher analyses. Their allocated
levels must sum to at most family alpha. `examples/overallocated.stat` exposes
that unmet requirement at the alpha declaration. `examples/adaptive.stat` points
to its unjustified adaptive sampling declaration. Both remain unresolved, without
issuing the requested certificate. Neither is a proof of excessive actual error.

## Optional observations and results

```text
let data = observe(analysis=analysis, control_successes=10, treatment_successes=25)
calculate result(data)
verify result(data)
```

Run `examples/fisher_result.stat` for the complete example. `observe` checks the
count domains. `calculate` proposes the exact value and decision through Python;
it creates no formal evidence. `verify result(data)` independently checks that
result and the scoped error guarantee through the existing Lean certificate
pipeline. A numerical result and a Type I guarantee remain different claim kinds.

## Reports, replay, and source changes

```sh
uv run --locked statproof check examples/fisher.stat --output .statproof/my-program
uv run --locked statproof check-certificate .statproof/my-program/request-001
```

`--output` must name a new directory. By default, a run directory is allocated
under `.statproof/programs/`. A run retains:

- `Source.stat`: the UTF-8 source snapshot used for this execution.
- `run.json`: the source hash, normalized typed objects, source locations,
  dependencies, per-request statuses, diagnostics, and certificate references.
- `request-NNN/`: ordinary certificate bundles for successful verification
  requests, using their statement positions. Calculation-only or unresolved
  requests have no certificate bundle.

`run.json` is a provenance/reporting record, not a mathematical certificate.
`check-certificate` replays a request directory, not the parent run directory.
The certificate binds canonical mathematical inputs and generated Lean statements;
it does not certify the spelling of the original `.stat` source. The parser,
elaborator, lowering, and report binding remain trusted application components.
Review the source snapshot and normalized objects when assessing that mapping.

Every execution elaborates afresh and invokes Lean afresh for verification.
There is no persistent proof-status cache. Changing a relevant declaration changes
the lowered request and requires new evidence. Existing certificates continue to
describe their old inputs; they are not automatically attached to edited code.
If the original source is edited/deleted, or its retained snapshot changes during
execution, the aggregate status is `stale_source`; rerun the current file.

Independent requests have separate results. A run can retain a successfully
verified claim while another remains unresolved; the aggregate exit code is then
1. `certificate_issued` means at least one request issued a certificate. Inspect
the per-request statuses for its scope.

Add `--json` to obtain the structured report. Exit codes are:

| Code | Meaning |
| --- | --- |
| `0` | Requested verification succeeded, calculation completed, or explicit elaboration-only checks passed; consult the reported status |
| `1` | A requested guarantee/calculation remains unresolved, or the source became stale |
| `2` | Syntax/type/domain errors, malformed arguments, or file/output errors |

With no requests, the status is only `elaborated`, and no artifacts are written.

## Implementation and parallel comparison

`language_syntax.py` handles the common grammar and source spans. `language.py`
defines typed objects, constructor schemas, module builders, and elaboration.
`language_runner.py` lowers supported claim kinds into the existing design,
family, and result operations. Module constructors extend the registry without
changing the parser; a new statistical claim additionally needs an explicit
verification adapter and its Lean proof. Similar-looking objects alone do not
authorize reuse of a theorem. This is a built-in module registry, not a runtime
loader for untrusted third-party plugins.

Integration tests compare the canonical inputs, hypotheses, levels, and result
values with the existing TOML route and replay the resulting Lean certificates.
The Lean examples remain the reference for direct proof construction and manual
proofs. The standalone route currently offers simpler declarations and domain
diagnostics, while relying on a trusted translation layer.

This milestone implements file execution. Interactive sessions, completion,
an LSP, and a decision about the primary interface remain future work. The module
schemas and source-aware elaborator provide concrete inputs for those experiments.
