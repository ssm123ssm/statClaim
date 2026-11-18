# The statistical file-language prototype

Language version `0.12.0` provides a small declaration grammar over the existing
statistical objects and Lean backend. Claims, verification results, and calculation
results are first-class values. The statistical language is the researcher-facing
interface; the Lean and TOML interfaces remain supported.

| Module | Provides |
| --- | --- |
| `models.two_arm_binomial`, `sampling`, `tests.fisher` | Two-arm studies and Fisher's exact test (this guide) |
| `models.two_arm_continuous`, `tests.t` | Two means with cited t-tests ([cited methods](cited-methods.md)) |
| `models.two_arm_survival`, `tests.survival` | Two survival curves with the cited log-rank test |
| `tests.difference` | Exact test with a margin, such as non-inferiority ([planning](planning.md)) |
| `multiplicity.bonferroni` | Several endpoints ([multiple testing](multiple-testing.md)) |
| `planning` | Power targets and sample-size searches ([planning](planning.md)) |
| `tests.binomial` | One-sample exact test and confidence interval ([planning](planning.md)) |
| `estimation` | Confidence interval for a difference of two proportions ([planning](planning.md)) |
| `designs.two_stage` | Two-stage designs with an interim stop ([planning](planning.md)) |

The [catalogue](catalogue.md) lists every constructor and field.

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

let claim = typeI(analysis)
let verification = verify(claim)
```

After the usual project setup, run from the project directory:

```sh
# Compile a plan and inspect types, requested claims, and known requirements:
uv run --locked statclaim compile examples/first_class.stat

# Run the actual Lean verification and issue a certificate:
uv run --locked statclaim check examples/first_class.stat

# Discover the available constructors:
uv run --locked statclaim modules
```

`compile` performs no numerical calculations, builds, or artifact writes.
`check --elaborate-only` uses the same fast path. A successful compilation is not
a proof. Ordinary `check` explicitly executes the operations after the entire
file has parsed and type-checked and its known requirements have been inspected.

The output states the precise properties established, assumptions, and certificate
directory. `typeI(analysis)` requests the bound at the analysis's declared alpha,
uniformly over the equal-proportions null. It does not assert that this null is
true in the study. Alpha and sample sizes are exact inputs; observations are optional.

## Grammar

The formal grammar, every type, constructor, fixed value, limit and diagnostic
code are in the generated [language reference](catalogue.md). This section is
the short version.

The grammar has imports, immutable declarations, and operation calls:

```text
use module.name
let name = expression
verify(claim_expression)
calculate(claim_expression)
```

Expressions are references, calls, public field projections, lists, integers, exact decimals or rational
numbers, and double-quoted strings. Calls accept positional arguments followed
by named arguments. For example, `two_arm_binomial(100, 100)` is equivalent to
the named call above. Calls and lists can span lines and have trailing commas.
The original `verify claim_expression` and `calculate claim_expression` spellings
remain supported as sugar for the corresponding calls.
Comments start with `#`. Statements are separated by newlines; there are no
semicolons, assignments after declaration, loops, arbitrary arithmetic, Python
evaluation, or raw Lean escapes. Only verification and calculation calls may be
used as unnamed statements; other objects are introduced with `let`.

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
| `models.two_arm_binomial` | `two_arm_binomial(n_control, n_treatment)`, `assignment(n_control, n_treatment)`, `binary_outcome([better])`, `two_arm(assignment, outcome)`, `equal_proportions(model)`, `proportion_difference(model, value)`, `proportion_difference_at_most(model, value)` |
| `sampling` | `fixed(model)`, `adaptive(model)` |
| `tests.fisher` | `fisher(design, null, alpha)`, `observe(analysis, control_successes, treatment_successes)`, `typeI(analysis)`, `result(observation)` |
| `multiplicity.bonferroni` | `bonferroni(analyses, alpha, joint_law)`, `familywise(family)` |

The intermediate representation distinguishes models, sampling plans, hypotheses,
analyses, observations, families, and claim requests. Its source map retains
declaration and argument locations and named dependencies. Hypotheses describe
parameter restrictions without asserting their truth. Analysis constructors have
explicit supported-hypothesis contracts; the current Fisher analysis supports
equal proportions. See [hypothesis compatibility](hypothesis-contracts.md) for
same-model mismatches, source guidance, and the exact zero-difference alias.

The supported binomial model descriptions are matched structurally by their sizes.
Reusing a model or plan reuses its distributional specification. It does not prove
that real observations follow it or introduce independence between outcomes.
General equivalence of arbitrary future models is outside this prototype.

## Models from an assignment and an outcome

A two-arm model has two pieces: an assignment, which says how participants reach
the arms, and an outcome, which says what is measured on each participant. The
one-call constructors are shorthand:

```text
let arms = assignment(n_control=120, n_treatment=120)
let responders = two_arm(assignment=arms, outcome=binary_outcome(better="higher"))
let scores = two_arm(assignment=arms, outcome=continuous_outcome(better="lower"))
```

`two_arm(assignment=arms, outcome=continuous_outcome())` is the same model as
`two_arm_continuous(n_control=120, n_treatment=120)`, with the same claims and
evidence. A shared assignment states the arm sizes once, and a change to it is
reported against every model, analysis and claim built on it. Sharing does not
assume that the outcomes are independent. Read the pieces back as
`scores.assignment` and `scores.outcome`. See `examples/shared_assignment.stat`.

## First-class claims and execution results

The built-in operations are available without an additional import:

```text
verify(claim) -> VerificationResult
calculate(claim) -> CalculationResult
```

Both accept positional or named `claim` arguments. Verification accepts the
supported Type I, familywise, and observed-result claims. Calculation accepts
only an observed-result claim.

```text
let validity = typeI(analysis)
let checked = verify(validity)
let saved = checked
let checks = [checked, saved]
```

`validity` describes a proposition; it does not establish that proposition.
`checked` holds the result of an explicit execution. During compilation it has a
known type and an execution slot, but no result has been produced. Fast reports
represent it as `not_executed`, with no evidence.

Aliases and lists preserve the identity of execution results. The example above
executes one verification, not three. Two separate calls to `verify(validity)`
create two operations; there is no persistent proof cache. Calls inside lists
also work, and operations execute in source order, left to right within a list.

An executed verification result has one of these statuses:

| Status | Meaning |
| --- | --- |
| `verified` | Lean checked the claim; the result contains an `Evidence` object with certificate references, established properties, and required assumptions |
| `unresolved_obligation` | A known statistical requirement prevents the supported proof route; no evidence is supplied |
| `backend_error` | The verification backend could not complete the proof or certificate operation; no evidence is supplied |

Neither unresolved requirements nor backend errors disprove a claim. A successful
result establishes the listed claim under the listed assumptions, rather than
establishing that real data obey the model. A verification result cannot be passed
where a claim or an analysis is expected.

Calculation results carry the exact numerical calculation and, when supported,
the decision. Their status is `calculated` or `unresolved_obligation`; they contain
no formal evidence. All result values are immutable and identify the source hash
for their execution. Public fields can be projected in `.stat` expressions and
inspected through `--json`. See [public fields and the Claims view](fields-and-claims.md)
for optional evidence, compilation versus execution, and the field schema.
User-defined functions, functions as values, and operations that consume checked
evidence remain future work. The built-in names
`verify` and `calculate` cannot be used as binding names.

## Compilation and explicit execution

The source compiles to a typed statistical execution plan, not Python source or
machine code:

```text
.stat source -> parser -> typed objects and planned operations
                                   |
                         known requirement checks
                                   |
                          explicit check command
                             /             \
                   Python calculation    generated Lean proof
                             |             |
                     CalculationResult   Lean checks -> VerificationResult
```

The Python runtime orchestrates execution. Verification adapters instantiate
existing formal definitions and theorems in generated `Proof.lean` files. Lean
checks those proofs; Python retains their certificates and binds results to their
source snapshot. We do not translate arbitrary statistical source into arbitrary
Python or promise automatic discovery of mathematical proofs.

`statclaim.language_compiler.compile_source(Source(...))` is the backend-free API
for tooling. It returns the typed program, diagnostics, and per-operation known
requirements. These include invalid types and domains, incompatible models,
overallocated Bonferroni levels, and unjustified adaptive stopping. It can report
multiple unmet requirements for one operation, with source locations preserved
through aliases. The compiler never calls numerical evaluators, Lean, or artifact
writers. A clean plan reports `elaborated`, meaning no known blocker was detected.

`statclaim compile file.stat --json` exposes this analysis on the command line.
Planned operations report `planned` or `blocked`; their result values remain
`not_executed`. The explicit `statclaim check file.stat` command performs supported
operations and returns named results. Independent operations continue when one
verification has unmet requirements or a backend error. Any syntax or type error
anywhere in the file prevents all execution and artifact creation.

Full formal verification still requires running Lean, even if a future build
command chooses to do that work during compilation. Ordinary editor analysis
should call the fast compiler API without executing the plan.

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
uv run --locked statclaim check examples/two_outcomes.stat
```

The named analyses occupy two endpoint slots under the declared marginal-law
contract. Dependence between endpoints is unrestricted. The guarantee counts
rejections of true endpoint nulls for every joint parameter configuration. Each
endpoint still requires the independent-binomial law within its two arms.
See the [multiple-testing guide](multiple-testing.md) for the precise theorem.

A family has two to twenty named Fisher analyses. Their allocated
levels must sum to at most family alpha. `examples/overallocated.stat` exposes
that unmet requirement at the alpha declaration. `examples/adaptive.stat` points
to its unjustified adaptive sampling declaration. Both remain unresolved, without
issuing the requested certificate. Neither is a proof of excessive actual error.

## Optional observations and results

```text
let data = observe(analysis=analysis, control_successes=10, treatment_successes=25)
let observed_claim = result(data)
let computation = calculate(observed_claim)
let checked = verify(observed_claim)
```

Run `examples/fisher_result.stat` for the complete example. `observe` checks the
count domains. `calculate` proposes the exact value and decision through Python;
it creates no formal evidence. `verify(observed_claim)` independently checks that
result and the scoped error guarantee through the existing Lean certificate
pipeline. A numerical result and a Type I guarantee remain different claim kinds.

## Reports, replay, and source changes

```sh
uv run --locked statclaim check examples/fisher.stat --output .statclaim/my-program
uv run --locked statclaim check-certificate .statclaim/my-program/request-001
```

`--output` must name a new directory. By default, a run directory is allocated
under `.statclaim/programs/`. A run retains:

- `Source.stat`: the UTF-8 source snapshot used for this execution.
- `run.json`: the source hash, normalized typed objects, source locations,
  dependencies, per-request statuses, diagnostics, and certificate references.
- `request-NNN/`: ordinary certificate bundles for successful verification
  requests, numbered in execution order. Calculation-only or unresolved
  requests have no certificate bundle.

`run.json` is a provenance/reporting record, not a mathematical certificate.
Its `program` records static objects and typed execution slots. Its `values` map
contains named values with resolved results, and each request also exposes its
result as `value`. Backend reports remain in each request's `report`. This keeps
the aggregate/per-request status interface compatible: a backend error still
produces aggregate `unresolved_obligation` and exit code 1, while its named
`VerificationResult` has the more specific `backend_error` status.
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
Immutable result values continue to describe their recorded `source_sha256`;
their evidence must not be presented as verification of the newly edited file.

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
defines typed objects, constructor schemas, module builders, elaboration, and
planned operation slots. `language_fields.py` is the shared public field schema.
`language_inspection.py` supplies pure claim descriptions and requirements for
reports and the IDE Claims view. `language_compiler.py` exposes backend-free compilation
and known requirement diagnostics. `language_values.py` defines immutable runtime
results and evidence. `language_runner.py` lowers supported claim kinds into the
existing design, family, and result operations and resolves named execution values.
Module constructors extend the registry without
changing the parser; a new statistical claim additionally needs an explicit
verification adapter and its Lean proof. Similar-looking objects alone do not
authorize reuse of a theorem. This is a built-in module registry, not a runtime
loader for untrusted third-party plugins.

Integration tests compare the canonical inputs, hypotheses, levels, and result
values with the existing TOML route and replay the resulting Lean certificates.
The Lean examples remain the reference for direct proof construction and manual
proofs. The standalone route currently offers simpler declarations and domain
diagnostics, while relying on a trusted translation layer.

File execution, first-class claims/results, the fast compiler, a stdio LSP, and
a minimal VS Code extension are implemented. The [editor guide](editor.md)
describes live diagnostics, completion, hover, definition lookup, and explicit
verification. Interactive REPL sessions remain future work.
