# The statistical file-language prototype

Language version `0.43.0` provides a small declaration grammar over the existing
statistical objects and Lean backend. Claims, verification results, and calculation
results are first-class values. The statistical language is the researcher-facing
interface; the Lean and TOML interfaces remain supported.

| Module | Provides |
| --- | --- |
| `models.two_arm_binomial`, `sampling`, `tests.fisher` | Two-arm studies and Fisher's exact test (this guide) |
| `models.two_arm_continuous`, `tests.t` | Two means with cited t-tests ([cited methods](cited-methods.md)) |
| `models.two_arm_survival`, `tests.survival` | Two survival curves with the cited log-rank test |
| `tests.difference` | Exact test with a margin, such as non-inferiority ([planning](planning.md)) |
| `tests.wald`, `tests.score`, `tests.pearson`, `tests.likelihood_ratio`, `tests.farrington_manning` | Finite-sample Type I error audits for two-arm binomial tests ([scope](scope.md)) |
| `tests.association` | Tests of association, including an audit of the uncorrected McNemar rule ([observational studies](observational.md#matched-pairs)) |
| `tests.randomisation` | Randomisation test of the sharp null, proved in Lean (below) |
| `multiplicity.bonferroni` | Several endpoints ([multiple testing](multiple-testing.md)) |
| `planning` | Power targets and sample-size searches ([planning](planning.md)) |
| `tests.binomial` | One-sample exact test, confidence interval, and Type I error audits for the score and Wald rules ([scope](scope.md)) |
| `estimation` | Confidence interval for a difference of two proportions ([planning](planning.md)) |
| `designs.two_stage` | Two-stage designs with an interim stop ([planning](planning.md)) |
| `designs.group_sequential` | Interim looks: a split of the level, spending boundaries and look-size searches ([multiple testing](multiple-testing.md), [planning](planning.md)) |

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

# Print the program as StatClaim compiled it, the form a certificate binds:
uv run --locked statclaim compile --canonical examples/first_class.stat

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
The one-call constructors also take `population` and `name`, described below;
randomisation and repeated measurements need the pieces.

An outcome can have a name: `binary_outcome(name="response")`. One name is one
outcome, so models that share a name must agree on its kind and `better`
(`outcome_conflict` otherwise). A family, sequence or graph that asks the same
question of a named outcome twice, the same test of the same null on the same
participants at any level, is refused with `duplicate_analysis`. Different
questions of one outcome, such as non-inferiority and then superiority, are
fine. Without names, two identical analyses could be two outcomes measured on
the same participants, so they are not refused.

The pieces also declare a design that a test's assumptions can contradict:

```text
let visits = two_arm(assignment=arms, outcome=continuous_outcome(measurements=3))
let clinics = cluster_assignment(clusters_control=12, clusters_treatment=12,
                                 n_control=240, n_treatment=240)
```

A test that takes one value per participant is refused for `visits`, and a test
that assumes independent participants is refused for a model built on
`clinics`, both with `unit_mismatch`. The message names a test that fits, such
as `cluster_t_test` for clinics, or suggests `declared_test(...)`. Sites in a trial that randomises participants
are not clusters. See `examples/declared_design.stat` and
[cited methods](cited-methods.md#clusters-and-repeated-measurements).

## Randomisation tests

An assignment can say how it was randomised. `randomisation="complete"` means
every split of the units into arms of the declared sizes was equally likely.
A randomisation test then has a level that follows from the design alone:

```text
let arms = assignment(n_control=20, n_treatment=20, randomisation="complete")
let pain = two_arm(assignment=arms, outcome=continuous_outcome(better="lower"))
let analysis = randomisation_test(design=fixed(model=pain), null=no_effect(model=pain),
                                  alpha=1/20)
```

Lean proves, once, that for any statistic fixed in advance the randomisation
p-value is at most alpha with probability at most alpha, whatever the outcomes.
The claim is `verified`. Its null is the sharp null `no_effect`: treatment
changes no participant's outcome. It is not `equal_means`, and neither stands in
for the other: each test's contract refuses the other's null.

Most trials randomise within strata or in blocks. Declare that instead, and the
same theorem covers it, because each stratum or block is randomised on its own:

```text
let arms = assignment(n_control=24, n_treatment=24, randomisation="blocked", block_size=4,
                      strata=[stratum(control=10, treatment=10),
                              stratum(control=14, treatment=14)])
```

`randomisation="stratified"` with `strata=[...]` means complete randomisation
within each stratum; `"blocked"` with `block_size` means every block of that size
has the allocation of its stratum (or of the whole trial). The strata must add up
to the arm sizes and the blocks must divide them, or the assignment is refused.
Strata and blocks count randomised units, so a pair-matched cluster trial is
`cluster_assignment(..., randomisation="blocked", block_size=2)`. See
`examples/stratified_randomisation.stat`.

With `cluster_assignment(..., randomisation="complete")` the units are the
clusters, and the test permutes clusters. This is a proved analysis for a
cluster-randomised trial. A design with too few splits to reach its level, such
as two clusters per arm at 1/20, is refused with `never_rejects`; an assignment
without a declared scheme is refused with `undeclared_randomisation`. The
p-value counts every split; a p-value from a random sample of splits is not
covered by the exact form. For that, add `draws`:

```text
let analysis = randomisation_test(design=fixed(model=pain), null=no_effect(model=pain),
                                  alpha=1/20, draws=9999)
```

The p-value then compares the observed assignment with 9,999 drawn independently
and uniformly, counting the observed one among them, the usual `(1 + count) /
(draws + 1)`. Lean proves this has Type I error at most alpha for any number of
draws, with the draws' independence stated as a product of uniform laws. Too
few draws to reach the level, such as 18 at 1/20, are refused with
`never_rejects`. See `examples/randomisation.stat`.

A randomisation test can be a member of a Bonferroni family, a fixed sequence or
a graph, like any exact test: Lean checks the combination, and the member's own
bound is proved separately. It cannot be a look of a sequential design. See
`examples/randomisation_family.stat`.

### Who is analysed

An assignment can also say who is analysed. `population="randomised"` means
everyone randomised, in the arm they were assigned to (intention to treat).
`population="per_protocol"` means participants excluded after randomisation are
left out, and the arm sizes count those analysed.

A randomisation test's level rests on analysing everyone randomised. Without a
population, that is listed as assumed (`analysed_as_randomised`); with
`"randomised"` the file states it, and the report lists it as declared. With
`"per_protocol"` the test is refused with `population_mismatch`. Other tests take
either population, and their claims list which population the bound covers
(`randomised_population` or `per_protocol_population`). A per-protocol claim also
lists as assumed that exclusions followed rules fixed before outcomes were
observed (`prespecified_exclusions`): its arm sizes are counted after them. See
`examples/analysis_population.stat` and tutorial lesson 22.

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

These statuses cover common outcomes of `verify(...)`.

| Status | Meaning |
| --- | --- |
| `verified` | Lean checked the claim; the result contains an `Evidence` object with certificate references, established properties, and required assumptions |
| `refuted` | Lean checked a counterexample to the requested claim. The run reports the witness and its certificate. |
| `unresolved_obligation` | A known statistical requirement prevents the supported proof route; no evidence is supplied |
| `backend_error` | The verification backend could not complete the proof or certificate operation; no evidence is supplied |

For a Type I error audit, a single null parameter value whose rejection
probability exceeds alpha is enough to refute the claim. An open requirement or
a backend error leaves the claim's truth open. Checked results apply to the
declared model under its listed assumptions. A verification result cannot be
passed where a claim or an analysis is expected. See the
[complete status list](catalogue.md#statuses-and-other-fixed-values).

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
                   Python calculation    the program as Lean data
                             |             |
                     CalculationResult   Lean semantics -> contracts and claims
```

The Python runtime orchestrates execution. The canonical program and the values
the run reports are written as Lean data. The semantics in `StatClaim/Semantics/`
defines what the program claims and which contracts it must meet; Lean decides
the contracts and proves the claims with one soundness theorem. Python retains the
certificate and binds results to their source snapshot. We do not translate
arbitrary statistical source into arbitrary Python or promise automatic discovery
of mathematical proofs.

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
uv run --locked statclaim check-certificate .statclaim/my-program/lean
```

`--output` must name a new directory. By default, a run directory is allocated
under `.statclaim/programs/`. A run retains:

- `Source.stat`: the UTF-8 source snapshot used for this execution.
- `run.json`: the source hash, normalized typed objects, source locations,
  dependencies, per-request statuses, diagnostics, and certificate references.
- `lean/`: the program's certificate. Every program a check runs is built in
  Lean once (`statclaim_program_certificate`), even one that only calculates:
  Lean decides the declarations' contract facts and checks proofs and
  refutations of `verify` claims. Each request takes its checked result from the
  bundle. If a proof attempt leaves a claim unresolved, the rest can be built
  again in `lean-proved/`. See [certificate replay](certificates.md).

`run.json` is a provenance/reporting record, not a mathematical certificate.
Its `program` records static objects and typed execution slots. Its `values` map
contains named values with resolved results, and each request also exposes its
result as `value`. Backend reports remain in each request's `report`. This keeps
the aggregate/per-request status interface compatible: a backend error still
produces aggregate `unresolved_obligation` and exit code 1, while its named
`VerificationResult` has the more specific `backend_error` status.
`check-certificate` replays the `lean/` directory, not the parent run directory.
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

Independent requests have separate results. A run can retain a verified claim
alongside a refuted or unresolved claim and exit with code 1. Inspect the
per-request statuses to see what the certificate establishes.

Add `--json` to obtain the structured report. Exit codes are:

| Code | Meaning |
| --- | --- |
| `0` | Requested verification succeeded, calculation completed, or explicit elaboration-only checks passed; consult the reported status |
| `1` | A requested guarantee was refuted, a request remains unresolved, or the source became stale |
| `2` | Syntax/type/domain errors, malformed arguments, or file/output errors |

With no requests, the status is only `elaborated`, and no artifacts are written.

## Implementation and parallel comparison

`language_syntax.py` handles the common grammar and source spans. The `language/`
package defines typed objects, constructor schemas, module builders, elaboration, and
planned operation slots. `language_fields.py` is the shared public field schema.
`language_inspection.py` supplies pure claim descriptions and requirements for
reports and the IDE Claims view. `language_compiler.py` exposes backend-free compilation
and known requirement diagnostics. `language_values.py` defines immutable runtime
results and evidence. `language_runner.py` lowers supported claim kinds into the
existing design, family, and result operations and resolves named execution values.
Module constructors extend the registry without
changing the parser; a new statistical claim additionally needs its meaning in the
Lean semantics and a proof. Similar-looking objects alone do not
authorize reuse of a theorem. This is a built-in module registry, not a runtime
loader for untrusted third-party plugins.

Integration tests build the examples' program certificates and replay them,
including tampered bundles. The Lean examples remain the reference for direct
proof construction and manual proofs. The parser and the elaborator remain
trusted; Lean checks that the data it reads is the compiled program and proves
that the printed form determines it.

File execution, first-class claims/results, the fast compiler, a stdio LSP, and
a minimal VS Code extension are implemented. The [editor guide](editor.md)
describes live diagnostics, completion, hover, definition lookup, and explicit
verification. Interactive REPL sessions remain future work.
