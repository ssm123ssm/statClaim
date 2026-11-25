# Configurable Fisher levels and Bonferroni composition

A reusable Bonferroni proof composes two to twenty Fisher analyses. It needs no
observed counts. Dependence between outcomes is unrestricted. In the file
language, see `examples/two_outcomes.stat` and `examples/three_outcomes.stat`.

## Declare the family

```text
# The same family as two_outcomes.toml, using the common declaration grammar.
use models.two_arm_binomial
use sampling
use tests.fisher
use multiplicity.bonferroni

let study = two_arm_binomial(n_control=200, n_treatment=100)
let plan = fixed(model=study)
let null = equal_proportions(model=study)
let primary_outcome = fisher(design=plan, null=null, alpha=1/40)
let secondary_outcome = fisher(design=plan, null=null, alpha=1/40)

let outcomes = bonferroni(
    analyses=[primary_outcome, secondary_outcome],
    alpha=1/20,
    joint_law="binomial_marginals",
)
verify familywise(outcomes)
```

Each member is its own analysis declaration, whose name labels its outcome; listing
one declaration under two names is rejected. Arm sizes may differ between analyses.
Levels are exact; `0.025` and `1/40` are the same rational. Unequal allocations are
supported provided their sum does not exceed the family's level. Both analyses and
the allocation must be specified before observing results.

```sh
uv run --locked statclaim check examples/two_outcomes.stat --output .statclaim/two-outcomes
uv run --locked statclaim check-certificate .statclaim/two-outcomes/lean
```

## What is proved

For each outcome `i`, let `H_i(theta)` state equality of its arm probabilities,
and `R_i` be rejection by its Fisher analysis at the allocated level `alpha_i`.
The per-outcome theorem supplies:

```text
For every joint parameter theta:
  H_i(theta) implies P_theta(R_i) <= alpha_i.
```

The Bonferroni theorem proves:

```text
P_theta(at least one rejection of a true H_i)
  <= sum_i alpha_i
  <= family_alpha.
```

This is strong familywise error control: the statement includes configurations
with only one true null and with no true nulls. It is not restricted to the case
where all nulls are true. The proof is a finite union bound and makes no
independence assumption between outcomes.

The sampling contract remains essential. Each outcome's pair of counts must have
the product-binomial marginal law with its declared sizes and two success
probabilities. Those probabilities may differ under the alternative. The two
outcomes can be dependent even though the arms within each outcome have the
specified independent-binomial law.

`joint_law = "binomial_marginals"` requests a theorem universally quantified over
probability-law families satisfying these marginal equalities. The certificate
checks that conditional theorem. It does not construct or empirically validate
the actual study's joint law. In a concrete Lean application, the user supplies
the law and proves its marginal contract before receiving the composed guarantee.

## The Lean building blocks

- `SignificanceLevel` stores a rational alpha and proofs that `0 <= alpha <= 1`.
- `Fisher.procedure sizes level` sets the rejection threshold.
- `Fisher.analysis sizes design level` binds it to the design and null.
- `Fisher.module sizes level` supplies its Type I guarantee after compatibility.
- `Bonferroni.Family` describes finitely many hypotheses, rejection events, and
  nonnegative budgets on a common sampling-law family.
- `Bonferroni.module` requires proved marginal bounds and an adequate allocation,
  then returns a `FamilywiseGuarantee` containing a certificate.
- `FisherFamily.MarginalContract` requires the two projected laws to match the
  respective binomial models. `marginal_bound` transports an individual Fisher
  guarantee along such an equality.
- `FisherFamily.module` combines those pieces for two outcomes;
  `FisherFamilyN` does the same for any finite number.

`examples/MultipleTesting.lean` supplies a concrete independent-outcome joint law,
proves its marginals, and obtains the guarantee. `tests/lean/Composition.lean`
also composes two identical rejection events on the same law, demonstrating that
perfect dependence is permitted.

## Unmet requirements and certificate scope

Two 5% allocations do not satisfy a 5% family budget. The overallocated example
returns `unresolved_obligation` at stage `allocation`, without invoking Lean or
issuing a certificate. A different theorem might justify a tighter bound for a
particular joint law; this allocation failure does not demonstrate excessive error.
Data-dependent stopping likewise remains unresolved until separately justified.

Family certificates bind the analysis names/order, sample sizes, stopping plans,
levels, family bound, marginal-law contract, test/module versions, generated
statements, and environment. Replay regenerates the expected proof and checks it
again. Rehashed metadata cannot promote the certificate into evidence about
observed p-values, power, or an unproved stronger bound.

Single-design and observed-result commands remain available. Old declarations
without `[analysis]` keep alpha `1/20`. A certificate from an older source snapshot
must be reissued after this upgrade because replay requires matching sources.

The [standalone file-language prototype](stat-language.md) now expresses the same
composition in `examples/two_outcomes.stat`, in parallel with Lean. The LSP
provides completion, diagnostics and claim inspection; a REPL remains future work.

## Families with cited tests

`bonferroni` also takes [cited tests](cited-methods.md), one-sided Fisher
analyses, the exact test with a margin and randomisation tests, alone or mixed. `joint_law` is optional and is left out here:

```stat
let endpoints = bonferroni(analyses=[response, symptoms], alpha=1/20)
let family = verify(familywise(endpoints))
```

The result has status `conditional`. Lean checks that the levels sum to at most
the family level and applies `StatClaim.Modules.Composition.familywise_le_of_levels`,
a union bound whose hypothesis is each member's own error bound. Those bounds
are listed as assumptions, each marked as cited or as provable in Lean.

The theorem allows each member's bound a slack, and the family bound then holds
up to the sum of the slacks. So a family with a large-sample member has a
large-sample guarantee: a family is only as exact as its least exact member.

The certificate kind is `statclaim_composition_certificate`, with status
`combination_verified_members_assumed`. See `examples/mixed_endpoints.stat`.

## Interim looks

`alpha_spending` in `designs.group_sequential` applies the same theorem to one
question asked at several looks:

```stat
let trial = alpha_spending(looks=[interim, final], alpha=1/20)
let overall = verify(typeI(trial))
```

Each look is an analysis whose model has the cumulative arm sizes at that look,
with the level spent there. Every look must use the same test and null, and the
looks must be in order. The result is `conditional`, and the claim is `typeI`
because rejecting at any look is one kind of error.

The member assumptions "sizes are fixed" and "the test is run once" are replaced
by one: the looks happen at the declared sizes and the study stops at the first
rejection. The split is conservative: it ignores the correlation between looks.
See `examples/interim_look.stat`.

### Spending boundaries

`group_sequential` uses the correlation between looks:

```stat
let trial = group_sequential(looks=[interim, final], alpha=1/20, spending="obrien_fleming")
let overall = verify(typeI(trial))
```

`spending` is `"obrien_fleming"` or `"pocock"`, the error-spending functions of Lan
and DeMets (1983). The statistics at the looks are taken to have the canonical joint
distribution (Jennison and Turnbull, 2000): the information at a look is
proportional to `n_control n_treatment / (n_control + n_treatment)`, and a two-sided
design spends half the level on each side, as gsDesign and rpact do. StatClaim
computes each look's boundary numerically and refuses a look whose level is above its
boundary's nominal level; the message lists the levels to use. They may add up to
more than `alpha`.

The rule is cited, not proved, and its guarantee is large-sample. Lean checks that
the looks ask one question at growing sizes and that each level is within the
design's level; the boundaries are StatClaim's calculation. The looks must be
Fisher's test or a t-test. The boundaries agree with rpact and gsDesign to six
decimals (`replication/comparison/spending_boundaries_r.R`). See
`examples/group_sequential.stat` and lesson 46.

## Fixed sequences

`fixed_sequence` in `multiplicity.fixed_sequence` is hierarchical testing:

```stat
let hierarchy = fixed_sequence(analyses=[survival, symptoms, response], alpha=1/20)
let overall = verify(familywise(hierarchy))
```

The endpoints are tested in the listed order, each at the full level, and one
is tested only if every earlier one was rejected. Every entry must have the
sequence's `alpha`. Lean applies
`StatClaim.Modules.Composition.fixed_sequence_le_of_levels`: a false rejection
needs the first true null's own test to reject, so the error is at most the
level. The result is `conditional`.

An entry of a family or a sequence may be a whole design with interim looks.
It counts as one test of its null at its overall level, and its own split is
checked as part of the larger plan. See `examples/confirmatory_trial.stat`.

A secondary endpoint is declared as one test at its stated sample size. If a
trial stops at an interim look and analyses it on the interim data, that is
not the declared test.

## Graphical procedures

`graphical` in `multiplicity.graphical` states a procedure with recycling:

```stat
let primary = graphical(
    analyses=[trough_not_worse, peak_not_worse, peak_better],
    weights=[1/2, 1/2, 0],
    transitions=[[0, 1, 0], [0, 0, 1], [1, 0, 0]],
    alpha=1/40,
)
```

`weights` gives each test's starting share of the level. Row i of `transitions`
says how test i's level is shared among the others when it is rejected. The
contract checks that there is one weight per test, that the weights sum to at
most 1, that no test passes level to itself and that no row passes on more than
the whole. Every test is declared at the overall `alpha`.

The result is `cited`: the procedure's guarantee is taken from Bretz et al.
(2009) and Burman et al. (2009), not proved in Lean. It also assumes each test
controls its error at every level up to `alpha`.

## Nesting

An entry of a family or a fixed sequence may itself be a family, a sequence, a
graph or a design with looks. It counts as one member whose own bound is
assumed, with the grade of its own rule. In a fixed sequence, an entry that
holds several nulls must have all of them rejected before the next entry is
tested. See `examples/recycling.stat`.
