# Configurable Fisher levels and Bonferroni composition

This milestone adds a reusable composition proof and a two-outcome Fisher adapter.
It needs no observed counts. The generic Lean Bonferroni module accepts any finite
number of tests on a common sampling law; the first TOML/CLI adapter supports
exactly two Fisher analyses.

## Declare the family

```toml
[family]
module = "bonferroni"
alpha = "1/20"
joint_law = "binomial_marginals"

[[analyses]]
name = "primary_outcome"
n_control = 200
n_treatment = 100
stopping = "fixed"
alpha = "1/40"

[[analyses]]
name = "secondary_outcome"
n_control = 200
n_treatment = 100
stopping = "fixed"
alpha = "1/40"
```

Names must be distinct. Arm sizes may differ between analyses. Levels are exact
strings in `[0,1]`; `"0.025"` and `"1/40"` normalize to the same rational value.
Unequal allocations are supported provided their sum does not exceed family alpha.
Both analyses and the allocation must be specified before observing results.

```sh
uv run --locked statproof inspect-family examples/two_outcomes.toml
uv run --locked statproof verify-family examples/two_outcomes.toml \
  --output .statproof/two-outcomes
uv run --locked statproof check-certificate .statproof/two-outcomes
```

Inspection exits with code 1 because it has not checked the proof. Successful
verification and replay exit with code 0. Malformed declarations exit with code 2.
The output directory must be new.

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
- `FisherFamily.module` combines those pieces for two outcomes.

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

The next interface experiment remains the small standalone statistical language
in parallel with Lean. This milestone adds no new language, REPL, or LSP.
