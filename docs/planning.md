# Planning a study

Planning asks whether a design meets a target, or searches for one that does.
`examples/planning.stat` and `examples/two_stage.stat` are complete files.
The rates and targets below are illustrative inputs, not defaults.

## Check a proposed study

The researcher expects success rates of 10% and 40%, wants at least 80% power,
and requires a Type I error bound of 5%. First try 20 participants per arm.

```stat
use models.two_arm_binomial
use sampling
use tests.fisher
use planning

let study = two_arm_binomial(n_control=20, n_treatment=20)
let design = fixed(model=study)
let null = equal_proportions(model=study)
let analysis = fisher(design=design, null=null, alpha=1/20)

let alternative = binomial_rates(p_control=1/10, p_treatment=2/5)
let target = power_target(at=alternative, minimum=4/5, maximum_typeI=1/20)
let feasibility = meets(analysis=analysis, target=target)
let calculation = calculate(feasibility)
let verification = verify(feasibility)
```

- `alternative` is a planning point. It does not replace the equality null, and
  it must lie outside it. A difference alone would not specify both rates.
- `minimum` is power at this point, not a guarantee for other alternatives.
- `alpha` defines the rejection rule; `maximum_typeI` is the requested error
  bound. Verification is blocked if alpha exceeds it.

```text
calculated [calculation]: power ~ 0.492; power target met = false
unresolved_obligation [verification]: power_target_not_met
```

`calculate` reports each component. `verify` issues evidence only when every
component is established, so here evidence is absent. Failing a planning claim
says nothing about whether the null is true.

## Find a sufficient sample size

```stat
let candidates = equal_arm_sizes(analysis=analysis, min_per_arm=2, max_per_arm=40)
let sizing = smallest_sample_size(candidates=candidates, target=target)
let recommendation = calculate(sizing)
let sizing_verification = verify(sizing)
let recommended_size = recommendation.calculation.n_control
```

Candidates keep the analysis's sampling, null form, test and alpha, and change
only the arm sizes. The search is ascending with step one and evaluates every
candidate; power is not assumed to increase with sample size.

```text
calculated [recommendation]: arm sizes = (36, 36); power ~ 0.8004
verified [sizing_verification]: No equal-arm size from 2 up to 35 reaches that
  power, so (36, 36) is the smallest sufficient candidate in the range 2 to 40.
```

There are two sizing claims:

- `sample_size` certifies that the selected design meets the target.
- `smallest_sample_size` also certifies that every smaller candidate in the
  range fails. It takes longer, and claims nothing outside the range.

An exhausted search reports `no_feasible_candidate` and claims nothing about
other designs or larger samples.

For unequal allocation, replace `equal_arm_sizes` with `allocated_arm_sizes`.
With `treatment_per_control=2`, each candidate has `n` controls and `2n`
treated participants. See `examples/unequal_allocation.stat`.

## Plan a single-arm study

`tests.binomial` provides the one-sided exact binomial test. Its null is every
response rate at or below `null_rate`.

```stat
use tests.binomial
use planning

let study = one_arm_binomial(n=25)
let analysis = binomial_test(model=study, null_rate=1/5, alpha=1/20)
let target = power_target(at=response_rate(value=2/5), minimum=4/5, maximum_typeI=1/20)
let candidates = sample_sizes(analysis=analysis, min_n=10, max_n=60)
let verification = verify(smallest_sample_size(candidates=candidates, target=target))
```

The result is 35 participants, rejecting at 12 or more responses. The test
rejects at the smallest count whose tail probability at `null_rate` is at most
alpha. See `examples/one_sample.stat`.

Once the data are in, analyse them with the same test:

```stat
let data = responses(analysis=analysis, count=14)
let verification = verify(binomial_result(data))
```

Lean confirms the exact p-value, the critical value and the decision. See
`examples/one_sample_result.stat`.

For an estimate with an exact confidence interval:

```stat
let interval = confidence_interval(model=study, count=14, level=19/20)
let verification = verify(interval)
```

This gives 0.2387 to 0.5789. The interval is the exact (Clopper–Pearson) one
with endpoints rounded outward to four decimals. The certificate states that
the procedure covers the true rate with probability at least the level, for
every true rate. See `examples/confidence_interval.stat`.

## Plan an adaptive design

The same target applies to a complete two-stage policy:

```stat
use designs.two_stage
use planning

let stages = two_stage_binomial(n_stage1=13, n_stage2=30)
let rule = threshold_rule(continue_above=3, reject_above=12)
let analysis = two_stage_test(design=stages, rule=rule, null_rate=1/5)
let target = power_target(at=response_rate(value=2/5), minimum=4/5, maximum_typeI=1/20)
let claim = meets(analysis=analysis, target=target)
let characteristics = calculate(claim)
let verification = verify(claim)
```

`calculate` also reports expected sample size and the early-stopping
probability. `posterior_rule` replaces count thresholds with posterior
probabilities under a `beta_prior`; see `examples/two_stage_posterior.stat`.
A posterior threshold is a decision rule. Its Type I error and power are
separate claims about the whole policy, and are checked the same way.
See [policies](policies.md) for the model and its limits.

## What is checked

| Result | Meaning |
| --- | --- |
| `calculate(...)` | Exact fractions computed in Python. Not proof evidence. |
| `verify(...)` | Lean recomputes the rejection probability from the formal definitions and checks the requested bounds. No calculated value is trusted. |

Published fields include `calculation.power`, `power_target_met`,
`typeI_target_met`, sizes and, for two-stage policies, `typeI` and
`expected_sample_size_null`. Decimals are display only. See the
[catalogue](catalogue.md) for all fields.

Limits: power is at one declared point. Error bounds for single-arm designs hold
for every rate at or below the null rate. Assurance and precision
targets are not yet supported.

Verification time grows with sample size. A Fisher design with 150 per arm
takes about 20 seconds; much larger designs may exceed `--timeout` and remain
unresolved.
