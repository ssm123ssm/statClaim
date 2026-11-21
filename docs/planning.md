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

## Plan an observational study

Fisher's test of association in a cohort or case-control study has exact power too.
A cohort is planned at `risks(...)`, a case-control study at `exposure_prevalence(...)`
and a cross-sectional study at `outcome_prevalence(...)`; `cohort_sizes`,
`case_control_sizes` and `total_sizes` search their sizes. McNemar's test is
planned at `discordant_pairs(...)` and the rate test at `incidence_rates(...)`. See
[observational studies](observational.md#power-and-sample-size) and
`examples/observational_power.stat`.

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

## A one-sided two-arm test

To ask whether the treatment is better than the control, use the one-sided
Fisher test. Its null is that the treatment's success rate is at most the
control's:

```stat
let null = proportion_difference_at_most(model=study, value=0)
let analysis = fisher_one_sided(design=design, null=null, alpha=1/40)
```

`typeI`, `observe`/`result`, `meets` and the sample-size claims work as for the
two-sided test. The error bound holds for every pair of rates with the
treatment no better than the control, not only for equal rates. The planning
point must have the larger treatment rate. To test the other direction, swap
which arm you call the treatment. See `examples/one_sided.stat`.

## A non-inferiority test

To show a new treatment is not worse than the control by more than a margin,
use the exact difference test. Its null is that the treatment's success rate
falls short by more than the margin:

```stat
use tests.difference

let null = proportion_difference_at_most(model=study, value=-1/10)
let analysis = difference_test(design=design, null=null, alpha=1/40)
let guarantee = verify(typeI(analysis))
```

A margin of zero gives a superiority test; a positive margin asks for more
than superiority. `typeI`, `observe`/`result`, `meets` and `sample_size` are
available. See `examples/non_inferiority.stat`.

The test is a list of thresholds: with a given number of control successes,
it rejects at a stated number of treatment successes or more. The list is
chosen from the usual score statistic and is part of the certificate. Lean
checks that the error is at most alpha for every pair of rates in the null. It
does this by cutting the range of control rates into intervals and bounding the
error on each one.

Limits: up to 120 participants per arm, where verification takes about 80
seconds. `smallest_sample_size` is not offered, because each sample size has
its own threshold list. Results are a decision, without a p-value.

## Estimate a difference between two arms

```stat
use models.two_arm_binomial
use estimation

let study = two_arm_binomial(n_control=50, n_treatment=50)
let interval = difference_interval(model=study, control_successes=12,
    treatment_successes=24, level=19/20)
let verification = verify(interval)
```

This gives -0.0825 to 0.5254 for the difference in success rates. The interval
combines an exact interval for each arm, so it is valid for every pair of true
rates. It is wider than intervals designed for the difference, and it can
include zero when a test rejects. See `examples/difference_interval.stat`.

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

To find a design instead of proposing one, search:

```stat
let candidates = two_stage_designs(null_rate=1/5, max_total=45, criterion="optimal")
let verification = verify(sample_size(candidates=candidates, target=target))
```

`"optimal"` minimises the expected sample size at the null rate; `"minimax"`
minimises the maximum sample size. Here the result is Simon's design: stop
after 13 participants with 3 or fewer responses, otherwise continue to 43 and
reject with more than 12. Lean certifies the selected design's error and
power. The ranking among designs is a calculation and is not certified.
See `examples/two_stage_search.stat`.

After the study, enter the counts. Use `completed_stages` if the study continued
and `stopped_at_interim` if it stopped:

```stat
let data = completed_stages(analysis=analysis, stage1_responses=5, stage2_responses=9)
let verification = verify(two_stage_result(data))
```

Lean confirms the decision the declared rule reaches and the design's error
bound. Counts that contradict the rule, such as stage-two data when the rule
would have stopped, are rejected. See `examples/two_stage_result.stat`.

`calculate` also reports expected sample size and the early-stopping
probability. `posterior_rule` replaces count thresholds with posterior
probabilities under a `beta_prior`; see `examples/two_stage_posterior.stat`.
A posterior threshold is a decision rule. Its Type I error and power are
separate claims about the whole policy, and are checked the same way.
See [policies](policies.md) for the model and its limits.

## Power for cited tests

A [cited test](cited-methods.md) has no exact power, but most have an approximate
one from a published formula. `calculate` gives it; `verify` is refused, since no
proof or cited theorem covers an approximate power.

```stat
use models.two_arm_continuous
use sampling
use tests.mixed_model
use planning

let study = two_arm_continuous(n_control=440, n_treatment=440)
let analysis = mmrm_test_one_sided(
    design=fixed(model=study),
    null=mean_difference_at_most(model=study, value=-50),
    alpha=1/40,
)
let target = power_target(at=mean_difference(value=-10, sd=167), minimum=9/10,
    maximum_typeI=1/40)
let power = calculate(meets(analysis=analysis, target=target))
```

```text
calculated [power]: meets(analysis)
  arm sizes = (440, 440); total = 880
  power ~ 0.9444 (normal approximation, not a bound); power target met = true
  rejects when the estimate is above -27.93; standard error ~ 11.26
```

The status is always `calculated`. The report also lists the test's assumptions,
the formula's own and the formula's references.

Planning points:

| Outcome | Point | Formula |
| --- | --- | --- |
| Continuous | `mean_difference(value=..., sd=...)` | Difference of two means with a known SD |
| Yes-or-no | `binomial_rates(p_control=..., p_treatment=...)` | Two proportions: pooled variance under the null, unpooled at the point |
| Survival | `hazard_ratio(value=..., events=...)` | Schoenfeld's formula in the number of events |

- `sd` is the standard deviation of one participant's outcome on the analysed
  scale. For a mixed model, give the effective SD of the contrast.
- The margin comes from the declared null. The point must lie outside it.
- `hazard_ratio` is treatment over control. Power depends on the events, not on
  the arm sizes, and it assumes proportional hazards. The log-rank test's error
  rate does not.
- For an outcome where lower is better, with `mean_difference_at_least`, the
  test rejects when the estimate is below the margin minus z × SE.

What is calculated:

- Power uses the normal approximation throughout, with no noncentral t. With 400
  per arm it is at most 0.001 above R's `power.t.test`. For two proportions it
  equals R's `power.prop.test`.
- A one-sided test is at `alpha`. A two-sided test is at `alpha/2` and ignores
  rejections in the direction away from the point, as R does by default.
- `calculation.critical_estimate` is the value the estimate must pass to reject:
  the margin plus z × SE. `calculation.reject_when` says above or below. Plans
  often state this value, so it checks their arithmetic too.
- `maximum_typeI` is compared with the test's `alpha`. The test's guarantee is
  cited, not proved.

`equal_arm_sizes` and `allocated_arm_sizes` accept a cited test, up to 100,000
per arm. `calculate(smallest_sample_size(...))` returns the first size in the
range that reaches the target. It is not offered for `hazard_ratio`.

A test without a formula, such as a declared test, gets `no_power_formula`. See
`examples/cited_power.stat`.

## Power by simulation

`simulate` runs the test itself on simulated studies and counts how often it
rejects. It takes the same planning claims as `calculate`, a seed and, if you
like, the number of runs (10,000 by default, from 1,000 to 200,000).

```stat
let estimate = simulate(meets(analysis=analysis, target=target), seed=2026)
let sizing = simulate(smallest_sample_size(candidates=sizes, target=target), seed=2026)
```

```text
simulated [estimate]: meets(analysis)
  power ~ 0.6025 (95% interval 0.5928 to 0.6121); power target met = false
  Type I at the null ~ 0.0509 (95% interval 0.0467 to 0.0554); ...
```

- The status is `simulated`: an estimate, never evidence. A file of calculations
  and simulations reports `simulated`; simulations do not weaken a proof.
- Power is the share of studies that rejected at the planning point, with a 95%
  Clopper-Pearson interval. Type I error is simulated at the null's boundary and
  reported; the Type I target is judged on the test's `alpha`.
- `power_target_met` needs the whole interval at or above the minimum. When the
  interval contains it, the decision is `undecided`; more runs may settle it.
- A search goes up the range and simulates every size, so it never assumes power
  rises with n. The first size that passes is simulated again from an independent
  stream; its reported power comes from that run. `curve` lists every size tried.
- The same seed gives the same numbers. The engine uses only Python's
  `random.Random(...).random()`, seeded from SHA-256 of the seed and a label, and
  records its version.
- Each study draws its summary statistics directly, so a run costs the same at
  any size: a search of 100 sizes with 10,000 runs takes about a second. A search
  may simulate at most 20 million studies.

Simulation covers the t-tests, Student's and Welch's, on normal outcomes with the
planning SD in both arms. Other tests get `no_simulation_model`; exact tests are
refused, since `calculate` gives their exact power. See lesson 28 of the tutorial.

## What is checked

| Result | Meaning |
| --- | --- |
| `calculate(...)` | Exact fractions computed in Python, or for a cited test an approximate power. Not proof evidence. |
| `simulate(...)` | Power and Type I error estimated from simulated studies, with 95% intervals. Not proof evidence. |
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
