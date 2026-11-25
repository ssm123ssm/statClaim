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
| Cluster means or proportions | the same points with `icc=...` | Noncentral t on cluster summaries with the design effect |
| Yes-or-no (logistic regression) | `binomial_rates(p_control=..., p_treatment=...)` | Exact: the Wald test of the log odds ratio, summed over both arms' binomial counts |
| Survival | `hazard_ratio(value=..., events=...)` | Schoenfeld's formula in the number of events |
| Survival, from times | `exponential_survival(hazard_ratio=..., control_median=..., accrual=..., follow_up=...)` | Schoenfeld's formula at the events the arm sizes expect |

- `sd` is the standard deviation of one participant's outcome on the analysed
  scale. For a mixed model, give the effective SD of the contrast.
- A logistic regression's power is exact for its Wald test: every pair of counts is
  weighed by its binomial probability. A table with an empty cell has no finite
  estimate and, as with `glm`, does not reject. The report adds the test's exact
  Type I when both arms have the control rate; the level itself stays cited. `glm`
  fitted to every table in R agrees to 1e-12
  (`replication/comparison/logistic_wald_r.R`). See lesson 44.
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
range that reaches the target. It is not offered for `hazard_ratio`, whose power
does not depend on the arm sizes; plan at `exponential_survival` instead.

### Survival times

`exponential_survival` plans the log-rank test from times: the hazard ratio, the
control median, a steady accrual period, the follow-up after it and, if you like,
`dropout` by `dropout_time`. Each arm's chance of an event by the analysis, times
its size, gives the expected events, and power is Schoenfeld's formula there.

```stat
let expected = exponential_survival(hazard_ratio=7/10, control_median=12, accrual=24,
    follow_up=12, dropout=1/10, dropout_time=12)
let target = power_target(at=expected, minimum=4/5, maximum_typeI=1/20)
let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=50, max_per_arm=1000)
let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))
```

The result gives `expected_events` and each arm's probability of an event. It
assumes exponential times, steady entry and dropout unrelated to the event. The
expected events equal gsDesign's `eEvents` to ten decimals, and the search agrees
with rpact's `getSampleSizeSurvival` and gsDesign's `nSurv`. See
`examples/log_rank.stat` and lesson 32 of the tutorial.

A test without a formula, such as a declared test, gets `no_power_formula`. See
`examples/cited_power.stat`.

### Cluster-randomised trials

The t-test on cluster summaries is sized in clusters. Give the intracluster
correlation on the point: `mean_difference(value=5, sd=10, icc=1/20)` for
`cluster_t_test`, or `binomial_rates(..., icc=...)` for `cluster_proportion_t_test`.
A cluster of m participants then has a summary with variance (1 + (m - 1) icc) / m
times that of one participant. The declared assignment gives the clusters per arm
and their mean size.

```stat
let target = power_target(at=mean_difference(value=5, sd=10, icc=1/20), minimum=4/5,
    maximum_typeI=1/20)
let power = calculate(meets(analysis=summaries, target=target))
let clinics = cluster_counts(analysis=summaries, cluster_size=20, min_per_arm=4,
    max_per_arm=40)
let needed = calculate(smallest_sample_size(candidates=clinics, target=target))
```

- Power uses the noncentral t with `k_control + k_treatment - 2` degrees of
  freedom, since clusters are few. With equal arms and cluster sizes it equals R's
  `power.t.test` with n clusters per arm, to twelve decimals.
- `cluster_counts` searches clusters per arm of a fixed size, from at least four.
  `cluster_sizes(analysis=..., min_size=..., max_size=...)` keeps the declared
  clusters and searches participants per cluster.
- With few clusters, more participants may never be enough: a cluster mean's
  variance falls only to sd² × icc. The search then reports `power_ceiling`.
- Clusters of unequal sizes give less power than the formula; the result lists
  this as an assumption.

See `examples/cluster_trial.stat` and lesson 31 of the tutorial.

## Precision targets

A study can be sized for precision: an interval narrow enough, not a test powerful
enough. Name the interval you will report, then the margin of error you want.

```stat
let estimate = planned_interval(model=survey, measure="prevalence")
let target = precision_target(at=proportion(value=1/10), level=19/20, margin_of_error=3/100)
let sizes = interval_sizes(interval=estimate, min_size=10, max_size=5000)
let smallest = calculate(smallest_sample_size(candidates=sizes, target=target))
```

| Measure | Design | Planning point |
| --- | --- | --- |
| `response_rate` | one arm | `response_rate(value=)` or `proportion(value=)` |
| `prevalence`, `cumulative_incidence` | cross-sectional, cohort | `proportion(value=)` |
| `difference` | two-arm binomial trial | `binomial_rates(p_control=, p_treatment=)` |
| risk or prevalence `_ratio` and `_difference`, `odds_ratio` | cohort, cross-sectional, case-control | the design's point, as for power |
| `conditional_odds_ratio` | matched pairs | `discordant_pairs(share=, odds_ratio=)` |
| `rate_ratio` | person-time cohort | `incidence_rates(..., events=)` |

- **Margin of error** is half the interval's width. `relative_margin_of_error=r` is a
  fraction of the planning value; for a ratio it asks that the lower limit be at least
  (1 - r) times the estimate, half the width on the log scale.
- Without `assurance`, the interval is taken at the counts the planning point expects.
  With `assurance=a`, the chance that the interval turns out narrow enough must be at
  least `a`; it is summed exactly over the possible counts. When a design fixes only its
  total, the assurance is taken at the expected numbers exposed.
- `method="exact"`, the default, is StatClaim's own interval: Clopper-Pearson, rounded
  outward to 1/10,000, and for two groups two exact intervals combined. It is valid for
  every true value, and wide for two groups. StatClaim computes it for results of up to
  1,000 per group; a plan beyond that says so.
- `method="normal"` is the usual large-sample interval: Wald for a proportion or a
  difference, Katz for a ratio, Woolf for an odds ratio. It takes a survey's
  `design_effect` and, for one proportion, `population_size` for a finite population
  correction (Cochran). A complex sample needs it.
- `interval_sizes` searches participants, or for two fixed groups the first (exposed,
  cases, or a trial's control arm) with `ratio` of the other for each, or pairs, or
  events. Without an assurance the margin falls steadily with the size and the search
  finds the smallest size; with one, only `sample_size`, a sufficient size, is offered.

Precision is a calculation: `verify` is refused. It agrees with R's `binom.test`
enumerated over every count to about 1e-13, with `presize` for the normal intervals,
and with Cochran's size for a survey (`replication/comparison/precision_r.R`). See
`examples/precision.stat` and lesson 36.

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
planning SD in both arms or in the scenarios below, the t-tests on cluster summaries,
the log-rank test from survival times, the tests of a correlation or a slope with
skewed data, t-tests repeated at interim looks, Student's t-test with its sample size
re-estimated at an interim look, and families of Fisher tests and t-tests. Other tests get
`no_simulation_model`; exact tests are refused, since `calculate` gives their exact
power. See lesson 28 of the tutorial.

### Clusters of unequal sizes

The noncentral t of a cluster test assumes every cluster has the arm's mean size.
`simulate` drops that: give `cluster_size_cv`, the coefficient of variation of
cluster sizes, on the planning point.

```stat
let uneven = power_target(at=mean_difference(value=5, sd=10, icc=1/20, cluster_size_cv=3/5),
    minimum=4/5, maximum_typeI=1/20)
let varied = simulate(meets(analysis=summaries, target=uneven), seed=2026)
```

Each simulated cluster gets a size from a gamma distribution with that mean and
coefficient of variation (rounded, at least 1), a normal cluster effect with variance
icc × sd², and its participants' mean about it; for proportions, a beta cluster rate
and binomial responses. The test is the unweighted t-test of the cluster summaries.
`calculate` refuses `cluster_size_cv`. `cluster_counts` and `cluster_sizes` searches
can be simulated too. A raw-data simulation in R agrees within its Monte Carlo error
(`replication/comparison/cluster_simulation_r.R`). See lesson 37.

### When the t-test's assumptions fail

Two inputs on `mean_difference` describe another scenario for simulating a
two-sample t-test:

- `sd_treatment`: the treatment arm's SD; `sd` is then the control arm's.
- `skewness`: a skewed outcome, from -4 to 4. Each arm is a gamma distribution
  shifted and scaled to the arm's mean and SD, mirrored when the skewness is negative.

```stat
let spread = power_target(at=mean_difference(value=8, sd=20, sd_treatment=10),
    minimum=4/5, maximum_typeI=3/40)
let pooled = simulate(meets(analysis=student, target=spread), seed=2026)
```

The test's level holds by theory only for normal outcomes with a common SD (Welch's,
approximately, for unequal SDs too). In these scenarios that theory no longer applies,
so simulated Type I is judged like power: met when its whole 95% interval is at or
below `maximum_typeI`, not met when the whole interval is above it, and otherwise
undecided. A search passes over sizes where Type I is not met. A target of exactly
alpha is rarely met this way. Bradley's liberal criterion, 1.5 × alpha, is a common
tolerance (Bradley, 1978, *Br J Math Stat Psychol* 31, 144-152).

`calculate` refuses these inputs. Normal outcomes are drawn as summaries, so their
cost does not grow with the size; skewed outcomes are drawn one participant at a time,
up to 120 million in a run. A raw-data simulation in R agrees within its Monte Carlo
error (`replication/comparison/t_scenarios_r.R`). See lesson 38.

### Survival trials

`log_rank` is simulated from `exponential_survival`, not from a number of events.
Each participant enters uniformly over the accrual period and is followed to its end
plus the follow-up, with exponential event times and exponential dropout. The test is
the log-rank score test with its normal approximation. Without a delay it checks
Schoenfeld's formula.

`effect_delay` on `exponential_survival` is for `simulate` only: the hazard ratio
applies from that time after entry, and before it both arms share the control hazard.
Schoenfeld's formula assumes proportional hazards, so `calculate` refuses it.

```stat
let late = exponential_survival(hazard_ratio=7/10, control_median=12, accrual=12,
    follow_up=12, effect_delay=3)
let too_small = simulate(meets(analysis=analysis, target=power_target(at=late,
    minimum=4/5, maximum_typeI=1/20)), seed=2026)
```

Every participant is drawn, so the same budget applies as for skewed outcomes. A
search over hundreds of sizes may need fewer runs or a narrower range; bracket it
with the formula. A simulation in R with `survival::survdiff` agrees within its
Monte Carlo error (`replication/comparison/survival_simulation_r.R`). See lesson 39.

### Skewed data for a correlation or a slope

Under normality the power of `pearson_correlation`, and of `linear_association` with a
measured exposure, is exact, so `simulate` refuses them there. With skewed data it
runs them: give `skewness` (of the outcome's error) or `exposure_skewness`, from -4 to
4, on `correlation` or `slope`.

```stat
let skewed = power_target(at=correlation(value=1/2, skewness=3, exposure_skewness=3),
    minimum=4/5, maximum_typeI=3/40)
let simulated = simulate(meets(analysis=pearson, target=skewed), seed=2026)
```

Each variable is a gamma distribution shifted and scaled to mean 0 and the planning SD.
As for the t-tests, Type I is judged on the simulation. Searches take `total_sizes`.
Covariates are not simulated yet, and Spearman's exact permutation test is not
simulated. A raw-data simulation in R with `cor.test` and `lm` agrees within its Monte
Carlo error (`replication/comparison/correlation_simulation_r.R`). See lesson 40.

### Interim looks

A design with looks, `alpha_spending(looks=[...], alpha=...)` or
`group_sequential(looks=[...], alpha=..., spending=...)`, has no power formula.
`simulate(meets(analysis=trial, target=...))` runs it look by look: each simulated
trial enrols up to each look's cumulative arm sizes, tests with that look's level,
and stops at the first rejection.

```stat
let trial = alpha_spending(looks=[interim, final], alpha=1/20)
let looked = simulate(meets(analysis=trial, target=target), seed=2026)
```

```text
  looks: (50, 50) at 1/200, (100, 100) at 9/200; stopping ~ 0.3619, 0.5708 (under the null 0.0051, 0.0426)
  expected total ~ 163.8 (under the null ~ 199.5)
  power ~ 0.9327 (95% interval 0.9276 to 0.9375); power target met = true
```

- `power` is the chance of rejecting at any look. `looks` gives how often each look
  stopped the trial, at the planning point and under the null.
- `expected_sample_size` is the mean total at which trials stopped;
  `expected_sample_size_null` is the same under the null.
- Lean proves the Type I bound of `alpha_spending` (lesson 14), and the bound of
  `group_sequential` is cited, so the simulated Type I is reported, not judged. It shows
  how conservative a split is, and how much of the level the boundaries use.
- The looks may be Student's or Welch's t-tests, at normal outcomes or the scenarios
  above. The looks are simulated as declared, not searched.
- When the looks are Fisher's test, nothing is simulated: `calculate(meets(...))` sums
  the power exactly over every path of counts through the looks, each look with the
  exact rejection region of its own level, up to 500 per arm at the last look. It
  reports the same stopping rates and expected sizes, and the exact Type I with both
  arms at the control rate. A brute-force enumeration in R with `fisher.test` agrees to
  1e-12 (`replication/comparison/fisher_looks_r.R`). See lesson 45.
- `verify` refuses the claim either way.

A raw-data simulation in R that applies `t.test` at each look agrees within its Monte
Carlo error (`replication/comparison/group_sequential_r.R`). See lesson 41.

### Re-estimating the sample size

`blinded_reestimation` (in `designs.adaptive`) wraps Student's t-test. After
`interim_per_arm` per arm it estimates the variance from everyone with the arms pooled,
so no one sees the groups (Kieser and Friede, 2003). It recomputes the size per arm for
the planned `difference` and `power`, never below the analysis's size per arm nor above
`max_per_arm`, and runs the t-test on everyone.

```stat
let trial = blinded_reestimation(analysis=final, interim_per_arm=30, difference=5,
    power=4/5, max_per_arm=200)
let nulls = null_scenarios(at=[mean_difference(value=0, sd=6),
    mean_difference(value=0, sd=10), mean_difference(value=0, sd=14)])
let target = power_target(at=mean_difference(value=5, sd=14), minimum=3/4,
    maximum_typeI=3/40, nulls=nulls)
let adapted = simulate(meets(analysis=trial, target=target), seed=2026)
```

Its Type I error is not proved, so the target must list null scenarios: points on the
null, here different SDs. `simulate` estimates Type I at each one and judges each like
power; the target is met only when every scenario's whole 95% interval is at or below
`maximum_typeI`. Nothing is claimed at SDs not listed. The derivation records the rule
and the scenarios, and the checker verifies that each lies on the null. The report gives
power, each scenario's Type I and expected size, and the expected size at the planning
point. `calculate` and `verify` refuse the claim, and `nulls` is refused for analyses
whose level is proved or cited. A raw-data simulation in R agrees within its Monte Carlo
error (`replication/comparison/reestimation_r.R`). See lesson 42.

### The power of a family

A family's power depends on how its endpoints move together, so it is planned at one
point per member and a correlation, and `power_target` says what power means:
`rejecting="any"` (at least one endpoint) or `rejecting="all"` (every endpoint).

```stat
let expected = endpoint_points(at=[binomial_rates(p_control=3/10, p_treatment=1/2),
    mean_difference(value=4, sd=10)], correlation=1/2)
let either = simulate(meets(analysis=endpoints, target=power_target(at=expected,
    minimum=4/5, maximum_typeI=1/20, rejecting="any")), seed=2026)
```

```text
  endpoints: response ~ 0.7962, symptoms ~ 0.8017; any ~ 0.9239, all ~ 0.6740 (bonferroni, correlation 1/2; power means any)
  familywise error under the global null ~ 0.0379 (95% interval 0.0342 to 0.0418); ...
```

- The family may be `bonferroni`, `fixed_sequence` or `graphical`, of Fisher's tests and
  t-tests. Each endpoint is tested by its own test, and the family's procedure decides;
  a graph passes level along its edges (Bretz et al., 2009).
- Endpoints with a correlation above 0 are measured on the same participants: each has a
  latent normal with that exchangeable correlation, and a yes-or-no outcome is a success
  when its latent is high. They must share their arm sizes. With 0 they are independent.
- The familywise bound is proved or cited for any dependence, so the simulated error
  under the global null is reported, not judged.
- Families are simulated as declared, not searched. `calculate` and `verify` refuse the
  claim.

A raw-data simulation in R with `fisher.test` and `t.test`, and the graphical algorithm
written independently, agrees within its Monte Carlo error
(`replication/comparison/family_power_r.R`). See lesson 43.

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
