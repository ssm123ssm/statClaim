# Observational studies

In an observational study nobody assigned the exposure. `models.observational`
declares which design was run, because the design decides what the sampling
fixed, what the study can estimate and how a test is justified.

| Design | Constructor | Fixed by sampling | Can estimate |
|---|---|---|---|
| Cross-sectional | `cross_sectional(n)` | the total | prevalence, prevalence ratio and difference, odds ratio |
| Cohort, groups sampled | `cohort(exposed, unexposed)` | the exposed and unexposed groups | risk, risk ratio and difference, odds ratio |
| Cohort, one population | `cohort(n)` | the total | as above |
| Case-control | `case_control(cases, controls)` | the cases and controls | odds ratio only |
| Matched case-control | `matched_case_control(pairs)` | the pairs of one case and one control | conditional odds ratio |
| Person-time cohort | `person_time_cohort()` | nothing; it counts events over person-time | incidence rate ratio |

Each constructor takes `exposure` and `outcome` names, which the claims use.
`no_association(model=...)` is the null: an odds ratio of 1, stated in the
design's terms.

```text
use models.observational
use sampling
use tests.association

let study = case_control(cases=150, controls=300, exposure="smoking", outcome="lung cancer")
let analysis = fisher_exact(design=fixed(model=study), null=no_association(model=study), alpha=1/20)
let checked = verify(typeI(analysis))
```

## What is proved

`fisher_exact` is Fisher's exact test of no association. Lean proves its Type I
bound in `StatClaim.Modules.Association`:

- **Two group sizes fixed** (a cohort with `exposed` and `unexposed`, or a
  case-control study). The table holds two independent binomial counts, so
  Fisher's theorem applies with the groups in place of arms:
  `groups_typeI_le_alpha`.
- **Only the total fixed** (a cross-sectional study or `cohort(n)`). The number
  exposed is binomial. Given it, the test rejects with probability at most
  alpha, so the average over it is at most alpha too: `mixture_typeI_le_alpha`.

Both hold for every probability under the null. The assumptions list how the
study sampled, independence between participants and, for a case-control study,
that the controls come from the population that gave rise to the cases.

## Observed tables and effect measures

`observed_table(model=..., exposed_cases=, exposed_noncases=, unexposed_cases=,
unexposed_noncases=)` records the data. Cases have the outcome. The table must fit
what the design fixed, or it is refused.

- `association_result(analysis=..., table=...)` gives the exact p-value and
  decision of Fisher's test. `verify` checks both in Lean, with the test's bound.
  For a design that fixed only the total, the p-value is given the number exposed.
- `estimation.observational` gives intervals at a declared level:

| Measure | Designs |
|---|---|
| `odds_ratio` | any; for a case-control study, the odds ratio of exposure |
| `risk_ratio`, `risk_difference` | cohort |
| `prevalence_ratio`, `prevalence_difference` | cross-sectional |

Any other pairing is refused with `not_estimable`, which says what the design can
estimate instead. Each interval comes from exact intervals for the two groups'
probabilities, built at a level whose square is at least the requested one, so
both hold together. The measure then lies between its values at the ends:
`ratio_contains` and `odds_ratio_contains` in Lean, and
`BinomialInterval.difference_contains` for differences. When only the total is
fixed, joint coverage holds given the number exposed and so on average:
`mixture_joint_coverage`. The intervals are valid for every pair of
probabilities and wider than large-sample ones. A ratio has no finite upper
bound when the reference group's lower end is zero.

## Matched pairs

`matched_case_control(pairs)` declares a 1:1 matched study, and
`observed_pairs(model=..., both_exposed=, case_exposed_only=,
control_exposed_only=, neither_exposed=)` records who was exposed in each pair.
Only the discordant pairs, where exactly one was exposed, carry information.

- `mcnemar(design, null, alpha)` is McNemar's exact test: given the discordant
  pairs, a two-sided binomial test at one half. Lean proves its level given their
  number and, since that number is binomial too, on average
  (`StatClaim.Modules.Matched.typeI`). `matched_result` checks the p-value and
  decision for observed pairs.
- `conditional_odds_ratio(pairs, level)` is the odds that the case is the exposed
  one in a discordant pair, from the exact interval for that probability
  (`pairs_coverage`, `odds_contains`).

`fisher_exact` and `observed_table` refuse a matched study with
`matched_design`: an unmatched analysis ignores the matching, and Fisher's
theorem assumes independent groups. The assumptions list one conditional odds
ratio shared by all pairs.

## Prevalence, risk and incidence rates

- `prevalence(model=..., cases=, level=)` for a cross-sectional study and
  `cumulative_incidence(model=..., cases=, level=)` for a cohort give a single
  proportion with its exact interval (`BinomialInterval.coverage`). A cohort that
  sampled its groups separately takes `group="exposed"` or `"unexposed"`.
- `person_time_cohort()` with `observed_events(model=..., exposed_events=,
  exposed_time=, unexposed_events=, unexposed_time=)` records events and
  person-time, which may be fractional.
- `rate_test` is the exact test of equal incidence rates: given the total events,
  a two-sided binomial test at the exposed share of person-time. Lean proves its
  level for every rate and any person-time, given the total and on average over
  any law of it (`StatClaim.Modules.Incidence.typeI`). `rate_result` checks the
  p-value and decision; `rate_ratio` gives the incidence rate ratio, the odds of
  the exposed share times unexposed over exposed person-time.

A single incidence rate has no exact interval yet: its Poisson tails involve
powers of e, which the kernel cannot check exactly. Up to 500 events in a checked
rate result, and up to 1000 participants in a proportion's group.

## Covariates, continuous variables and complex surveys

These methods are cited, not proved. The compiler checks that each fits the
study's design, measurement scales and survey, and the null; the report gives the
cited guarantee, its scope and its assumptions.

- Studies declare `exposure_scale` and `outcome_scale`, `"binary"` unless
  `"continuous"`, and a cross-sectional study declares `survey` (`"simple_random"`,
  `"stratified"`, `"cluster"` with `clusters=`, or `"weighted"`).
- `tests.regression`: `logistic_association` (cross-sectional, cohort,
  case-control), `conditional_logistic` (matched pairs), `poisson_rate_regression`
  (person-time cohorts), `modified_poisson` (risk or prevalence ratio; refused for
  case-control studies) and `linear_association` (continuous outcome). Each takes
  `adjusted_for=[...]`.
- `tests.correlation`: `pearson_correlation` (bivariate normality) and
  `spearman_correlation` (exact permutation), for two continuous variables.
- `tests.survey`: `survey_logistic`, `survey_linear` and `rao_scott_test`,
  design-based, needing at least 20 sampled clusters in a cluster survey.

Proved methods need yes-or-no variables and simple random sampling. They refuse a
continuous variable with a type error and a complex sample with
`complex_sample`, and a refusal names the methods that fit the study.

## Power and sample size

`fisher_exact` has exact power when the design fixes both groups: a cohort declared
with `exposed` and `unexposed`, or a case-control study. Declare the planning point in
the design's terms, then use `meets` and the sample-size claims from `planning`:

| Design | Planning point | Search |
|---|---|---|
| Cohort | `risks(unexposed=, exposed=)` or `risks(unexposed=, risk_ratio=)` | `cohort_sizes(analysis, min_exposed, max_exposed, unexposed_per_exposed)` |
| Case-control | `exposure_prevalence(controls=, cases=)` or `exposure_prevalence(controls=, odds_ratio=)` | `case_control_sizes(analysis, min_cases, max_cases, controls_per_case)` |

```text
let target = power_target(at=exposure_prevalence(controls=1/5, odds_ratio=2),
    minimum=4/5, maximum_typeI=1/20)
let power = calculate(meets(analysis=analysis, target=target))
let sizes = case_control_sizes(analysis=analysis, min_cases=50, max_cases=200, controls_per_case=2)
let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))
```

Power is the exact probability that the test rejects when the two groups' counts are
binomial at the point. `verify` has Lean recompute it from the formal p-value
(`StatClaim.Modules.AssociationPower`), with the test's Type I bound; a smallest-size
claim also proves that each smaller candidate falls short, one theorem each, so it takes
longer. The ratio between the groups is a whole number from 1 to 10, and each group holds
at most 500. Exact power agrees with R: every table through `fisher.test`, and
`exact2x2::power2x2` with `strict = TRUE`
(`replication/comparison/observational_power_r.R`).

`mcnemar` and `rate_test` have exact power too:

| Test | Planning point | Search |
|---|---|---|
| `mcnemar` | `discordant_pairs(share=, odds_ratio=)` | `matched_sizes(analysis, min_pairs, max_pairs)` |
| `rate_test` | `incidence_rates(rate_ratio=, exposed_time=, unexposed_time=, events=)` | `event_counts(analysis, min_events, max_events)` |

- `share` is the probability that a pair is discordant. With probabilities `p10` that only
  the case is exposed and `p01` that only the control is, it is `p10 + p01`, and the
  conditional odds ratio is `p10 / p01`. Power averages over the number of discordant pairs.
- The rate test's power is given the total number of events, as the test itself is; only
  the exposed share of person-time matters. `event_counts` searches the events, so the
  point then leaves `events` out. Averaging over a Poisson total would need powers of e,
  which the kernel cannot check exactly.

Lean checks the bounds of each rejection region against the binomial tails
(`StatClaim.Modules.BinomialPower`). Up to 400 pairs, where `verify` takes about 40 seconds,
and 500 events. Both agree with R to twelve decimals (`binom.test`, `exactci::poisson.exact`
and `exact2x2::powerPaired2x2`).

A design that fixes only the total, a cross-sectional study or `cohort(n)`, has no power
calculation yet: its number exposed is random.

## What is refused

Tests and nulls of randomised arms (`fisher`, `t_test`, `randomisation_test`,
`no_effect` and the rest) refuse an observational study with
`observational_design` or a type error that names `fisher_exact`. Exposure was
not assigned, so their premises do not hold.

## What a claim does not say

A bound concerns association in the population sampled. It is never a claim
about an effect of the exposure: confounding is not excluded. Each report says
so under the claim.

Not yet supported: matching with several controls per case, single incidence
rates, intervals from regression models, power for designs that fix only the total, and proofs
for any cited method.
