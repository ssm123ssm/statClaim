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

## What is refused

Tests and nulls of randomised arms (`fisher`, `t_test`, `randomisation_test`,
`no_effect` and the rest) refuse an observational study with
`observational_design` or a type error that names `fisher_exact`. Exposure was
not assigned, so their premises do not hold.

## What a claim does not say

A bound concerns association in the population sampled. It is never a claim
about an effect of the exposure: confounding is not excluded. Each report says
so under the claim.

Not yet supported: matching with several controls per case, prevalence and
incidence estimates, regression with covariates and complex samples.
