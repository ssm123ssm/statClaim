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

## What is refused

Tests and nulls of randomised arms (`fisher`, `t_test`, `randomisation_test`,
`no_effect` and the rest) refuse an observational study with
`observational_design` or a type error that names `fisher_exact`. Exposure was
not assigned, so their premises do not hold.

## What a claim does not say

A bound concerns association in the population sampled. It is never a claim
about an effect of the exposure: confounding is not excluded. Each report says
so under the claim.

Not yet supported: intervals for odds, risk and prevalence ratios, observed
tables, matched designs, prevalence and incidence estimates, regression with
covariates and complex samples.
