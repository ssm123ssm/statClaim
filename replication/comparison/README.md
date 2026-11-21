# Cross-checks against R packages

These scripts show what established R packages compute for designs StatClaim also
checks. The tools have different aims, so this is a record of what each reports, not
a ranking. The scripts need R and are not part of `make replicate`. Each writes a
pinned output beside it, ending with the R session (without locale or time zone).

Install the packages into any library, then point R at it:

```sh
Rscript -e 'install.packages(c("clinfun", "gsDesign", "graphicalMCP", "DeclareDesign", "jsonlite"), lib = "path/to/library")'
R_LIBS=path/to/library Rscript replication/comparison/simon_clinfun.R
```

Run every script from the repository root. Versions used: R 4.6.1, clinfun 1.1.6,
gsDesign 3.11.0, graphicalMCP 0.3.0, DeclareDesign 2.0.0, exact2x2 1.7.0, epiR 3.0.1, exactci 1.4.5, CRTSize 1.2, rpact 5.0.0, pwr 1.3.0, pwrss 1.3.3, MESS 0.6.0.
gMCP was not used: it needs Java.

| Script | Output | What it compares |
| --- | --- | --- |
| `simon_clinfun.R` | `simon_clinfun.txt` | `clinfun::ph2simon` against StatClaim's re-check of the 102 designs of Simon (1989): the selected designs, the early-stopping probability and the expected sample size |
| `graph_graphicalMCP.R` | `graph_graphicalMCP.txt` | Rejections, adjusted p-values and simulated power for a graph with recycling, and how invalid graphs are refused |
| `group_sequential_gsDesign.R` | `group_sequential_gsDesign.txt` | Boundaries that use the correlation between looks against StatClaim's union-bound split of the level |
| `power_base_r.R` | `power_base_r.txt` | Base R's `power.t.test` and `power.prop.test`; writes `tests/fixtures/power_r.json`, which `replication/power.py` compares with StatClaim |
| `declaredesign_two_arm.R` | `declaredesign_two_arm.txt` | DeclareDesign's simulated diagnosands for a two-arm design |
| `cluster_power_r.R` | `cluster_power_r.txt` | Power of the t-test on cluster means and proportions with the design effect (`power.t.test`, the noncentral t through `pt`, and CRTSize's normal-approximation cluster counts); writes `tests/fixtures/cluster_power_r.json`, which `tests/test_cluster_power.py` compares with StatClaim |
| `survival_power_r.R` | `survival_power_r.txt` | Log-rank power from exponential survival times: expected events (`gsDesign::eEvents` and numerical integration), Schoenfeld's power, and sample sizes from `rpact::getSampleSizeSurvival` and `gsDesign::nSurv`; writes `tests/fixtures/survival_power_r.json`, which `tests/test_survival_power.py` compares with StatClaim |
| `regression_power_r.R` | `regression_power_r.txt` | Power of the t-tests of a correlation and a regression slope with a normal exposure (numerical integration, raw-data simulation, and `pwr.r.test` and `pwr.f2.test` for context); writes `tests/fixtures/regression_power_r.json`, which `tests/test_regression_power.py` compares with StatClaim |
| `logistic_power_r.R` | `logistic_power_r.txt` | Hsieh's formulas for logistic regression and Signorini's for Poisson rates (`pwrss`), Connor's for matched pairs (`MESS::power_mcnemar_test`), and `glm` on simulated studies; writes `tests/fixtures/logistic_power_r.json`, which `tests/test_logistic_power.py` compares with StatClaim |
| `survey_power_r.R` | `survey_power_r.txt` | Survey tests through the design effect: `pwrss`'s Hsieh sizes for a simple random sample, times the design effect, and the Wald test of a slope; writes `tests/fixtures/survey_power_r.json`, which `tests/test_survey_power.py` compares with StatClaim |
| `observational_power_r.R` | `observational_power_r.txt` | Exact power of Fisher's test of association for cohort and case-control studies (every table through `fisher.test`, `exact2x2::power2x2` and epiR's normal formulas), McNemar's test (`binom.test`, `exact2x2::powerPaired2x2`) and the rate test (`exactci::poisson.exact`); writes `tests/fixtures/observational_power_r.json`, which `tests/test_observational_planning.py` compares with StatClaim |

StatClaim's side of the same designs is `graph.stat`, `sequential.stat` and
`two_arm_power.stat`. `statclaim_side.py` runs them, and four invalid variants of the
graph, and writes `statclaim_side.txt`. The two-look design needs the Lean setup.

## Results

- **Simon (1989).** clinfun selects all 102 tabulated designs with a maximum of 120
  participants. Its early-stopping probabilities and expected sizes agree with
  StatClaim's exact values in every case. Both differ from four printed
  early-stopping probabilities in Simon's tables (see `../simon_results.md`).
- **Graphs.** graphicalMCP tests a graph against p-values: it gives rejections,
  adjusted p-values and power by simulation. StatClaim checks the declared graph
  before any data exist and cites the procedure's familywise bound. Both refuse a row
  of transitions that sums to more than 1, weights that sum to more than 1 and a test
  that passes its level to itself. StatClaim also refuses a test declared at less
  than the overall level.
- **Group-sequential.** StatClaim's split is a union bound. With O'Brien-Fleming
  type spending over two looks, its true Type I error is 0.0240 against a bound of
  0.025, and its final boundary is z = 1.987 against gsDesign's 1.969. Power falls
  from 0.900 to 0.897. With Pocock type spending the true error is 0.0216 and power
  falls to 0.877.
- **Power.** For two proportions StatClaim matches `power.prop.test` to six
  decimals. For two means it is above `power.t.test` by less than 0.001 at 400 per
  arm or more, since it uses the normal distribution, not the noncentral t.
- **Observational power.** For seven cohort and case-control designs, and three that fix
  only their total, StatClaim's exact
  power equals R's enumeration with `fisher.test` to twelve decimals, and
  `exact2x2::power2x2` with `strict = TRUE` to within its error bound of 1e-6. Its default
  doubles a one-sided test instead, which gives up to 0.075 less power with unequal
  groups. epiR's normal formulas differ from the exact power by up to 0.09. McNemar's
  test and the rate test agree with enumeration to twelve decimals, and with
  `exact2x2::powerPaired2x2(strict = TRUE)` within 1e-6.
- **Cluster trials.** For six cluster-mean and four cluster-proportion designs,
  StatClaim's noncentral t equals `power.t.test` (equal arms) and `pt` (unequal
  arms) to twelve decimals, and its searches find the same number of clusters and
  cluster size as R. CRTSize's normal formula asks for 0.2 to 1.9 fewer clusters per
  arm before rounding, since it ignores the t distribution.
- **Survival times.** For five designs, with and without accrual and dropout,
  StatClaim's expected events equal `eEvents` and numerical integration to ten
  decimals, and its power equals Schoenfeld's formula at them to twelve. Its
  searches find the smallest arm sizes above rpact's and nSurv's unrounded totals,
  which agree with each other.
- **Correlation and slope.** For six correlations and four slopes, StatClaim's power
  equals R's numerical integration to twelve decimals, and 40,000 simulated studies
  each agree within four standard errors. `pwr.r.test` (Fisher's z) differs by up to
  0.003; `pwr.f2.test`, which holds the exposure fixed, gives up to 0.006 more power.
- **Regressions.** StatClaim's power reaches the target exactly at the unrounded
  sizes pwrss gives for Hsieh's formulas, equals Signorini's formula to nine decimals
  (pwrss adds the other tail, below 1e-6) and MESS's Connor formula to ten. At
  Hsieh's size, 4,000 simulated studies analysed with `glm` give 0.802 against 0.80.
- **Surveys.** A survey's power reaches the target at the design effect times pwrss's
  simple-random size, to nine decimals; the slope's Wald power agrees to twelve.
- **DeclareDesign.** For 100 per arm and a difference of 0.4 standard deviations,
  2,000 simulations give power 0.81 (standard error 0.009), bias 0.002 and coverage
  0.96. StatClaim's normal approximation gives 0.807; `power.t.test` gives 0.804.
