# Roadmap

## 0.1 developer preview

- Typed study, null, analysis, claim and result objects.
- Fisher equality-null contracts, exact calculations and Lean certificates.
- One-sided Fisher test with an error bound over "treatment no better than control".
- Exact test with a margin (non-inferiority), up to 120 participants per arm.
- Bonferroni composition of two to twenty endpoints under declared joint laws.
- VS Code diagnostics and Claims view, Codespaces and contributor checks.
- Classified catalogue and documented scope.
- Contract derivations with an independent checker, study reports and change impact,
  for analyses, families, one-sample tests, two-stage designs and planning claims.
- Planning: exact Fisher power, target checks and a bounded sample-size search,
  with an optional smallest-in-range claim and unequal allocation.
- Sampling policies with their own records; a two-stage binomial design with
  count or Beta-posterior rules and checked Type I error and power.
- One-sided exact binomial test for a single arm: sample-size search and
  checked p-values for observed data.
- Exact confidence intervals for one proportion with checked coverage, and a
  conservative interval for a difference of two proportions.
- Search for optimal or minimax two-stage designs; the selected design is checked.
- Checked decisions for observed two-stage data.
- Evidence grades and guarantee scope on every claim.
- Cited t-tests for two means: the contract is checked, the guarantee is cited.
- Structured guarantees, named assumptions and versions for methods and rules.
- Bonferroni over proved and cited tests, with the combination proved in Lean.
- Outcomes and null forms as registry data; a cited log-rank test for survival.
- One-sided and margin tests in Bonferroni families.
- Interim looks with the error level split across them, the split proved in Lean.
- Fixed-sequence testing proved in Lean; designs with looks as entries of larger plans.
- A complete generated language reference.
- Graphical procedures with recycling (cited), and nesting of combinations.
- Replication materials: an error-injection evaluation and a re-check of Simon (1989).
- Cited mixed-model and logistic-regression tests; declared tests for anything else.
- Every result and file names its weakest part.
- Approximate power and sample-size search for cited tests, by calculation only.
- Two-arm models built from an assignment and an outcome; outcomes on the same
  participants can share one assignment.
- Randomisation by cluster and repeated measurements declared on the model, and
  tests whose independence assumptions they contradict refused.
- Randomisation tests of the sharp null, proved in Lean once for every design,
  by participant or by cluster, under declared complete, stratified or blocked
  randomisation, with exact or Monte Carlo p-values.
- A cited t-test on cluster-level means or proportions for cluster-randomised trials.
- Randomisation tests as members of families, fixed sequences and graphs.
- Who is analysed, declared on the assignment: everyone randomised or per protocol.
- Named outcomes, so a family cannot ask the same question of one outcome twice.
- Observational studies: cross-sectional, cohort and case-control designs, and
  Fisher's exact test of no association proved for each.
- Observed 2x2 tables with checked p-values, and conservative intervals for odds,
  risk and prevalence ratios and differences; each design estimates only what its
  sampling allows.
- Matched case-control studies: McNemar's exact test and the conditional odds
  ratio, proved in Lean; unmatched analyses refuse matched pairs.
- Prevalence and cumulative incidence with exact intervals, and person-time
  cohorts with an exact test of equal incidence rates and their ratio.
- Cited regression, correlation and survey tests for observational studies, with
  measurement scales and complex survey designs declared on the study.
- Exact power and sample sizes for Fisher's test of association in every
  observational design, McNemar's test and the rate test, checked in Lean and
  cross-checked against R.
- Power and sample sizes for cluster-randomised trials: the t-test on cluster
  summaries planned with the intracluster correlation, by number of clusters or
  cluster size, cross-checked against R.
- Sample sizes for the log-rank test from survival times: control median, accrual,
  follow-up and dropout give the expected events, cross-checked against rpact and
  gsDesign.
- Power and sample sizes for Pearson's correlation and the slope of a linear
  regression with covariates, exact under normality and cross-checked against R.
- Simulated power for cluster-randomised trials, with clusters of unequal sizes,
  cross-checked against a raw-data simulation in R.
- Simulated t-tests with unequal SDs or a skewed outcome, where Type I is judged on the
  simulation, cross-checked against a raw-data simulation in R.
- Simulated log-rank tests from survival times, with an effect that starts late,
  cross-checked against survival::survdiff in R.
- Simulated tests of a correlation or a regression slope with skewed data, cross-checked
  against cor.test and lm in R. Covariates and Spearman's test are not simulated yet.
- Simulated power of t-tests at interim looks: stopping at each look and the expected
  size, cross-checked against a raw-data simulation in R.
- Blinded sample-size re-estimation for Student's t-test, whose Type I error is judged
  by simulation at null scenarios listed on the target, cross-checked against R. Next:
  more adaptive rules (unblinded re-estimation, dropping an arm) on the same footing.
- Simulated power of families (Bonferroni, fixed sequence, graphical) of Fisher tests and
  t-tests with correlated endpoints: each endpoint, any and all, cross-checked against R.
- Exact power of the logistic regression trial test, summed over both arms' counts for its
  Wald test, matching glm on every table.
- Exact power of Fisher's test at interim looks, summed over every path of counts,
  matching a brute-force enumeration in R.
- Precision targets: sample sizes for a margin of error, absolute or relative, with an
  optional assurance, for every interval StatClaim reports, and for surveys through the
  normal interval with a design effect and a finite population correction.
- The protocol verified as one program in Lean: each program is elaborated into typed
  objects and encoded as Lean data, a semantics in Lean defines its claims, premises,
  grades and contracts, and Lean decides the contracts and proves every claim with one
  soundness theorem. Exact tests, results, intervals and plans share one interface,
  and the Python translator that stated claims before is retired.
- Power and sample sizes for every cited observational test: logistic, modified
  Poisson, conditional logistic and Poisson regressions, Spearman's correlation, linear
  regression on a yes-or-no exposure, and the survey tests through the design effect.

## Direction

Common trial methods with continuous or large-sample guarantees will be added as
contracts: the tool checks that the null, the multiplicity and the sampling plan
fit the method, and lists the assumptions it cites. Lean proves exact designs and
the rules that combine tests, and decides the contracts of every program. Each claim
shows its
[evidence grade](docs/scope.md#evidence-grades).

## Next

1. Repeated binary measurements, and strata
   on the assignment once a covariate-adjusted analysis reads them.
2. Cited group-sequential boundaries that use the correlation between looks.
3. A narrower exact interval for a difference of two proportions.
4. Larger sample sizes and p-values for the test with a margin.
5. Assurance in the Bayesian sense: power averaged over a design prior. (Precision
   targets, with the assurance that an interval meets its margin, are done.)
6. More adaptive designs: several interim looks, efficacy stopping, allocation.
7. A formalized Beta posterior, so posterior rules need no stated closed form.
8. A versioned extension API for community modules.

Planning principles: scientific inputs stay explicit; a sufficient sample size
and the smallest one are separate claims; composing verified parts never
certifies a whole design by itself. Calculations, simulations and proofs stay
distinguishable in every report. See the [planning roadmap](docs/study-planning.md).

## Future integrations

- **StatClaim Studio.** The block editor is in `studio/`. Next, use generative AI
  to turn a plain-language description of the study design and its goal into
  editable StatClaim code. Flag assumptions
  for the user to review and run the draft through the existing checker.
- **R package.** Let R users check StatClaim protocols from an R script and
  inspect claims, evidence grades and diagnostics as R objects. Use the same
  checker as the command-line tool.

## Before a stable 1.0

Document migration rules; test supported platforms and clean installs; have
independent statistical and proof review, including the Lean semantics that states
every claim; keep proof assumptions visible;
verify negative cases and certificate tampering; agree which APIs are stable.
A preview release does not promise language compatibility.
