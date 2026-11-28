# Scope and trust

What is supported:

- **Two arms.** Fixed samples from two independent binomial arms, an equality
  null, and the two-sided Fisher test in exact rational arithmetic.
- **Two arms, one-sided.** The one-sided Fisher test of "treatment no better than
  control". Its error bound covers every such pair of rates.
- **Two arms, unpooled Wald.** A pre-data Type I error certificate for the
  two-sided Wald rule with equal fixed binomial arm sizes and an equality null.
  Specify `squared_cutoff` for the rule and `alpha` for the requested error ceiling.
  The rule rejects when the squared observed difference exceeds `squared_cutoff`
  times the estimated variance, including when that variance is zero.
  [The 20-per-arm example](../examples/wald_bound.stat) uses a cutoff of 1.96
  and verifies a ceiling of 8.24% over the entire null.
  If the upper-bound search falls short, statClaim tries candidate null rates.
  A Lean-checked exact rejection probability above the ceiling refutes the claim.
- **Two arms, pooled score.** `score_test` uses the pooled variance for the two-sided
  test of equal proportions, with fixed and equal binomial arm sizes. The
  [20-per-arm example](../examples/score_bound.stat) uses a critical value of
  1.96 and a Type I error ceiling of 5.4%. Change the ceiling to 5% to check a
  counterexample at a common success rate of 25%.
- **Two arms, Pearson chi-square.** `pearson_test` accepts unequal or equal
  fixed binomial arm sizes and an equality null. The optional `correction="yates"`
  applies the [continuity correction](https://search.r-project.org/R/refmans/stats/html/chisq.test.html)
  used for a two-by-two table. Lean checks the error over all common rates or
  certifies an exact counterexample. [Worked example](../examples/tutorial/51_pearson_unequal_arms.stat).
- **Two arms, Farrington–Manning.** A one-sided noninferiority score rule with
  independent fixed binomial arms, a margin strictly between −1 and 0, and a
  positive rational squared cutoff. Lean checks rational brackets for the
  constrained maximum-likelihood fit for each relevant table. An enclosing
  rejection region gives an upper bound over the whole composite null. An
  inner region can refute the ceiling at a pair of rates on the null boundary.
  [Worked example](../examples/tutorial/49_farrington_manning.stat).
- **Matched pairs, uncorrected McNemar.** The two-sided chi-square rule uses the
  observed number of discordant pairs and their imbalance. Lean checks a
  bound over every discordance probability or an exact rational witness above
  the ceiling. [Worked example](../examples/tutorial/48_asymptotic_mcnemar.stat).
- **Two arms with a margin.** An exact test of "treatment exceeds control by at
  most a margin", for non-inferiority or superiority, with an error bound over
  the whole null. Up to 120 participants per arm.
- **Several endpoints.** Bonferroni composition of two to twenty Fisher
  endpoints, with any allocation that sums to at most the family level.
- **Planning.** Exact Fisher power at one declared point and a bounded
  sample-size search with equal or unequal allocation. A size can be certified
  as sufficient, or as the smallest sufficient size in the declared range. The
  same holds for Fisher's test of association in every observational design (a
  design that fixes only its total up to 150 participants, with sufficient sizes
  only), for McNemar's test, and for the rate test given its number of events.
- **One arm.** The one-sided exact binomial test, for planning and for an
  observed count, and exact confidence intervals with coverage for every true
  rate. The two-sided `binomial_score_test` checks the exact rejection
  probability at a specified null rate. [Worked example](../examples/tutorial/50_one_sample_score.stat).
- **Difference of two proportions.** A confidence interval built from an exact
  interval per arm. It has checked coverage for every pair of rates and is
  conservative.
- **Two stages.** A single-arm design with an interim stop, using count or
  Beta-posterior rules. Type I error and power are checked for the whole design,
  and the decision for observed counts is checked against the declared rule.
- **Randomisation tests.** Under declared complete, stratified or blocked
  randomisation of participants or clusters, the randomisation test of the sharp
  null has Type I error at most alpha for any statistic fixed in advance,
  whatever the outcomes. One Lean theorem covers every design. The p-value counts
  every possible assignment, or compares the observed one with a declared number
  of random draws (Monte Carlo); both are proved. The test can be a member of a
  family, a fixed sequence or a graph.
- **Observational studies.** Cross-sectional, cohort and case-control studies,
  whose exposure was not assigned. Fisher's exact test of no association is
  proved for each: with the two group sizes fixed by a cohort or case-control
  design, and with only the total fixed, by averaging over the number exposed.
  Tests of randomised arms refuse these designs. An observed table gives a
  checked p-value and decision, and intervals for the odds ratio, the risk ratio
  and difference (cohort) or the prevalence ratio and difference
  (cross-sectional), with joint coverage proved for every pair of probabilities.
  A design refuses a measure it cannot estimate. A 1:1 matched case-control
  study takes McNemar's exact test and an interval for the conditional odds
  ratio, both proved, and refuses unmatched analyses. Prevalence and cumulative
  incidence have exact intervals; a person-time cohort has an exact test of equal
  incidence rates and an interval for their ratio. Regression with covariates,
  correlations and design-based survey analyses are cited; proved methods refuse
  continuous variables and complex samples. A bound concerns association,
  never an effect of the exposure. See [observational studies](observational.md).

- **Cluster-randomised trials, cited.** A t-test on one summary per cluster, a
  mean or a proportion of responders, with the clusters as the sample size and at
  least four per arm. It assumes
  independent clusters, which randomising clusters does not contradict. Its
  references await review. Power comes from the noncentral t with the design
  effect, given the intracluster correlation; searches vary the clusters per arm
  or the participants in each.
- **Mixed models and logistic regression, cited.** A treatment contrast from a
  mixed model for repeated measures, and the treatment coefficient of a logistic
  regression. Both list their own assumptions, such as missing at random.
- **Declared tests.** Any other analysis can be named and vouched for. Only its
  fit to the design is checked.
- **Graphical procedures.** Tests with starting shares of the level and rules
  for passing a share on after a rejection. The contract checks the graph; the
  procedure's guarantee is cited.
- **Nesting.** A family, sequence, graph or design with looks can be an entry of
  a family or a sequence.
- **Fixed sequences.** Endpoints tested in a fixed order, each at the full level
  and only after every earlier one was rejected. Lean checks the rule; each
  test's own bound is assumed. A design with interim looks can be an entry.
- **Interim looks.** One test at several prespecified looks, with the error
  level split across them. Lean checks the split; each look's own bound is
  assumed. The split is conservative and ignores the correlation between looks.
- **Spending boundaries, cited.** O'Brien-Fleming or Pocock boundaries that use the
  correlation between looks, for Fisher's test and the t-tests. StatClaim computes
  them and checks each look's level against its boundary; the rule is cited, with a
  large-sample guarantee. Lean checks one question at growing sizes.
- **Look sizes.** Every look's size searched freely by a minimax or optimal
  criterion: exact for Fisher's test, simulated for t-tests. A calculation.
- **Mixed families.** Bonferroni over supported exact two-arm tests and cited tests. Finite-sample audits of asymptotic rules are supported for individual claims.
  Lean checks that the levels fit the budget and that the union bound gives the
  family bound. Each member's own bound is a hypothesis of that theorem.
- **Two survival curves, cited.** The two-sided log-rank test, with a
  large-sample guarantee in the number of events. Its power can be planned at a
  number of events, or at exponential survival times with accrual, follow-up and
  dropout, whose expected events let arm sizes be searched.
- **Two means, cited.** Pooled-variance and Welch t-tests, two-sided or
  one-sided with a margin. The contract is checked; the guarantee is cited from
  the literature and not proved. See [cited methods](cited-methods.md).
- **Precision, calculated.** Sample sizes for a margin of error, absolute or relative,
  with an optional assurance, for every interval StatClaim reports, and the normal
  interval with a design effect and finite population for surveys. Not checked by Lean.
- **Power for cited tests, calculated.** Approximate power and the value the
  estimate must pass, from a normal formula (the noncentral t for cluster tests,
  a correlation and a regression slope), and a sample-size search. The cited
  observational regressions have formulas too, and the survey tests are planned
  through a declared design effect. Status
  `calculated`, never verified. See
  [power for cited tests](planning.md#power-for-cited-tests).

Error bounds for single-arm designs cover every rate at or below the null rate.
Power is always at one declared planning point. The posterior rule's closed
form is a definition; its identity with the Beta integral is not proved in Lean.

The Fisher analyses reject nulls they do not support, with guidance; an
equality null with a nonzero difference has no supporting analysis yet. Declaring a Fisher analysis `adaptive` leaves its Type I error
obligation unresolved; use a complete two-stage design instead.

The design theorem concerns repeated-sampling Type I error. A result certificate
checks the observed calculation and decision. These are different claims.
Neither certifies recruitment, data quality, model fit or a causal conclusion.
Independence, the sampling law and other declared assumptions must match reality.

`calculate` produces a calculation, not proof evidence. `compile` and the LSP
inspect requirements without verification. `verify` creates evidence only when
its backend succeeds. Missing or failed verification leaves evidence absent.

## Evidence grades

Every piece of evidence states how its guarantee was established:

| Grade | Meaning |
| --- | --- |
| `proved` | Proved in Lean. |
| `conditional` | The combination is proved in Lean; each member's own guarantee is assumed. |
| `cited` | Taken from the literature; not machine-checked. |
| `simulated` | Estimated by simulation; not a proof. |
| `declared` | Stated by the author; not checked and not cited. |

A grade is shorthand for two facts, also available separately:
`evidence.sources` says where the statement comes from (a Lean proof, the
literature or a simulation), and `evidence.machine_checked` says how far a
machine checked it (the guarantee, only the composition, or only the contract).

Every claim also states its scope: `finite_sample` for a bound that holds at the
declared sample size, or `asymptotic` for a large-sample approximation. The two
are never shown as the same thing.

The exact modules are `proved` and `finite_sample`. The t-tests are `cited`;
Welch's is also `asymptotic`. A Bonferroni family with a cited member is
`conditional`. Read them with `evidence.grade` and `claim.scope`.

`simulate(...)` requests have the status `simulated`: power and Type I error
estimated from simulated studies, with 95% intervals. Like calculations, they
give numbers, not evidence, and do not weaken a file's status.

Each grade has its own result status, so a status never overstates its evidence:
`proved` gives `verified`, `conditional` gives `conditional`, `cited` gives
`cited` and `declared` gives `declared`. Cited and declared evidence have no
certificate; a conditional certificate states that the members are assumed.

A result is only as strong as its weakest part. A combination's status describes
its own rule, so each result also names the weakest grade inside it, and a file
reports the weakest part anywhere in it. A proved combination of cited tests
makes the file `cited`, and one declared test makes it `declared`.

With Lean available, every check builds the whole program in Lean: Lean decides
the contracts of its declarations and proves each claim as the semantics in
`StatClaim/Semantics/` defines it, so the protocol is checked as one program. Certificates record
source/toolchain hashes and can be replayed. Trust includes the Lean kernel and
declared axioms, the pinned dependencies, the semantics that turns statistical
intent into formal statements, the parser and elaborator, and Lean's JSON
printer. Lean checks that the data it reads is the compiled program, and proves
that the printed form determines that data (`Program.form_injective`). CI audits Lean sources and
axioms and tests modified certificates. Read the statement and assumptions;
passing tests alone cannot establish that a new method models the intended study.

## What a verified claim does not cover

Every status concerns the study as declared in the file, under the listed
assumptions. It says nothing about how the study is run. Three examples:

- **An endpoint chosen after seeing data.** A file that declares only the
  endpoint finally reported gets a verified test of that endpoint. The choice
  made after an interim comparison is not in the file, so it is not checked. The
  listed assumption "the analysis and its level are chosen before outcomes are
  observed" is the one that fails.
- **Participants excluded after randomisation.** A per-protocol analysis
  declared with the remaining numbers is verified for those numbers. It says
  nothing about the population that was randomised. Declared with
  `population="per_protocol"`, the claim says it covers that population only,
  and a randomisation test is refused.
- **A randomisation test read as a test of means.** A verified randomisation
  test bounds error under the sharp null that treatment changes no one's
  outcome. It says nothing about equal means when effects differ between
  participants.
- **Repeated measurements counted as participants.** Three measurements on each
  of 100 participants, declared as 300 per arm, get a cited t-test. The listed
  assumption that observations are independent is the one that fails.

Declare what you can, so that it can be checked. For example, `better="lower"`
on a model has the direction of a one-sided null checked; left out, the
direction is listed as an assumption. Declaring the three measurements with
`continuous_outcome(measurements=3)`, or randomised clinics with
`cluster_assignment(...)`, turns the third example into a refusal of any test
that assumes independent observations. `replication/results.md` lists such
cases with what StatClaim reports for each.

## Related work

- [StatWhy](https://arxiv.org/abs/2405.17492) verifies annotated hypothesis-testing
  programs with Why3 and automated provers. It checks that test routines are used
  within their contracts, and trusts the routines themselves.
- [DeclareDesign](https://declaredesign.org/) declares research designs and
  diagnoses properties such as power and bias by simulation, without deductive
  guarantees.

StatClaim differs in checking the guarantees themselves in Lean, for exact
finite designs. See the [project background](background.md).

See [formal proof](formal-proof.md) and [certificates](certificates.md).
