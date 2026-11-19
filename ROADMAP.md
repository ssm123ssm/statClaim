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
  by participant or by cluster, under declared complete randomisation.
- A cited t-test on cluster-level summaries for cluster-randomised trials.

## Direction

Common trial methods with continuous or large-sample guarantees will be added as
contracts: the tool checks that the null, the multiplicity and the sampling plan
fit the method, and lists the assumptions it cites. Lean stays for exact designs
and for rules that combine tests. Each claim shows its
[evidence grade](docs/scope.md#evidence-grades).

## Next

1. Cluster-level tests for binary outcomes, repeated binary measurements, and strata
   on the assignment once a covariate-adjusted analysis reads them. Stratified
   and blocked randomisation for the randomisation test, and Monte Carlo p-values.
2. Cited group-sequential boundaries that use the correlation between looks.
3. A narrower exact interval for a difference of two proportions.
4. Larger sample sizes and p-values for the test with a margin.
5. Assurance and precision targets for planning.
6. More adaptive designs: several interim looks, efficacy stopping, allocation.
7. A formalized Beta posterior, so posterior rules need no stated closed form.
8. A versioned extension API for community modules.

Planning principles: scientific inputs stay explicit; a sufficient sample size
and the smallest one are separate claims; composing verified parts never
certifies a whole design by itself. Calculations, simulations and proofs stay
distinguishable in every report. See the [planning roadmap](docs/study-planning.md).

## Before a stable 1.0

Document migration rules; test supported platforms and clean installs; have
independent statistical and proof review; keep proof assumptions visible;
verify negative cases and certificate tampering; agree which APIs are stable.
A preview release does not promise language compatibility.
