# Sampling and decision policies

A fixed-sample design observes the model's outcome directly. An adaptive design
does not: what is recorded depends on interim decisions. `StatProof/Core/Policy.lean`
therefore describes a design as a **policy**:

- the law of all *potential* data, for each parameter value;
- a measurable rule mapping potential data to the *record* actually observed.

The record has its own type. A policy's law is derived from these two parts,
so a stopping rule is part of the design, not an exception to a fixed-sample
model. Fixed sampling is the special case whose record is the potential data;
`TypeIGuarantee.toPolicy` carries existing fixed-sample guarantees across.

A `PolicyAnalysis` adds a hypothesis and the set of records that reject it.
Two claim forms are defined on it:

| Claim | Statement |
| --- | --- |
| `typeIClaim bound` | rejection probability ≤ bound for every parameter in the hypothesis |
| `powerClaim alternative bound` | rejection probability ≥ bound for every parameter in the alternative |

A guarantee for a policy comes from a theorem about that policy. Resembling a
fixed-sample design establishes nothing.

## Two-stage binomial design

`StatProof/Modules/TwoStageBinomial.lean` is the first adaptive module: one arm,
a first stage, an interim futility stop, and a final decision. Two rule families
are provided:

- `thresholdDesign`: continue above an interim count, reject above a total count
  (Simon-type designs);
- `posteriorDesign`: continue or declare success when the posterior probability
  that the response rate exceeds a reference reaches a declared level, under a
  Beta prior with positive integer parameters.

For a rational response rate, the policy's exact rejection probability is a
ratio of natural numbers (`rejection_probability`). `typeI_of_check` and
`power_of_check` turn one kernel-checked comparison into the claim for that
specific design. No general theorem about two-stage designs is assumed.

Current limits, stated plainly:

- The null is every rate at or below the reference rate
  (`typeI_atMost_of_check`); both rule families are proved monotone in the
  response counts. Power is at a single rate.
- The posterior rule is *defined* by the binomial-sum form of the Beta tail.
  Its identity with the Beta integral is standard but not proved in Lean.
  Operating characteristics are proved for the rule as defined.
- A posterior threshold is a decision rule. Its Type I error and power are
  separate, repeated-sampling claims about the complete policy.

## One-sample binomial test

`StatProof/Modules/OneSampleBinomial.lean` is the one-sided exact binomial
test. Its Type I bound is checked at the reference rate and holds for every
smaller rate.

Both composite-null results rest on `StatProof/BinomialMonotone.lean`: the
probability of an upper set of counts does not decrease as the rate increases.

## Confidence intervals

`StatProof/Modules/BinomialInterval.lean` defines the exact confidence set for
a binomial proportion and proves its coverage for every true rate (`coverage`).
`interval_contains` places the set for one observed count inside an interval
with rational endpoints, using two kernel checks.

For two independent arms, `joint_coverage` bounds the probability that both
arms' sets contain their rates, and `difference_contains` turns the two
intervals into one for the difference.

## One-sided Fisher test

`StatProof/Modules/FisherOneSided.lean` rejects when the one-sided conditional
p-value is small. `boundary_le` bounds the error at equal rates for every
sample size. `typeI_of_hints` extends it to every pair with the treatment rate
at most the control rate, using the fact that one more treatment success never
turns a rejection into a non-rejection. That fact is checked for the declared
design from kernel-validated thresholds.

## Tests with a margin

`StatProof/Modules/DifferenceTest.lean` handles the null
`p_treatment - p_control ≤ margin`. A test is a list of thresholds that never
decrease with control successes. Its rejection region is then a lower set in
control successes and an upper set in treatment successes, so by
`productBinomial_real_le_corner` its probability over a rectangle of rates is
largest at one corner. `typeI_of_cells` takes a checked list of intervals of
the control rate and concludes the bound for the whole null.

## Fisher power

`StatProof/Modules/FisherPower.lean` gives the exact power of the fixed Fisher
analysis at one pair of rational success probabilities. The rejection region is
recomputed in the kernel from the formal p-value. Power at a planning point says
nothing about other alternatives.

See `tests/lean/Policies.lean` for checked and deliberately failing examples,
and [planning a study](planning.md) for the `.stat` interface.
