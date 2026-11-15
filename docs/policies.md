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

- The null and the alternative are single response rates. The Type I claim is
  at the declared null rate, not for every smaller rate.
- The posterior rule is *defined* by the binomial-sum form of the Beta tail.
  Its identity with the Beta integral is standard but not proved in Lean.
  Operating characteristics are proved for the rule as defined.
- A posterior threshold is a decision rule. Its Type I error and power are
  separate, repeated-sampling claims about the complete policy.

## Fisher power

`StatProof/Modules/FisherPower.lean` gives the exact power of the fixed Fisher
analysis at one pair of rational success probabilities. The rejection region is
recomputed in the kernel from the formal p-value. Power at a planning point says
nothing about other alternatives.

See `tests/lean/Policies.lean` for checked and deliberately failing examples.
