# First planning example

**Proposed syntax and behavior; these constructors are not implemented.**
This is a concrete target for the [planning roadmap](../study-planning.md).
The rates and targets below are illustrative inputs, not hidden defaults.

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
let target = power_target(
    at=alternative,
    minimum=4/5,
    maximum_typeI=1/20,
)
let feasibility = meets(analysis=analysis, target=target)
let calculation = calculate(feasibility)
let verification = verify(feasibility)
let status = verification.status
let evidence = verification.evidence
```

`alternative` is a parameter point used for planning. It does not replace the
analysis's equality null. The difference alone would not specify both rates.
`minimum` refers to power at this point, not a guarantee for every alternative.
`alpha` defines the analysis's rejection rule; `maximum_typeI` is the requested
error bound under its null. They happen to match in this example.

Expected behavior after implementation:

```text
calculation.status: calculated
  power: approximately 0.4920329563603535
  power_target_met: false

verification.status: unresolved_obligation
  diagnostic: power_target_not_met
  evidence: absent for the combined planning claim
```

The existing Fisher Type I theorem can support the error component, but does
not establish the unmet power component. Reports should show the components
separately. Failing this planning claim says nothing about whether the null is true.

## Find a sufficient sample size

Continue the same proposed file:

```stat
let candidates = equal_arm_sizes(
    analysis=analysis,
    min_per_arm=2,
    max_per_arm=40,
)
let sizing = sample_size(candidates=candidates, target=target)
let recommendation = calculate(sizing)
let sizing_verification = verify(sizing)
let sizing_status = sizing_verification.status
let sizing_evidence = sizing_verification.evidence
```

`candidates` describes a finite design space. Candidates use new arm sizes with
the design/null rebound to each new model, preserving fixed sampling, the null
predicate, test and alpha. The rates remain a point in the same parameter space.
The original analysis stays unchanged. Execution searches inclusive bounds in
ascending order with step one; the claim asks for a candidate meeting the target.

```text
recommendation.status: calculated
  n_control: 36
  n_treatment: 36
  total_sample_size: 72
  power: approximately 0.8003902630552112
  power_target_met: true
  minimum_sample_size_claim: not_requested
```

Once its proof adapter exists, successful `verify(sizing)` must certify the
selected design's Type I and power bounds and identify that design in evidence.
Sufficiency does not certify minimality. Exhausting the search reports no feasible
candidate in this space, without a claim about other designs or larger samples.

## Interface decisions

- All objects stay immutable; a target is reusable across designs and searches.
- `calculate` computes; `verify` establishes all requested components. Neither runs
  while editing. Results remain pending until explicit execution.
- `verify(sizing)` checks the static search claim and certifies a witness, without
  consuming runtime recommendation fields. Matching requests may share computation.
- Compilation checks types, rates in `[0,1]`, an alternative outside the null,
  bounds and adapter availability. Failed checks produce diagnostics, not evidence.
- Publish typed result fields and Claims view entries for sizes, power, component
  status and optional evidence. Retain exact fractions; decimals are display only.
- Later Bayesian assurance/precision targets should reuse `meets`/`sample_size`;
  Type I calibration is optional for those targets, requested explicitly.

## Numerical reference and implementation boundary

These reference values sum independent binomial probabilities over the existing
Fisher rejection region with exact arithmetic. P-values were cross-checked by
direct table-weight enumeration. They are not yet Lean-certified power results.
All equal-arm sizes from 2 through 40 were checked: 36 is the first passing size;
35 gives approximately 0.7847697628681884. Do not assume monotonicity in the search.

Implementation tests should cover these values, exhausted searches, invalid
inputs, changed assumptions, component failures and certificate replay.
