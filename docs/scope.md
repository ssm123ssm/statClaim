# Scope and trust

What is supported:

- **Two arms.** Fixed samples from two independent binomial arms, an equality
  null, and the two-sided Fisher test in exact rational arithmetic.
- **Two arms, one-sided.** The one-sided Fisher test of "treatment no better than
  control". Its error bound covers every such pair of rates.
- **Two arms with a margin.** An exact test of "treatment exceeds control by at
  most a margin", for non-inferiority or superiority, with an error bound over
  the whole null. Up to 120 participants per arm.
- **Several endpoints.** Bonferroni composition of two to twenty Fisher
  endpoints, with any allocation that sums to at most the family level.
- **Planning.** Exact Fisher power at one declared point and a bounded
  sample-size search with equal or unequal allocation. A size can be certified
  as sufficient, or as the smallest sufficient size in the declared range.
- **One arm.** The one-sided exact binomial test, for planning and for an
  observed count, and exact confidence intervals with coverage for every true
  rate.
- **Difference of two proportions.** A confidence interval built from an exact
  interval per arm. It has checked coverage for every pair of rates and is
  conservative.
- **Two stages.** A single-arm design with an interim stop, using count or
  Beta-posterior rules. Type I error and power are checked for the whole design,
  and the decision for observed counts is checked against the declared rule.

- **Two means, cited.** Pooled-variance and Welch t-tests, two-sided or
  one-sided with a margin. The contract is checked; the guarantee is cited from
  the literature and not proved. See [cited methods](cited-methods.md).

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
| `conditional` | Proved in Lean, given cited guarantees for the component tests. |
| `cited` | Taken from the literature; not machine-checked. |
| `simulated` | Estimated by simulation; not a proof. |

A grade is shorthand for two facts, also available separately:
`evidence.sources` says where the statement comes from (a Lean proof, the
literature or a simulation), and `evidence.machine_checked` says how far a
machine checked it (the guarantee, only the composition, or only the contract).

Every claim also states its scope: `finite_sample` for a bound that holds at the
declared sample size, or `asymptotic` for a large-sample approximation. The two
are never shown as the same thing.

The exact modules are `proved` and `finite_sample`. The t-tests are `cited`;
Welch's is also `asymptotic`. No module uses `conditional` or `simulated` yet.
Read them with `evidence.grade` and `claim.scope`. Only `proved` and
`conditional` evidence can give a `verified` status; cited evidence gives the
status `cited` and has no certificate.

Certificates record source/toolchain hashes and can be replayed. Trust includes
the Lean kernel and declared axioms, the pinned dependencies, and the translation
from statistical intent to the formal statement. CI audits Lean sources and
axioms and tests modified certificates. Read the statement and assumptions;
passing tests alone cannot establish that a new method models the intended study.

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
