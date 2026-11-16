# Exact test specification: Fisher, two-sided, probability ordering

Specification version: `0.2.0`.
Test identifier: `fisher_exact_two_sided_probability_ordered`.

## Sampling model and target claim

Let `X ~ Binomial(n_control, p_control)` and
`Y ~ Binomial(n_treatment, p_treatment)` be independent. Both sample sizes are
positive integers fixed before outcomes are observed. Test the null hypothesis
`p_control = p_treatment = p`, with `p` anywhere in `[0, 1]`.

The target theorem is that this specified procedure rejects with probability at
most the declared exact `alpha` in `[0,1]` under that null, for every such common `p`.
The default is `1/20`. Discreteness can make the actual rejection probability smaller. The procedure does not
randomize. The mathematical target is now checked in Lean as
`StatClaim.fisher_typeI_error_le_alpha`, against the product of Mathlib's binomial
measures. Correspondence between a Python execution and that formal rejection
event is now checked per result by the `verify` command. The fast `test` command
does not perform that check.

## Inputs and table convention

The design supplies positive integer arm sizes. An optional `[analysis]` table
supplies `alpha` as an exact string, such as `"1/40"`; omitting it uses `1/20`. The command supplies integer
counts `x` and `y`, with `0 <= x <= n_control` and `0 <= y <= n_treatment`.
Booleans, fractional counts, zero arm sizes, unknown design fields, and unsupported
design options are rejected.

| Arm | Success | Failure |
| --- | ---: | ---: |
| Control | `x` | `n_control - x` |
| Treatment | `y` | `n_treatment - y` |

## Conditional distribution

Write `s = x + y` and `N = n_control + n_treatment`. Conditional on the pooled
success count `s`, the intended null distribution of the control count has support

```text
L = max(0, s - n_treatment)
U = min(n_control, s)
```

For each integer `k` from `L` through `U`, define

```text
w(k) = choose(n_control, k) * choose(n_treatment, s - k)
D    = choose(N, s)
q(k) = w(k) / D
```

`D` is positive for valid observations. Vandermonde's identity gives
`sum_k w(k) = D`, so these conditional masses sum to one. These facts are checked
in `StatClaim/Hypergeometric.lean`. `StatClaim/BinomialModel.lean` proves that
these masses give the finite conditional probabilities whenever the pooled total
has positive probability.

## P-value and rejection rule

For the observed control count `x`, define

```text
p_value(x, y) = sum_{k in [L, U], w(k) <= w(x)} w(k) / D
reject       = (p_value(x, y) <= alpha)
```

All tables with probability equal to the observed table are included. This is
probability ordering, rather than doubling a one-sided tail or using a mid-p
adjustment. It follows the two-sided convention documented for
[R's `stats::fisher.test`](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/fisher.test.html).
R's floating-point implementation may handle near ties using numerical tolerance;
this implementation compares integer weights exactly.

The threshold comparison is inclusive and exact. For example, arm sizes `1` and
`19`, with successes `0` and `19`, produce `p_value = 1/20` and rejection.
With all observations failures or all observations successes, the conditional
support contains one table and the p-value is `1`.

## Executable calculation

`src/statclaim/fisher.py` uses Python's arbitrary-precision integers, `math.comb`,
and `fractions.Fraction`. It enumerates each feasible control count and adds the
weights meeting the probability-ordering condition. To avoid recomputing both
binomial coefficients at every point, neighboring weights use the exact identity

```text
w(k + 1) = w(k) * (n_control - k) * (s - k)
           / ((k + 1) * (n_treatment - s + k + 1))
```

The division is integral on the interior of the support. The final fraction is
reduced by `Fraction`. Decimal output is a rounded display approximation with 18
significant digits; neither table ordering nor rejection uses that approximation.
There are `U - L + 1` enumeration steps. Large-integer arithmetic and output size
grow with the sample sizes; no approximation or simulation is substituted for a
large problem.

The calculation returns the exact p-value, observed conditional table probability,
support bounds, table convention, exact threshold, and threshold comparison.
It does not estimate an odds ratio, produce a confidence interval, assess power,
or establish that the sampling assumptions hold for the study.

## Lean proofs completed

`StatClaim/FinitePValue.lean` defines `probabilityOrderedPValue` on a finite
support with rational masses and proves
`StatClaim.probabilityOrdered_rejection_mass_le`:

```text
For nonnegative masses and alpha >= 0,
sum_{x : probabilityOrderedPValue(x) <= alpha} mass(x) <= alpha.
```

The result even holds for unnormalized masses. When the masses sum to one, the
left side is the probability of rejection. The proof selects a rejected outcome
with maximum mass, observes that every rejected outcome is counted in its
p-value, and bounds the rejected mass by that p-value. An empty rejection set is
handled separately. No proof placeholders or additional project axioms are used.

`StatClaim/Hypergeometric.lean` specializes the generic theorem to the conditional
weights, proves their normalization, and proves that rational probability
ordering equals integer weight ordering. The latter gives the exact integer
ratio specified above, with the same inclusive support bounds as the executable.

`StatClaim/BinomialModel.lean` defines the independent-binomial joint masses,
proves their normalization, and partitions every feasible pair of observed counts
by its pooled total. It proves that each joint mass factors into a pooled
binomial mass and the rational hypergeometric mass. Summing the conditional bounds
therefore gives the uniform unconditional bound.

`StatClaim/Fisher.lean` connects those finite masses to Mathlib's product of
binomial probability measures. Its generalized theorem, `StatClaim.fisher_typeI_error_le_alpha`,
states that the probability of the Lean-defined rejection region at a nonnegative
rational `alpha` is at most that `alpha`, for all arm sizes and all common real probabilities in the closed unit
interval. The application restricts arm sizes to positive integers; the theorem
also supports zero-sized arms.

The argument never divides by a pooled event probability to establish the
unconditional bound. It consequently includes `p = 0` and `p = 1` directly,
without defining conditional probabilities for impossible totals. A separate
conditional-probability formula requires a positive-probability pooled total.

`StatClaim/Computation.lean` proves an efficient factorial-based integer formula
equal to the formal weights. For a proposed rational result, a checked natural
cross-product equality proves equality to the formal p-value. `verify` uses
`decide +kernel` for those integer checks and instantiates the model theorem for
the declared sizes. It also checks the observed table probability, support bounds,
valid counts, and reported rejection decision, and audits the generated proofs.

The original `fisher_typeI_error_le` remains the default 5% specialization.
The [multiple-testing module](multiple-testing.md) composes these individual
bounds under explicit common-law marginal contracts.

See the [proof walkthrough](formal-proof.md) and [certificate guide](certificates.md).
This is per-result verification; the Python implementation is not universally proved.

## Assumptions and remaining trust

The parser and generated numeral statements map the validated declaration to the
theorem. The canonical inputs and generated proof are retained and hashed, and
replay reconstructs the expected statements before rerunning Lean. This application
mapping is tested and explicitly trusted, rather than itself formally verified.

Certificates bind exact inputs, result fractions, generated statements, theorem
names, toolchain/dependency pins, and source/artifact snapshots. They list the
sampling assumptions and trusted components. They establish their named properties
for that result and mathematical model, not correctness of all Python executions
or the truth of real-world sampling assumptions.

Adding data-dependent stopping changes these obligations. The application may
compute the fixed-margin statistic for the supplied counts, but withholds a
procedure-level decision and certificate for that modification. It reports the
missing justification, without claiming that the error rate is inflated.

## Validation evidence

- Exhaustive direct combinatorial checks cover every table with both arm sizes
  from `1` through `8`, including exact conditional rejection-mass checks.
- Tests cover probability ties, row/outcome swaps, degenerate margins, inclusive
  rejection at `1/20`, invalid inputs, and a p-value below floating-point range.
- `scripts/compare_with_r.py` compares all small tables and selected larger ones
  with R's two-sided `fisher.test`, using relative tolerance `1e-10`. The compact
  offline fixture records the generating R version and regeneration command.
- `lake build` checks normalization, the conditional law, the finite-model bound,
  and the final theorem against Mathlib's binomial probability measures.
- Concrete Lean examples check support bounds, exact two-sided values, equality
  at the rejection threshold, degenerate totals, and theorem instances at both
  null endpoints. A transitive audit rejects unexpected theorem assumptions.
- Integration checks run the actual Lean backend, certify the demo and boundary
  cases, replay a certificate, and reject incorrect numerical candidates and
  altered or self-consistently rehashed false claims.

The enumerations and external comparisons are software-validation evidence for
their tested cases. `verify` provides the separate formal evidence for a checked
individual result and its explicitly scoped mathematical guarantee.
