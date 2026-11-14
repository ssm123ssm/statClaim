# Exact test specification: Fisher, two-sided, probability ordering

Specification version: `0.1.0`.
Test identifier: `fisher_exact_two_sided_probability_ordered`.

## Sampling model and target claim

Let `X ~ Binomial(n_control, p_control)` and
`Y ~ Binomial(n_treatment, p_treatment)` be independent. Both sample sizes are
positive integers fixed before outcomes are observed. Test the null hypothesis
`p_control = p_treatment = p`, with `p` anywhere in `[0, 1]`.

The target theorem is that this specified procedure rejects with probability at
most `1/20` under that null, for every such common `p`. Discreteness can make the
actual rejection probability smaller than `1/20`. The procedure does not
randomize. The current software computes the test; the full target theorem and
implementation correspondence have not yet been checked in Lean.

## Inputs and table convention

The design supplies positive integer arm sizes. The command supplies integer
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
`sum_k w(k) = D`, so these conditional masses sum to one. These mathematical
steps still need their project-specific Lean formalization.

## P-value and rejection rule

For the observed control count `x`, define

```text
p_value(x, y) = sum_{k in [L, U], w(k) <= w(x)} w(k) / D
reject       = (p_value(x, y) <= 1/20)
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

`src/statproof/fisher.py` uses Python's arbitrary-precision integers, `math.comb`,
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

## Lean proof completed in this version

`StatProof/FinitePValue.lean` defines `probabilityOrderedPValue` on a finite
support with rational masses and proves
`StatProof.probabilityOrdered_rejection_mass_le`:

```text
For nonnegative masses and alpha >= 0,
sum_{x : probabilityOrderedPValue(x) <= alpha} mass(x) <= alpha.
```

The result even holds for unnormalized masses. When the masses sum to one, the
left side is the probability of rejection. The proof selects a rejected outcome
with maximum mass, observes that every rejected outcome is counted in its
p-value, and bounds the rejected mass by that p-value. An empty rejection set is
handled separately. No proof placeholders or additional project axioms are used.

This theorem has not yet been specialized to the conditional weights above and
does not verify the Python implementation.

## Remaining proof and application obligations

1. Formalize the hypergeometric support, masses, normalization, and their
   correspondence with the executable integer calculation.
2. Derive that conditional distribution from independent binomial samples under
   the equal-proportions null for `0 < p < 1`.
3. Apply the finite-distribution lemma in each stratum of the total success count
   and combine the conditional bounds by total probability.
4. Handle `p = 0` and `p = 1` separately: the only observed tables have p-value `1`.
5. Validate the declaration-to-theorem translation and bind any future certificate
   to the actual checked theorem, inputs, backend, and module versions.

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
- `lake build` checks the generic finite-distribution theorem with Lean.

The enumerations and external comparisons are software-validation evidence for
their tested cases. They do not replace the remaining general formal proof.
