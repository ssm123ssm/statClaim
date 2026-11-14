# Fisher proof walkthrough

The mathematical result is now checked in Lean:

> For two independent binomial samples with the same success probability,
> the specified two-sided Fisher rejection rule has probability at most `0.05`.

Sample sizes are fixed indices of the probability model. The common success
probability can be any real number from `0` through `1`. This establishes a
property of the declared mathematical model; it does not establish that a real
study follows that model or that a Python execution implements the formal rule.

## The final statement

In `StatProof/Fisher.lean`, `StatProof.fisher_typeI_error_le` states:

```lean
theorem fisher_typeI_error_le (nControl nTreatment : ℕ) (p : unitInterval) :
    (fisherNullLaw nControl nTreatment p).real
        (fisherRejectionRegion nControl nTreatment) ≤ (1 / 20 : ℝ)
```

- `p : unitInterval` means a real number in the closed interval `[0, 1]`.
- `fisherNullLaw` is the product of Mathlib's two binomial measures, so the
  samples are independent and share the null success probability.
- `fisherRejectionRegion` contains exactly the feasible tables whose formal
  probability-ordered p-value is at most `1/20`, including ties and equality.
- `.real` is the real-valued probability of that event. The null law is proved
  to be a probability measure, so this is a finite probability, not an arbitrary
  real conversion of an infinite measure.

The theorem quantifies over all natural-number arm sizes, so it also covers the
application's positive arm sizes. No sample sizes or success probabilities have
been fixed to numerical examples in the general proof.

## How the proof works

1. **Finite p-values:** `StatProof/FinitePValue.lean` proves that, for nonnegative
   rational masses, the total mass of outcomes with probability-ordered p-value
   at most `alpha` is at most `alpha`. All ties are included.
2. **Hypergeometric probabilities:** `StatProof/Hypergeometric.lean` defines the
   feasible counts and the integer weights `choose(nControl,k) *
   choose(nTreatment,total-k)`. Vandermonde's identity proves their sum is
   `choose(nControl+nTreatment,total)`. Division by that positive denominator
   gives a normalized distribution. The finite p-value theorem gives the
   conditional rejection bound.
3. **Independent binomial sampling:** `StatProof/BinomialModel.lean` defines the
   binomial point masses and their independent product, and proves they sum to
   one. A bijection partitions all feasible observed pairs by the pooled total.
   Each joint mass factors into a pooled binomial mass times a hypergeometric
   mass. At a positive-probability total, the ratio of joint to pooled mass gives
   the conditional hypergeometric law.
4. **Overall error bound:** Each conditional rejection mass is at most `1/20`.
   Multiplying by nonnegative pooled masses and summing gives at most
   `(1/20) * sum(pooled masses) = 1/20`.
5. **Mathlib probability measures:** `StatProof/Fisher.lean` proves that the
   finite binomial formula equals Mathlib's binomial singleton probability, and
   that the finite joint formula equals the product measure's singleton
   probability. The feasible support has probability one. The finite rejection
   sum is therefore the actual probability of the formal rejection event.

The overall proof uses factorization, without dividing by a pooled-event
probability. It works at `p = 0` and `p = 1`, including strata that have zero
probability. It does not assign conditional probabilities to those impossible
events.

## What connects to the executable

Lean proves that its support is exactly the inclusive interval used by Python
and that its rational p-value equals the sum of the qualifying integer weights
divided by the common combinatorial denominator. This is the reference formula
in the [test specification](exact-test-spec.md).

The Python implementation enumerates those weights using a recurrence. Its
agreement with the formal formula is tested but not proved. The declaration
translation and certificate binding are also unfinished. Consequently the CLI
continues to mark application of the theorem to a Python run as unresolved and
issues no formal verification certificate.

A future bridge could prove the recurrence and its implementation correspondence,
or have Lean certify individual computed values against the formal formula. Either
route must bind the precise inputs, definition, theorem, and checked artifacts.

## Reproduce the checks

From the project folder:

```sh
make lean-check
make check
```

`lake build` checks every proof. `tests/lean/FisherExamples.lean` checks concrete
support bounds, tied tails, the exact rejection threshold, degenerate totals,
and applications of the general theorem at arbitrary probabilities and both
endpoints.

`scripts/audit_axioms.lean` collects the transitive dependencies of the main
theorems, including their imported dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted; an unexpected assumption
fails the check. A separate source guard rejects proof placeholders and
additional declared axioms in the project library and Lean examples.

Lean's kernel, the definitions' statistical meaning, and the toolchain/artifact
handling remain trusted components. This audit does not verify the Python parser,
recurrence, reporting code, or real-world sampling assumptions.
