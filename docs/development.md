# Development scope and next steps

The first module concerns two independent binomial samples with positive sample
sizes fixed before outcomes are observed. The specified test is the
nonrandomized, probability-ordered, two-sided Fisher exact test, rejecting at
`p_value <= 1/20`. Its [specification](exact-test-spec.md) defines the details.

## Completed

- Reproducible Python and Lean / Mathlib environments, local Git, and CI checks.
- An exact Fisher calculation using integer combinatorics and rational arithmetic.
- A CLI taking a design declaration and observed arm success counts, with JSON
  results that separate the numerical decision from formal-verification status.
- Exhaustive small-table checks, stored R reference fixtures, and an optional
  live R comparison script.
- The Lean theorem `StatProof.probabilityOrdered_rejection_mass_le`: a generic
  bound on rejected mass for finite, nonnegative rational masses with inclusive
  probability ordering and ties.
- Hypergeometric support and positive denominator, Vandermonde normalization,
  integer probability ordering, and the conditional rejection bound.
- A normalized finite independent-binomial model, its partition by pooled totals,
  and the conditional hypergeometric law at positive-probability totals.
- `StatProof.fisher_typeI_error_le`: the uniform Type I error bound against the
  product of Mathlib's binomial measures for every common `p` in `[0, 1]`.
- Concrete Lean examples and a transitive theorem dependency audit allowing only
  the standard logical axioms. The proof includes both null endpoints.
- An unsupported stopping example that exposes missing justification and withholds
  a procedure-level decision, while allowing the fixed-margin statistic to be shown.

## Next formal milestone

1. Establish correspondence with the executable calculation, or certify individual
   computed results. The current Python recurrence is tested but not formally verified.
2. Validate the declaration parser and its mapping to the theorem's assumptions.
3. Bind property-specific certificates to checked theorems, actual inputs, exact
   module/backend versions, assumptions, and trusted components. Subprocess
   success alone must never imply that the reported statistical claim was proved.

The final Lean theorem now establishes the mathematical guarantee for the formal
independent-binomial model. It does not certify a Python execution. Reports
reference the library theorem but keep its application to the run marked
`unresolved_obligation`, with `certificate_issued: false`, `backend_invoked:
false`, and empty formally established properties for that run. Their numerical
evidence is explicitly labeled `exact_computation`.

The [proof walkthrough](formal-proof.md) records the theorem's precise scope.

## Scope boundaries

Reports must distinguish verified properties, demonstrated violations, unresolved
obligations, and explicit assumptions. Sampling assumptions are requirements,
not statements that the real study satisfies them. Data-dependent stopping needs
additional justification; it does not by itself demonstrate inflated error.

Approximate tests, adaptive-design proofs, power, confidence intervals, state-space
models, a graphical interface, and community-module infrastructure remain later
work. The current executable focuses on one precisely specified test.

## Tooling references

- [Lean installation and Mathlib project setup](https://lean-lang.org/install/manual/).
- [Pinned Mathlib release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0).
- [Mathlib cache documentation](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Cache/README.md).
- [R's Fisher test definition](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/fisher.test.html).

The original project brief is retained unchanged.
