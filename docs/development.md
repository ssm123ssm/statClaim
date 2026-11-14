# Development scope and next steps

The first module concerns two independent binomial samples with positive sample
sizes fixed before outcomes are observed. Under equal success probabilities,
the eventual test must have rejection probability at most `1/20` for every common
probability in `[0, 1]`. Approximate tests, adaptive designs, power, and coverage
are outside this first proof.

## Boundaries established by the scaffold

Python parses a small TOML vocabulary and reports unresolved work. Lean contains
foundational declarations, without a binomial model or test. These definitions
have not yet been connected: a successful Python check or Lean build establishes
neither statistical validity nor correctness of the translation.

Future reports must distinguish verified properties, demonstrated violations,
unresolved obligations, and explicit assumptions. The initial CLI emits only
unresolved obligations. Required assumptions are listed as requirements, not
claims about a real study. Modifying the stopping rule exposes missing
justification; it does not by itself demonstrate inflated error.

## Next implementation work

1. Select and document one exact test, including its tail convention, rejection
   threshold, handling of ties, and whether randomization is used.
2. Formalize the sampling model, null, and rejection event in Lean / Mathlib.
3. Prove the uniform Type I error bound under explicit sampling assumptions.
4. Implement and validate the declaration-to-Lean translation and ensure reports
   refer to the checked theorem, precise inputs, and exact module/backend versions.
5. Add a property-specific certificate with assumptions, trusted components, and
   outstanding obligations. Never infer successful verification from subprocess
   success alone or use a proof containing placeholders.
6. Demonstrate the unsupported stopping modification end to end.

The source-token guard is a basic development safeguard, not a complete check of
Lean's trusted assumptions. A future proof pipeline must audit theorem axioms and
the correspondence between the formal theorem and the reported claim.

## Tooling references

- [Lean installation and Mathlib project setup](https://lean-lang.org/install/manual/).
- [Pinned Mathlib release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0).
- [Mathlib cache documentation](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Cache/README.md).

The original project brief is retained unchanged.
