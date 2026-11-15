# Scope and trust

The preview supports fixed samples from two independent binomial arms, an
equality null, and the specified two-sided Fisher test using exact rational
arithmetic. Alpha is explicit. Bonferroni composition handles two to twenty
Fisher endpoints with any allocation that sums to at most the family level.

Planning adds exact Fisher power at one declared point, target checks and a
bounded equal-arm sample-size search. A selected size can be certified as
sufficient, or as the smallest sufficient size within the declared range. A single-arm two-stage binomial policy with an interim stop is supported
with count or Beta-posterior rules: its Type I error and power are checked for
the complete policy. The one-sided exact binomial test is supported for a single
arm, for planning and for analysing an observed count. Exact confidence
intervals for one proportion have checked coverage for every true rate. Error bounds for that test and for count thresholds cover every rate at or
below the null rate; posterior thresholds cover the declared null rate only. The posterior rule's closed form
is a definition; its identity with the Beta integral is not proved in Lean.

Difference and inequality nulls can be described. Fisher rejects them with
contract guidance. Declaring a Fisher analysis `adaptive` still leaves its Type I
error obligation unresolved; use a complete policy instead. These are useful diagnostics, not new proofs.

The design theorem concerns repeated-sampling Type I error. A result certificate
checks the observed calculation and decision. These are different claims.
Neither certifies recruitment, data quality, model fit or a causal conclusion.
Independence, the sampling law and other declared assumptions must match reality.

`calculate` produces a calculation, not proof evidence. `compile` and the LSP
inspect requirements without verification. `verify` creates evidence only when
its backend succeeds. Missing or failed verification leaves evidence absent.

Certificates record source/toolchain hashes and can be replayed. Trust includes
the Lean kernel and declared axioms, the pinned dependencies, and the translation
from statistical intent to the formal statement. CI audits Lean sources and
axioms and tests modified certificates. Read the statement and assumptions;
passing tests alone cannot establish that a new method models the intended study.

See [formal proof](formal-proof.md) and [certificates](certificates.md).
