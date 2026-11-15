# Scope and trust

The preview supports fixed samples from two independent binomial arms, an
equality null, and the specified two-sided Fisher test using exact rational
arithmetic. Alpha is explicit. The file-language Bonferroni adapter currently
handles two Fisher endpoints; the Lean composition library is more general.

Difference and inequality nulls can be described. Fisher rejects them with
contract guidance. Adaptive sampling can be described, but its current Type I
error obligation is unresolved. These are useful diagnostics, not new proofs.

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
