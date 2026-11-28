# Trusted Lean

A certificate proves what the Lean definitions say it proves, so a reviewer must read
those definitions. Lean's kernel checks every proof, so proofs need no review. This page
lists every Lean file of the library with what in it is trusted:

- **Trusted in full**: the semantics' syntax, the meaning of every claim, its premises
  and grade, the contracts, the encoding of a program as data, and the generated
  registry of cited methods and procedures.
- **Definitions trusted**: the objects and procedures claims are stated in, and the
  statement of each checked claim; Lean checks the theorems and each check's soundness.
- **Not trusted**: proofs only.

Beyond these files, Lean's kernel, its JSON printer, the toolchain and the StatClaim
parser and elaborator are trusted; see [certificates](certificates.md).

`scripts/check_trusted_lean.py` writes this page, and `make lean-check` fails when it is
out of date: a change to a trusted file changes its line count here, so it shows in
review. Run `uv run python scripts/check_trusted_lean.py` after a reviewed change.

Trusted in full: 2300 lines. Definitions trusted, with proofs Lean checks: 9286 lines. Proofs only: 2111 lines.

| File | What is trusted | Lines |
| --- | --- | ---: |
| `StatClaim/BinomialModel.lean` | Definitions trusted; Lean checks the proofs | 261 |
| `StatClaim/BinomialMonotone.lean` | Definitions trusted; Lean checks the proofs | 259 |
| `StatClaim/Computation.lean` | Definitions trusted; Lean checks the proofs | 75 |
| `StatClaim/Core/Objects.lean` | Definitions trusted; Lean checks the proofs | 161 |
| `StatClaim/Core/Policy.lean` | Definitions trusted; Lean checks the proofs | 116 |
| `StatClaim/Design.lean` | Definitions trusted; Lean checks the proofs | 41 |
| `StatClaim/FinitePValue.lean` | Definitions trusted; Lean checks the proofs | 89 |
| `StatClaim/Fisher.lean` | Definitions trusted; Lean checks the proofs | 96 |
| `StatClaim/Generated/Methods.lean` | Trusted in full | 551 |
| `StatClaim/Hypergeometric.lean` | Definitions trusted; Lean checks the proofs | 131 |
| `StatClaim/Interface/Families.lean` | Definitions trusted; Lean checks the proofs | 178 |
| `StatClaim/Interface/Outcomes.lean` | Definitions trusted; Lean checks the proofs | 82 |
| `StatClaim/Interface/Premises.lean` | Definitions trusted; Lean checks the proofs | 108 |
| `StatClaim/Modules/Association.lean` | Definitions trusted; Lean checks the proofs | 290 |
| `StatClaim/Modules/AssociationPower.lean` | Definitions trusted; Lean checks the proofs | 162 |
| `StatClaim/Modules/BinomialInterval.lean` | Definitions trusted; Lean checks the proofs | 224 |
| `StatClaim/Modules/BinomialPolynomial.lean` | Definitions trusted; Lean checks the proofs | 78 |
| `StatClaim/Modules/BinomialPower.lean` | Definitions trusted; Lean checks the proofs | 244 |
| `StatClaim/Modules/Bonferroni.lean` | Definitions trusted; Lean checks the proofs | 70 |
| `StatClaim/Modules/Composition.lean` | Definitions trusted; Lean checks the proofs | 114 |
| `StatClaim/Modules/DifferenceTest.lean` | Definitions trusted; Lean checks the proofs | 278 |
| `StatClaim/Modules/FarringtonManning.lean` | Definitions trusted; Lean checks the proofs | 330 |
| `StatClaim/Modules/Fisher.lean` | Definitions trusted; Lean checks the proofs | 81 |
| `StatClaim/Modules/FisherFamily.lean` | Definitions trusted; Lean checks the proofs | 94 |
| `StatClaim/Modules/FisherFamilyN.lean` | Definitions trusted; Lean checks the proofs | 65 |
| `StatClaim/Modules/FisherOneSided.lean` | Definitions trusted; Lean checks the proofs | 339 |
| `StatClaim/Modules/FisherPower.lean` | Definitions trusted; Lean checks the proofs | 253 |
| `StatClaim/Modules/Incidence.lean` | Definitions trusted; Lean checks the proofs | 168 |
| `StatClaim/Modules/LikelihoodRatio.lean` | Definitions trusted; Lean checks the proofs | 173 |
| `StatClaim/Modules/Matched.lean` | Definitions trusted; Lean checks the proofs | 111 |
| `StatClaim/Modules/McNemarAsymptotic.lean` | Definitions trusted; Lean checks the proofs | 107 |
| `StatClaim/Modules/OneSampleBinomial.lean` | Definitions trusted; Lean checks the proofs | 146 |
| `StatClaim/Modules/OneSampleScore.lean` | Definitions trusted; Lean checks the proofs | 70 |
| `StatClaim/Modules/Pearson.lean` | Definitions trusted; Lean checks the proofs | 121 |
| `StatClaim/Modules/PolynomialBound.lean` | Definitions trusted; Lean checks the proofs | 117 |
| `StatClaim/Modules/Randomisation.lean` | Definitions trusted; Lean checks the proofs | 503 |
| `StatClaim/Modules/TwoArmBinomial.lean` | Definitions trusted; Lean checks the proofs | 87 |
| `StatClaim/Modules/TwoStageBinomial.lean` | Definitions trusted; Lean checks the proofs | 225 |
| `StatClaim/Modules/Wald.lean` | Definitions trusted; Lean checks the proofs | 267 |
| `StatClaim/ProductBinomial.lean` | Definitions trusted; Lean checks the proofs | 154 |
| `StatClaim/Semantics/Contracts.lean` | Trusted in full | 335 |
| `StatClaim/Semantics/Encode.lean` | Trusted in full | 476 |
| `StatClaim/Semantics/Exact.lean` | Definitions trusted; Lean checks the proofs | 899 |
| `StatClaim/Semantics/Grades.lean` | Trusted in full | 50 |
| `StatClaim/Semantics/Injective.lean` | Not trusted: Lean checks these proofs |  |
| `StatClaim/Semantics/Intervals.lean` | Definitions trusted; Lean checks the proofs | 307 |
| `StatClaim/Semantics/Meaning.lean` | Trusted in full | 472 |
| `StatClaim/Semantics/Plans.lean` | Definitions trusted; Lean checks the proofs | 698 |
| `StatClaim/Semantics/Results.lean` | Definitions trusted; Lean checks the proofs | 386 |
| `StatClaim/Semantics/Soundness.lean` | Not trusted: Lean checks these proofs |  |
| `StatClaim/Semantics/Syntax.lean` | Trusted in full | 416 |
| `StatClaim/Semantics/Theorems.lean` | Not trusted: Lean checks these proofs |  |
| `StatClaim/WaldBound.lean` | Definitions trusted; Lean checks the proofs | 528 |
