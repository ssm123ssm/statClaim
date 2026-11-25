# The first shared objects in Lean

This is the first implementation of the [core object model](core-object-model.md).
It uses ordinary Lean declarations. A [standalone file language](stat-language.md)
now targets the same semantics and certificate pipeline. Its REPL and LSP remain
later interface experiments.

## Run the example

From the project folder:

```sh
make objects-demo
```

For the primary workflow before observations, run `make design-objects-demo`,
which checks `examples/DesignGuarantee.lean`. It constructs and verifies the design
and leaves out the observation and numerical result entirely. A replayable
certificate of a study comes from `statclaim check` on its `.stat` file.

`make objects-demo` builds the library and checks `examples/FisherObjects.lean`. That example
constructs a model, sampling plan, analysis, general guarantee, observation,
proposed result, and a certificate for that exact value. It also demonstrates the
missing contract when the stopping mechanism's sampling law is unspecified.

The output uses Lean's `#check` to show the actual types of the checked objects
and proofs. It does not serialize a new certificate bundle; `statclaim check` and
`check-certificate` issue and replay those.

## Core objects

`StatClaim/Core/Objects.lean` defines:

| Object | Implemented meaning |
| --- | --- |
| `Model Parameter Outcome` | A probability-law family, an admissible observation set, measurability, and a proof that each law gives that set probability one |
| `SamplingLaw` | A supplied family of probability laws for the observation mechanism |
| `SamplingPlan` | A descriptive stopping category and an optional induced law |
| `StudyDesign model` | The model paired with a declared plan |
| `Compatibility design` | A supplied law, evidence it belongs to this plan, and equality to the model law for every parameter |
| `Hypothesis Parameter` | A predicate on parameters, separate from sampling assumptions |
| `Procedure model` | A statistic, rejection predicate on its output, and a measurable rejection event restricted to admissible outcomes |
| `Analysis model` | A design, hypothesis, and procedure bound together |
| `Observation model` | An outcome with a domain-membership proof |
| `Result analysis` | A proposed value associated with a valid observation |
| `Claim` | A Lean proposition, with its precise context expressed in that proposition |
| `Certificate claim` | Logical evidence establishing precisely that proposition |
| `Assessment claim` | Verified evidence, a checked refutation, unresolved obligations, or an explicit assumption |
| `TypeIGuarantee analysis bound` | Sampling compatibility and a certificate for the corresponding error-bound claim |
| `Module Input` | Versioned metadata, typed requirements, a dependent output type, and a provider requiring evidence of its input contract |

Domains and parameters are represented by types and typed model indices in this
first version. Probability parameters use the closed unit interval. Positive arm
sizes reuse the existing `FixedSampleDesign` record. Names, source locations,
completion metadata, and serialization will be added by the language interfaces.

`Certificate` is a proposition carrying mathematical proof. It is distinct from
the JSON certificate bundles, which record artifacts, versions, assumptions,
and provenance. Naming a claim or marking it assumed provides no proof term.

## Exact claim interface

| Object | Implemented meaning |
| --- | --- |
| `Semantics.Checked Input` | A proposition determined by the input, a hint type, a Boolean check, and a proof that a successful check establishes the proposition |
| `Semantics.ExactModule` | A sampling law, null, rejection event, and Type I check, with optional result, interval, and power checks |
| `Semantics.Program.Hints r` | The evidence data Lean expects for request `r`. `Program.checkAt` validates it before `Program.sound` proves the claim. |
| `Semantics.Request` | The Type I, familywise, observed result, interval, or planning claim to check |
| `Semantics.Program.encode` | The canonical claims, declarations, and certified values used to bind a proof to its inputs |

The Phase 2 spike exercises the interface on one-sided Fisher's Type I claim,
observed result, and minimum sample size. See the [Phase 2 proposal](proposals/lean-semantics-phase2.md).

## Model and hypothesis

`StatClaim/Modules/TwoArmBinomial.lean` defines a full model with parameters
`(p_control, p_treatment)`, each in `[0, 1]`. Its law is the product of the two
binomial measures, and its admissible counts are bounded by the two arm sizes.
The module proves support probability one for every parameter pair.

`equalProportions` is a separate predicate. The `law_under_null` theorem connects
that full model to the common-probability law in the original Fisher proof.
Creating the model does not assume the null is true for the observed data.

## Compose the fixed design and analysis

The following is ordinary Lean code:

```lean
import StatClaim.Modules.Fisher

open StatClaim

def sizes : FixedSampleDesign := ⟨100, 100, by decide, by decide⟩
noncomputable def model := Modules.TwoArmBinomial.model sizes
noncomputable def design := Core.StudyDesign.fixed model
def level : SignificanceLevel := ⟨1 / 40, by norm_num, by norm_num⟩
noncomputable def analysis := Modules.Fisher.analysis sizes design level

noncomputable def guarantee : Core.TypeIGuarantee analysis (level.value : ℝ) :=
  (Modules.Fisher.module sizes level).provide design ⟨Core.Compatibility.fixed model⟩
```

`StudyDesign.fixed` explicitly declares that the plan follows the model's law.
The associated compatibility object establishes equality of those declared laws.
Whether a real study follows that declared mechanism remains an assumption.

The Fisher provider requires compatibility before returning a guarantee. Its
`typeI_statement` proof rewrites the supplied law using that compatibility,
restricts the parameters under the null, proves equality of the rejection events,
and applies the generalized `fisher_typeI_error_le_alpha` theorem. It does not reprove
Fisher's mathematical bound or assume a new statistical result.

This guarantee can be constructed before observations exist. The level is an
exact rational in `[0,1]`; the real bound is written `(level.value : ℝ)` because
Type I error is a real probability. Omitting the level argument keeps the default
5% procedure and provider. `examples/ConfigurableAlpha.lean` is a runnable example.

The module now also composes with Bonferroni to establish familywise control.
See [multiple testing](multiple-testing.md) and run `make composition-demo`.
The generic composition module supports any finite family; the CLI adapter
supports two or more Fisher analyses and records their marginal-law contracts.

## Propose and check an observed result

The model module provides a domain-checked constructor:

```lean
def observation : Core.Observation model :=
  Modules.TwoArmBinomial.observe sizes 10 25 (by decide) (by decide)
```

The proof arguments check the count bounds. An out-of-range count cannot be
constructed with `by decide`. These are source-level checks, not empirical
evidence that the counts came from the declared sampling procedure.

`Core.Result` stores a proposed output without granting its correctness.
`Result.exactClaim` states equality to the procedure's formal evaluation. The
worked example uses the existing cross-product bridge and `decide +kernel` to
prove that claim for the exact p-value
`19912805355158606332329/2341699062001756564467919`.

A certificate for this point value cannot be supplied where a Type I error
certificate is required. Changing the proposed value or model changes the
relevant types and claims and requires matching evidence.

## An unresolved stopping mechanism

`StudyDesign.unresolvedAdaptive model` declares data-dependent stopping with no
induced sampling law. It drops the fixed-plan law rather than inheriting it.
The Fisher provider's compatibility requirement cannot be discharged from the
fixed design's evidence.

`adaptive_requirement_missing` proves only the absence of that supplied contract.
It does not prove that the actual procedure's error rate exceeds `0.05`.
`Modules.Fisher.adaptiveObligations` records the missing law and justification.

Sampling categories are descriptive metadata in this minimal representation.
The mathematical contract is the explicitly supplied law and its agreement with
the model. We have not implemented an operational semantics deriving sampling
laws from arbitrary stopping programs. A future justified adaptive mechanism may
provide an appropriate law and further proofs; it must not acquire them merely
by changing a category label.

Compatibility currently requires agreement for every parameter. Some future
contracts may need agreement only under a hypothesis, or a different form of
algorithm compatibility. That is a deliberate point to evaluate with the second
composition example rather than generalizing it speculatively now.

## Checks and current boundaries

`make lean-check` runs the original examples, the worked object example, and
`tests/lean/CoreObjects.lean`. The object tests include rejection of stale value
certificates, wrong claim kinds, assumption-to-proof conversion, invalid counts,
incompatible plan evidence, and a mismatched sampling law. A procedure with
pair-valued output also checks that the core is not restricted to Fisher's
rational-valued statistic.

The transitive dependency audit includes the new adapter theorems and allows
only the standard logical assumptions. No statistical proof placeholders or
additional project assumptions have been introduced into those proofs.

The module type is a typed provider, not a dynamic plugin loader. This version
does not dynamically load third-party modules or provide general proof automation.
The standalone file parser and domain diagnostics now operate against these
concrete definitions; the LSP and VS Code extension provide interactive guidance.
