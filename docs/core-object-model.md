# Core objects and parallel language prototypes

Status: the shared Lean objects, Fisher and Bonferroni providers, and standalone
file language with first-class claims/results and backend-free compilation are
implemented. A stdio LSP and minimal VS Code integration provide editor guidance;
interactive REPL sessions remain planned. See the [file-language guide](stat-language.md)
and [editor guide](editor.md).
This document remains the semantic design and comparison plan; the
[Lean object guide](lean-objects.md) describes the implemented API and examples.

## Working direction

Define the statistical objects and their meaning first. Represent them in a
shared Lean library, and express the Fisher example through that representation.
Use the standalone statistical language as the primary researcher interface,
with a small, consistent constructor grammar. Preserve the Lean and TOML routes;
direct Lean programming primarily serves module authors and advanced work.

The two routes share mathematical definitions, module contracts, proof results,
and certificate requirements. Their differences are syntax, elaboration, user
interaction, and editor integration. New mathematical results are proved once in
the shared Lean library.

## Proposed objects

These are semantic concepts. This list does not require one implementation class
for every row, and the names remain provisional.

| Object | Meaning | First Fisher instance |
| --- | --- | --- |
| Domain and parameter | A named unknown quantity and its allowed values; distinct from observed data or an estimate | Success probabilities `p_control`, `p_treatment` in `[0, 1]`; positive integer arm sizes |
| Model | Random quantities, their supports, probability laws, and joint dependence structure | Two binomial counts with their joint law given by the product of their marginal laws |
| Sampling plan | How observations are acquired and when sampling ends | Two positive sizes fixed before observing outcomes |
| Study design | A model paired with a sampling plan, with their compatibility obligations | The fixed-sample two-arm binomial design |
| Hypothesis | A predicate restricting the model parameters for a particular claim | `p_control = p_treatment` |
| Procedure | A mathematically specified operation, including its output and decision rule | Probability-ordered, two-sided Fisher p-value; reject at `p <= 1/20` |
| Analysis | A binding of a study design, hypothesis, procedure, and settings | Fisher applied to the declared design and equal-proportions null |
| Observation | Data bound to the declared random quantities and checked against their domains | Control count `10/100`, treatment count `25/100` |
| Claim | A precise proposition about a design, analysis, or computed result, with its context and quantifiers | Uniform Type I error at most `1/20`; separately, the exact p-value of the observed table |
| Evidence and certificate | Evidence for a named claim, together with assumptions, proof dependencies, versions, and provenance | A reusable general theorem and a checked per-result proof, recorded as separate properties in a bundle |
| Module | Typed constructors and operations, requirements, supported claims, formal definitions/proofs, automation, and documentation | Binomial modeling, fixed sampling, and Fisher inference modules |

An executable implementation is associated with a procedure but is not its
mathematical definition. The current Python recurrence proposes a result; Lean
checks that individual result against the formal procedure. A proof about every
execution of that implementation would be a different claim.

## Semantic boundaries

### Models, plans, and hypotheses

A model is a family of probability laws. Its definition may explicitly use a
product measure. The statement that real data follow that law remains a sampling
assumption. A sampling plan declares a data-collection mechanism; changing that
mechanism may require changing or rejustifying the probability model.

The null hypothesis is a restriction under which a guarantee is evaluated. A
Type I error theorem does not establish that the null is true for the supplied
observations. Parameter restrictions, sampling assumptions, and tested hypotheses
must remain distinguishable in the object model and reports.

### Claims and evidence

Each claim records its subject, mathematical statement, quantifiers, assumptions,
and dependencies. A claim about an analysis before observations are available is
different from a claim about the exact value of one computed result.

Maintain the existing distinction between verified, demonstrated violation,
unresolved obligation, and explicitly assumed. Also distinguish evidence kinds:
formal proof, exact computation, and simulation. An assumed premise is not a
proof artifact, and a computed value alone is not a proof of an error bound.

Existing certificates aggregate several named claims. The new objects should
make those claims individually addressable and record which context each uses.
Certificate references must resolve to checked propositions and matching module
definitions; a string identifier or a `verified` boolean is insufficient.

### Composition

To compose components, discharge the receiving component's requirements using
the available definitions, explicit assumptions, and checked claims. Record the
resulting dependencies and any assumptions that remain.

For example, the Fisher guarantee requires the declared binomial sampling law and
fixed-sample setting. A separate result about an outcome model does not discharge
the requirement about stopping. Adding data-dependent stopping exposes an
unresolved compatibility obligation until suitable additional justification is
available. It does not by itself demonstrate inflated error.

General consistency and equivalence of arbitrary statistical models cannot be
promised as automatic checks. The initial implementation should handle explicit,
supported contracts and report other obligations faithfully.

### Extension

Modules ordinarily extend the library vocabulary through typed constructors,
operations, and claims. The base grammar for declarations, imports, assumptions,
calculations, and verification should stay small. Avoid requiring every test
module to define a separate grammar or a separate inference engine.

New modules may introduce genuinely new mathematical definitions and manual
proofs. The current Fisher theorem must not be reused merely because a new module
has a similar-looking interface.

## The two representations

### Lean-facing representation

Use shared Lean structures and definitions for the core objects. Module authors
provide formal contracts and proofs. Researchers initially use documented
constructors and, where useful, a small amount of statistical syntax layered on
them. Preserve source information and produce statistical diagnostics at the
declaration that creates the obligation.

The first task is to connect the existing `FixedSampleDesign`, hypergeometric
p-value, product-binomial null law, and Fisher theorem to these objects, without
reproving Fisher solely to accommodate a new record layout.

### Standalone statistical language

Implement a small parser and typed representation for the same objects. Lower
those declarations into the shared Lean definitions and verification requests.
Keep source locations so diagnostics can refer to the user's statistical code.

Start with file execution and a limited interactive session. Reuse that language
analysis for completion, hints, and a later LSP. Fast structural checks should
work on incomplete documents; expensive verification should be explicit. Changing
a declaration must invalidate dependent proof status and cached results.

The lowering and report binding are trust boundaries to examine during the
comparison. Generated statements, normalized inputs, and precise assumptions
must remain available for review and replay.

## Fisher acceptance cases

Both representations should express and check these cases:

1. Declare the same positive fixed arm sizes and independent binomial model.
2. State an equal-proportions null without asserting its truth for observed data.
3. Bind the same probability-ordered, two-sided Fisher procedure at `1/20`.
4. Request the uniform error-bound claim before supplying observations.
5. Supply `10/100` and `25/100` and obtain the same exact p-value and decision.
6. Check that numerical result against the formal definition and issue a scoped
   certificate with the same mathematical claims and assumptions.
7. Reject invalid counts with a useful source location.
8. Modify the stopping plan and expose the missing justification without issuing
   the fixed-sample guarantee for the modified procedure.
9. Edit a relevant declaration and invalidate dependent evidence.

Compare the constructed objects, propositions, assumptions, and proof scope.
Source text, names, and certificate content hashes may differ between routes.
Structural agreement is sufficient for supported canonical objects; other
semantic equivalences may require an explicit theorem rather than automatic
normalization.

## Implementation sequence and decision point

1. Review this object model, especially the boundaries among model, sampling
   plan, hypothesis, procedure, and claim.
2. Implement the minimal Lean core and a Fisher example using those objects.
3. Build the standalone file-language prototype while the Lean interface is
   still small. Implement both against the same acceptance cases.
4. Add enough interactive guidance to compare incomplete input, completion,
   diagnostics, and proof inspection. Avoid two full IDE implementations at this
   stage.
5. Exercise a second composition pattern before choosing a primary route.
   Select that example after Fisher; keep new statistical proof scope explicit.
6. Review the results and select a primary interface. Retain the shared semantic
   library and useful interoperability regardless of the choice.

Compare researcher learning effort, diagnostic quality, manual-proof escape
routes, module-author effort, translation trust, verification performance, IDE
integration, installation, and maintenance cost. Fisher alone is a useful first
test but is insufficient evidence for every future module's language needs.

The implementation completes step 2 and now exercises step 5 with a generic
Bonferroni provider and a two-Fisher adapter. Alpha is explicit, and the second
composition requires marginal-law evidence and an adequate sum of error budgets.
See [multiple testing](multiple-testing.md).
Step 3 is now implemented as the small `.stat` file language, with typed objects,
source maps, module schemas, canonical lowering, and file execution through the
existing certificate pipeline. The Fisher acceptance cases and the Bonferroni
composition are covered by examples and cross-interface integration tests.
The language now also supports named claims and first-class calculation and
verification results, with a backend-free compiler that inspects known
requirements. Explicit execution invokes Python calculations or generated Lean
proofs; aliases and lists reuse existing results. The next step is interactive
guidance and completion using this same compiler; the initial stdio LSP and
VS Code extension now implement these features. The statistical language is the
primary researcher interface, with Lean and TOML retained. No REPL has been
implemented yet.
