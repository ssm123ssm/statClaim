# Study planning and Bayesian designs

**Roadmap proposal; not implemented in the current preview.** The goal is a
consistent way to plan a study, understand its expected performance and retain
the justification with the design. Bayesian and adaptive designs are core
targets, reflecting StatProof's original motivation.

Start with the [proposed Fisher planning example](proposals/planning-example.md)
for concrete syntax, numerical reference values and expected results.

## One planning workflow

1. Declare the model, question, analysis and complete sampling/decision policy.
2. State the effect or precision of interest and required planning assumptions.
3. Choose a target, such as power, assurance or interval precision, plus any
   applicable error constraints and sample-size/budget limits.
4. Evaluate a proposed design or search a declared range of candidate designs.
5. Return the recommended design, achieved targets, assumptions and evidence.

Be opinionated about the workflow: module authors supply compatible planning
adapters, documented presets and useful missing-input guidance. Show defaults
and allow overrides. Ask for scientific inputs such as a meaningful effect and
baseline rate; do not silently infer them from a test name.

## Proposed object and claim families

These are conceptual classifications, not committed API names or constructors.
The live [catalogue](catalogue.md) lists only implemented objects.

| Family | What it must describe |
| --- | --- |
| Planning specification | Candidate designs, allocation, parameter scenarios or domain, targets and search limits. |
| Power/error claim | A success or rejection event, sampling law, and a pointwise or uniform probability bound over an explicit parameter domain. |
| Sample-size claim | A particular design meets its targets under stated assumptions; minimality needs a separate claim over the declared search space. |
| Bayesian specification | Likelihood, prior, requirements for a well-defined posterior, computation method and decision or utility rule. |
| Assurance/precision claim | A prespecified success/precision criterion and its predictive probability, with any design prior explicit and distinguished from the analysis prior. |
| Planning result | Recommended design, achieved criteria, unmet requirements, computational limits and evidence provenance. |

Power needs an alternative and nuisance-parameter assumptions, not just alpha
and a desired percentage. Assurance averages the probability of meeting a
criterion over a declared design distribution. Posterior probability, assurance
and repeated-sampling power/error rates must remain distinct quantities.

## Bayesian and adaptive compatibility

Check that the prior and likelihood share the intended parameter space, that
the posterior is well defined, and that the decision rule matches the model.
Distinguish an invalid model from an unsupported inference backend; lack of
conjugacy alone is not a model incompatibility. Represent the full
history-dependent allocation, interim analyses, stopping and final decision.
Bind planning results to that complete specification; edits make them stale.

Allow Bayesian success, estimation and utility targets without requiring every
analysis to be framed as a frequentist test. When a user requests Type I error
or power, assess the complete policy under the specified sampling laws. A
posterior threshold alone does not establish those operating characteristics.
For adaptive designs report expected sample size under stated scenarios and a
maximum/cap separately. Composition rules must justify the resulting joint
claim, including relevant dependencies and multiplicity.

## Evidence and first milestones

Keep formal proofs, certified numerical bounds, approximations and simulation
estimates identifiable. Simulation reports need scenarios, run counts, seeds,
Monte Carlo uncertainty and a validation plan for a design selected by search.
Checking a finite scenario grid must not become a claim over an entire domain.
Report infeasible or unsupported targets explicitly. Do not assume power is
monotone in sample size without justification, especially for discrete/adaptive
designs.

1. Define shared planning contracts and claims; add exact power at specified
   alternatives for the existing Fisher model and a bounded sample-size search.
2. Add a beta-binomial Bayesian example with a declared posterior decision rule,
   predictive planning criterion and sensitivity to the prior.
3. Represent adaptive policies explicitly; support reproducible simulation of
   their operating characteristics, then add checked bounds/proofs where feasible.
4. Extend planning adapters and justified composition rules with each new method.

Initial validation should include independent small-case enumeration, unattainable
targets, mismatched assumptions, search/minimality distinctions and stale results.
Module authors should supply planning support with a new design/test when possible,
or expose a specific unsupported requirement instead of a generic recommendation.

## Background

- [Bayesian assurance and sample-size planning](https://pmc.ncbi.nlm.nih.gov/articles/PMC9325402/)
- [Bayesian trial design and operating characteristics](https://www.fda.gov/regulatory-information/search-fda-guidance-documents/guidance-use-bayesian-statistics-medical-device-clinical-trials)
- [Adaptive design evaluation](https://www.fda.gov/regulatory-information/search-fda-guidance-documents/adaptive-design-clinical-trials-drugs-and-biologics-guidance-industry)
