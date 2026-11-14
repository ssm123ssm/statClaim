# A formal checker for statistical designs

Project concept • 14 November 2026 • Updated project direction

## Goal
Build an open-source, modular system in which researchers describe a statistical model or study design using familiar statistical concepts. The system checks explicit constraints and compatibility requirements and reports which statistical guarantees have been established under which assumptions.

The working analogy is a “Lean for practical statistics.” Lean’s kernel checks proofs through type checking; this project would provide a statistical language and reusable modules above a formal verification backend. The agreed direction is a standalone application backed by Lean: a statistical interface above Lean’s existing proof-checking kernel. Building a new proof checker is outside the initial scope.

## Initial scope: one fixed-sample binary-outcome design
Start with a two-arm study modeled as two independent binomial samples, with positive sample sizes fixed before observing outcomes and a null hypothesis of equal proportions. This replaces the state-space model as the first implementation target; adaptive sampling remains a later application.

Choose one precisely specified exact test and prove that its rejection probability is at most 0.05 for every common success probability under the null, under the declared sampling assumptions. Selection and formalization of the exact test remain implementation tasks. Do not begin with an approximate normal test or attempt to certify power, coverage, and adaptive stopping simultaneously.

The prototype should accept the supported design and report its guarantee and assumptions. If data-dependent stopping is introduced, it should report that the fixed-sample theorem does not establish the modified procedure’s guarantee. This is an unresolved justification, not necessarily evidence of inflated error.

## Architecture and extension
The application provides familiar statistical declarations and readable diagnostics. Modules translate those declarations into formal definitions and proof obligations; Lean checks the resulting proofs. The correspondence between user declarations, formal statements, and reports must also be validated.

Keep the same Lean kernel as new designs are added. Each module contributes definitions, assumptions, proofs, and automation. Extending the statistical library and establishing compatibility between modules are the main tasks; a separate proof checker is not required for each design. Automation will vary, and some new designs will need manual proofs.

This avoids creating a new foundational prover, but formal probability, exact calculations, and the connection between mathematical specifications and executable implementations still require substantial work.

## Later application: state-space models and adaptive sampling
After demonstrating the first design end to end, extend to the state-space model component of the adaptive sampling framework before attempting its full set of components.

A model declaration should specify the latent state and its support, initial distribution, transition model, observation model, parameters, assumptions, and required computational operations.

Candidate checks:
- Dimensions, variable domains, and distribution parameters are compatible.
- Transitions preserve declared constraints, such as prevalence remaining between zero and one.
- Observation supports agree with the data: a binomial count is an integer between zero and the declared sample size.
- Dependencies and conditional-independence assumptions are explicit and consistent with the declared factorization.
- Model operations meet downstream algorithm requirements. A bootstrap particle filter, for example, requires initial-state sampling, transition sampling, and evaluation of the observation likelihood conditional on the state. It need not have an analytically available one-step predictive likelihood.

Example: adding unrestricted Gaussian noise directly to prevalence cannot guarantee preservation of its bounds. A bounded construction, a transformed state, or a suitable proof would be required.

## Verification approach
Use ordinary types for basic structural checks and richer constraints or proof obligations for mathematical properties. Supported modules should automate routine obligations using reusable results.

Distinguish four outcomes: verified; demonstrated violation; unresolved obligation; explicitly assumed. Failure of automation is not proof that a claim is false. General consistency and arbitrary statistical correctness cannot always be decided automatically.

Separate mathematical model properties, algorithm compatibility, numerical implementation correctness, and empirical adequacy. Verifying one does not establish the others.

## Certificates
Issue a property-specific verification report or certificate identifying:
- The exact design, module versions, and verification backend.
- The properties established and their precise scope.
- Assumptions, trusted components, and outstanding obligations.
- Whether evidence consists of formal proofs, exact computation, or simulation.

A certificate should mean: “These specified properties follow from these explicit assumptions.” It must not imply that real-world assumptions are true or that a study is universally valid. Simulation evidence should state tested scenarios and Monte Carlo uncertainty.

## Community modules and later extension
Contributors could add statistical definitions, design components, compatibility contracts, proofs, and automation. A common verification backend would check submitted proofs; module review would also examine whether formal statements capture the intended statistical meaning.

Following the initial two-arm module, contributors could extend the supported tests, assignment schemes, and outcome models. Further guarantees could include power at specified alternatives and interval coverage. Exact and asymptotic guarantees must be distinguished.

Combining individually verified modules requires checking their joint contracts. Adding interim looks or data-dependent stopping requires justification that the intended guarantees survive the change; it does not automatically invalidate every procedure.

## Related work identified
- **StatWhy:** formal verification of annotated hypothesis-testing programs using Why3 and automated provers. It checks use of test routines against their contracts, while trusting those routines and assuming stated population requirements. It is a close precedent, though its mechanism differs from Lean’s kernel type checking. [Paper](https://arxiv.org/abs/2405.17492) · [Code](https://github.com/fm4stats/statwhy)
- **DeclareDesign:** modular declaration of research designs and simulation-based diagnosis of properties such as bias, power, and coverage. It does not provide the same kind of deductive guarantee. [Project](https://declaredesign.org/)

These establish substantial prior work. Novelty of the proposed combination—an accessible statistical language, composable community modules, and explicit proof-backed certificates—remains to be assessed through a fuller review.

## Proposed first milestone
Deliver one supported design, one formally proved Type I error guarantee, and one unsupported modification with a clear explanation.

The demonstration should show the declared fixed-sample design, its Lean-checked guarantee, and a concise certificate listing assumptions and trusted components. Adding data-dependent stopping should expose the missing justification rather than silently reuse the fixed-sample certificate.

Success means a complete path from a statistical declaration to a verified claim and an understandable report. Use this experience to refine the module interface before expanding to state-space models and adaptive sampling.
