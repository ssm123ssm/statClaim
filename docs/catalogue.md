# Object and module catalogue

Generated from the language registries. Update with `uv run python scripts/update_catalogue.py`; CI checks for drift.

All APIs are preview APIs. Object availability does not imply a proof adapter. See [scope](scope.md) for supported guarantees.

## Core statistical objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Model | Sampling model and arm sizes. | `n_control: integer`, `n_treatment: integer` |
| StudyDesign | Model with a stopping rule. | `model: Model`, `stopping: string` |
| Hypothesis | A null restriction, not an assertion of truth. | `model: Model`, `predicate: string`, `value: exact number`, `statement: string` |
| Analysis | Design, compatible null and exact alpha. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number` |
| Observation | Observed counts tied to an analysis. | `analysis: Analysis`, `control_successes: integer`, `treatment_successes: integer` |
| Family | Analyses, family alpha and declared joint law. | `analyses: list`, `alpha: exact number`, `joint_law: string` |

## Claims and results

| Object | Meaning | Public fields |
| --- | --- | --- |
| Claim | Requested typeI, result or familywise proposition. | `kind: string`, `subject: object` |
| VerificationResult | Explicit verification outcome; optional evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `evidence: Option[Evidence]` |
| CalculationResult | Calculation outcome; no proof evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `calculation: Option[CalculationDetails]`, `decision: Option[string]` |

## Evidence and inspection

| Object | Meaning | Public fields |
| --- | --- | --- |
| Evidence | Checked properties, assumptions and certificate. | `claim: Claim`, `certificate: CertificateReference`, `established_properties: list`, `required_assumptions: list` |
| CertificateReference | Certificate identity, path and hash. | `certificate_id: string`, `file: string`, `directory: string`, `sha256: string` |
| CalculationDetails | Exact p-value, alpha and test details. | `p_value: exact number`, `alpha: exact number`, `observed_table_probability: exact number`, `p_value_le_alpha: boolean`, `test: string`, `test_version: string` |
| Diagnostic | A diagnostic code, severity and message. | `code: string`, `message: string`, `severity: string` |

Claim constructors return `TypeIClaim`, `ResultClaim` or `FamilywiseClaim`, all represented by Claim. Exact numbers, strings, booleans and lists are value types. Optional evidence stays optional through field access.

## Modules

`use` imports built-in constructors; it does not load arbitrary files or plugins.

### `models.two_arm_binomial` — Models and hypotheses

Two independent binomial arms; equality, difference and inequality null descriptions. Only equality has a current Fisher proof adapter.

- `two_arm_binomial(n_control, n_treatment) -> Model`
- `equal_proportions(model) -> Hypothesis`
- `proportion_difference(model, value) -> Hypothesis`
- `proportion_difference_at_most(model, value) -> Hypothesis`

### `sampling` — Study designs

Fixed sampling is supported. Adaptive sampling is descriptive; its current Type I error requirement remains unresolved.

- `fixed(model) -> StudyDesign`
- `adaptive(model) -> StudyDesign`

### `tests.fisher` — Analyses and claims

Two-sided Fisher calculation and Lean-backed result/Type I claims for the equality null with fixed sampling.

- `fisher(design, null, alpha) -> Analysis`
  Required null: p_treatment = p_control (equal arm success probabilities); same model required.
- `observe(analysis, control_successes, treatment_successes) -> Observation`
- `typeI(analysis) -> TypeIClaim`
- `result(observation) -> ResultClaim`

### `multiplicity.bonferroni` — Multiplicity and composition

File adapter for two Fisher endpoints with an explicit supported joint law. The Lean composition library is more general.

- `bonferroni(analyses, alpha, joint_law) -> Family`
- `familywise(family) -> FamilywiseClaim`

## Built-in operations

- `verify(claim) -> VerificationResult`
- `calculate(claim) -> CalculationResult`

Verification and calculation run only on explicit execution; the editor plans them. Compilation cannot create evidence.

## Lean library concepts

The formal library also defines parameter domains, procedures, guarantees and composition rules. These are not all standalone `.stat` constructors yet. See [core object model](core-object-model.md) and [Lean objects](lean-objects.md).

For typed parameters and contracts in machine-readable form, run `statproof catalogue --json`. See [adding modules](adding-modules.md).
