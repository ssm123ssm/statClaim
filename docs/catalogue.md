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
| OneArmModel | One arm with a fixed sample size. | `n: integer` |
| OneSampleAnalysis | One-sided exact binomial test with its null rate and alpha. | `model: OneArmModel`, `null_rate: exact number`, `alpha: exact number` |
| OneSampleObservation | Observed responses for a one-sample test. | `analysis: OneSampleAnalysis`, `responses: integer` |

## Planning objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Rates | Planning point for two arms; an input, not a fact. | `p_control: exact number`, `p_treatment: exact number` |
| Rate | Planning point for a single response rate. | `value: exact number` |
| PowerTarget | Required power at a point and a Type I bound. | `at: PlanningPoint`, `minimum: exact number`, `maximum_typeI: exact number` |
| Feasibility | One analysis assessed against one target. | `analysis: Analysis`, `target: PowerTarget` |
| Candidates | Finite equal-arm design space for a search. | `analysis: Analysis`, `min_per_arm: integer`, `max_per_arm: integer` |
| Sizing | Candidates searched for a design meeting a target. | `candidates: Candidates`, `target: PowerTarget` |
| OneArmCandidates | Sample sizes searched for a one-sample test. | `analysis: OneSampleAnalysis`, `min_n: integer`, `max_n: integer` |

## Adaptive design objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| TwoStageModel | Stage sizes of a single-arm design. | `n_stage1: integer`, `n_stage2: integer` |
| Prior | Beta prior with positive integer parameters. | `a: integer`, `b: integer` |
| Rule | Interim continuation and final decision rule. | `kind: string` |
| TwoStageAnalysis | Complete policy: stages, rule and the null response rate. | `design: TwoStageModel`, `rule: Rule`, `null_rate: exact number` |

## Claims and results

| Object | Meaning | Public fields |
| --- | --- | --- |
| Claim | Requested typeI, result, familywise or planning proposition. | `kind: string`, `subject: object` |
| VerificationResult | Explicit verification outcome; optional evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `evidence: Option[Evidence]` |
| CalculationResult | Calculation outcome; no proof evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `calculation: Option[CalculationDetails]`, `decision: Option[string]` |

## Evidence and inspection

| Object | Meaning | Public fields |
| --- | --- | --- |
| Evidence | Checked properties, assumptions and certificate. | `claim: Claim`, `certificate: CertificateReference`, `established_properties: list`, `required_assumptions: list` |
| CertificateReference | Certificate identity, path and hash. | `certificate_id: string`, `file: string`, `directory: string`, `sha256: string` |
| CalculationDetails | Exact p-value, alpha and test details. | `p_value: exact number`, `alpha: exact number`, `observed_table_probability: exact number`, `p_value_le_alpha: boolean`, `test: string`, `test_version: string` |
| PlanningDetails | Calculated sizes, power and target components; not proof evidence. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `power: Option[exact number]`, `power_target_met: boolean`, `typeI_bound: Option[exact number]`, `typeI_target_met: Option[boolean]`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| OneSampleDetails | Calculated critical value, error and power of a one-sample test. | `n: Option[integer]`, `critical_value: Option[integer]`, `typeI: Option[exact number]`, `typeI_target_met: Option[boolean]`, `power: Option[exact number]`, `power_target_met: boolean`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| OneSampleResultDetails | Exact one-sided p-value, critical value and decision. | `n: integer`, `responses: integer`, `critical_value: integer`, `p_value: exact number`, `alpha: exact number`, `reject_null: boolean`, `test: string` |
| PolicyDetails | Calculated error, power and expected sample size of a two-stage policy. | `n_stage1: integer`, `n_stage2: integer`, `maximum_sample_size: integer`, `typeI: exact number`, `typeI_target_met: boolean`, `power: exact number`, `power_target_met: boolean`, `expected_sample_size_null: exact number`, `expected_sample_size_alternative: exact number`, `early_stop_probability_null: exact number` |
| Diagnostic | A diagnostic code, severity and message. | `code: string`, `message: string`, `severity: string` |

Claim constructors return `TypeIClaim`, `ResultClaim`, `FamilywiseClaim` or `PlanningClaim`, all represented by Claim. Exact numbers, strings, booleans and lists are value types. Optional evidence stays optional through field access.

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

Bonferroni for two or more Fisher endpoints with an explicit joint-law contract. Dependence between endpoints is unrestricted.

- `bonferroni(analyses, alpha, joint_law) -> Family`
- `familywise(family) -> FamilywiseClaim`

### `planning` — Study planning

Exact power at a planning point, target checks and a bounded equal-arm sample-size search for the fixed Fisher analysis; targets also apply to two-stage policies. A size can be certified as sufficient or as the smallest in the declared range.

- `binomial_rates(p_control, p_treatment) -> Rates`
- `power_target(at, minimum, maximum_typeI) -> PowerTarget`
- `meets(analysis, target) -> PlanningClaim`
- `equal_arm_sizes(analysis, min_per_arm, max_per_arm) -> Candidates`
- `sample_sizes(analysis, min_n, max_n) -> OneArmCandidates`
- `response_rate(value) -> Rate`
- `sample_size(candidates, target) -> PlanningClaim`
- `smallest_sample_size(candidates, target) -> PlanningClaim`

### `designs.two_stage` — Adaptive designs

Single-arm two-stage binomial policy with an interim stop, using count thresholds or Beta-posterior thresholds. Type I error and power are checked for the complete policy. Count thresholds cover every rate at or below the null rate; posterior thresholds cover the declared null rate only.

- `two_stage_binomial(n_stage1, n_stage2) -> TwoStageModel`
- `threshold_rule(continue_above, reject_above) -> Rule`
- `beta_prior(a, b) -> Prior`
- `posterior_rule(prior, reference, continue_at_least, success_at_least) -> Rule`
- `two_stage_test(design, rule, null_rate) -> TwoStageAnalysis`

### `tests.binomial` — Analyses and claims

One-sided exact binomial test for a single arm. Type I error is checked for every rate at or below the null rate; power and sample size use the planning module. Observed counts give a Lean-checked p-value and decision.

- `one_arm_binomial(n) -> OneArmModel`
- `binomial_test(model, null_rate, alpha) -> OneSampleAnalysis`
- `responses(analysis, count) -> OneSampleObservation`
- `binomial_result(observation) -> ResultClaim`

## Built-in operations

- `verify(claim) -> VerificationResult`
- `calculate(claim) -> CalculationResult`

Verification and calculation run only on explicit execution; the editor plans them. Compilation cannot create evidence.

## Lean library concepts

The formal library also defines parameter domains, procedures, guarantees and composition rules. These are not all standalone `.stat` constructors yet. See [core object model](core-object-model.md) and [Lean objects](lean-objects.md).

For typed parameters and contracts in machine-readable form, run `statproof catalogue --json`. See [adding modules](adding-modules.md).
