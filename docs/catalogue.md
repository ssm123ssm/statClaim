# Object and module catalogue

Generated from the language registries. Update with `uv run python scripts/update_catalogue.py`; CI checks for drift.

All APIs are preview APIs. Object availability does not imply a proof adapter. See [scope](scope.md) for supported guarantees.

## Claims and results

| Object | Meaning | Public fields |
| --- | --- | --- |
| Guarantee | An error-rate statement: quantity, relation, bound, null and scope. | `quantity: string`, `relation: string`, `bound: exact number`, `null: string`, `scope: string`, `sentence: string` |
| Claim | Requested typeI, result, familywise or planning proposition. | `kind: string`, `subject: object`, `scope: string`, `guarantee: Option[Guarantee]` |
| VerificationResult | Explicit verification outcome; optional evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `evidence: Option[Evidence]` |
| CalculationResult | Calculation outcome; no proof evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `calculation: Option[CalculationDetails]`, `decision: Option[string]` |

## Core statistical objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Model | Sampling model and arm sizes. | `n_control: integer`, `n_treatment: integer` |
| StudyDesign | Model with a stopping rule. | `model: Model`, `stopping: string` |
| Hypothesis | A null restriction, not an assertion of truth. | `model: Model`, `predicate: string`, `value: exact number`, `statement: string` |
| Analysis | Design, compatible null and exact alpha. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number` |
| ContinuousModel | Two arms with a continuous outcome. | `n_control: integer`, `n_treatment: integer` |
| MeanHypothesis | A null restriction on the arm means. | `model: ContinuousModel`, `predicate: string`, `value: exact number`, `statement: string` |
| CitedAnalysis | Design, null and alpha for a test whose guarantee is cited, not proved. | `design: StudyDesign`, `null: MeanHypothesis`, `alpha: exact number`, `guarantee: Guarantee` |
| Observation | Observed counts tied to an analysis. | `analysis: Analysis`, `control_successes: integer`, `treatment_successes: integer` |
| Family | Analyses, family alpha and declared joint law. | `analyses: list`, `alpha: exact number`, `joint_law: string` |
| ComposedFamily | A family with cited members: the combination is proved, the members are assumed. | `analyses: list`, `alpha: exact number` |
| OneArmModel | One arm with a fixed sample size. | `n: integer` |
| OneSampleAnalysis | One-sided exact binomial test with its null rate and alpha. | `model: OneArmModel`, `null_rate: exact number`, `alpha: exact number` |
| OneSampleObservation | Observed responses for a one-sample test. | `analysis: OneSampleAnalysis`, `responses: integer` |
| DifferenceInterval | Observed two-arm counts and a confidence level. | `model: Model`, `control_successes: integer`, `treatment_successes: integer`, `level: exact number` |
| Interval | Observed count and confidence level. | `model: OneArmModel`, `responses: integer`, `level: exact number` |

## Planning objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Rates | Planning point for two arms; an input, not a fact. | `p_control: exact number`, `p_treatment: exact number` |
| Rate | Planning point for a single response rate. | `value: exact number` |
| PowerTarget | Required power at a point and a Type I bound. | `at: PlanningPoint`, `minimum: exact number`, `maximum_typeI: exact number` |
| Feasibility | One analysis assessed against one target. | `analysis: Analysis`, `target: PowerTarget` |
| Candidates | Finite equal-arm design space for a search. | `analysis: Analysis`, `min_per_arm: integer`, `max_per_arm: integer`, `ratio: integer` |
| Sizing | Candidates searched for a design meeting a target. | `candidates: Candidates`, `target: PowerTarget` |
| OneArmCandidates | Sample sizes searched for a one-sample test. | `analysis: OneSampleAnalysis`, `min_n: integer`, `max_n: integer` |
| TwoStageCandidates | Two-stage designs searched by an optimal or minimax criterion. | `null_rate: exact number`, `max_total: integer`, `criterion: string` |

## Adaptive design objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| TwoStageModel | Stage sizes of a single-arm design. | `n_stage1: integer`, `n_stage2: integer` |
| TwoStageObservation | Observed counts, with stage two only if the study continued. | `analysis: TwoStageAnalysis`, `stage1_responses: integer`, `stage2_responses: Option[integer]` |
| Prior | Beta prior with positive integer parameters. | `a: integer`, `b: integer` |
| Rule | Interim continuation and final decision rule. | `kind: string` |
| TwoStageAnalysis | Complete policy: stages, rule and the null response rate. | `design: TwoStageModel`, `rule: Rule`, `null_rate: exact number` |

## Evidence and inspection

| Object | Meaning | Public fields |
| --- | --- | --- |
| Evidence | Checked properties, assumptions and certificate. | `grade: string`, `sources: list`, `machine_checked: string`, `claim: Claim`, `certificate: Option[CertificateReference]`, `references: list`, `established_properties: list`, `required_assumptions: list` |
| CertificateReference | Certificate identity, path and hash. | `certificate_id: string`, `file: string`, `directory: string`, `sha256: string` |
| CalculationDetails | Exact p-value, alpha and test details. | `p_value: exact number`, `alpha: exact number`, `observed_table_probability: exact number`, `p_value_le_alpha: boolean`, `test: string`, `test_version: string` |
| PlanningDetails | Calculated sizes, power and target components; not proof evidence. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `power: Option[exact number]`, `power_target_met: boolean`, `typeI_bound: Option[exact number]`, `typeI_target_met: Option[boolean]`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| OneSampleDetails | Calculated critical value, error and power of a one-sample test. | `n: Option[integer]`, `critical_value: Option[integer]`, `typeI: Option[exact number]`, `typeI_target_met: Option[boolean]`, `power: Option[exact number]`, `power_target_met: boolean`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| OneSampleResultDetails | Exact one-sided p-value, critical value and decision. | `n: integer`, `responses: integer`, `critical_value: integer`, `p_value: exact number`, `alpha: exact number`, `reject_null: boolean`, `test: string` |
| DifferenceDetails | Estimate and interval for a difference of two proportions. | `level: exact number`, `arm_level: exact number`, `estimate: exact number`, `lower: exact number`, `upper: exact number`, `method: string` |
| MarginDetails | Thresholds, power and decision of an exact difference test. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `margin: Option[exact number]`, `thresholds: Option[list]`, `needed_treatment_successes: Option[integer]`, `typeI_bound: Option[exact number]`, `cells: Option[integer]`, `power: Option[exact number]`, `power_target_met: Option[boolean]`, `typeI_target_met: Option[boolean]`, `control_successes: Option[integer]`, `treatment_successes: Option[integer]`, `observed_difference: Option[exact number]`, `reject_null: Option[boolean]`, `candidates_evaluated: Option[integer]` |
| IntervalDetails | Estimate and exact confidence interval endpoints. | `n: integer`, `responses: integer`, `level: exact number`, `estimate: exact number`, `lower: exact number`, `upper: exact number`, `method: string` |
| StageResultDetails | Decision and error bound for observed two-stage counts. | `n_stage1: integer`, `n_stage2: integer`, `stage1_responses: integer`, `stage2_responses: Option[integer]`, `continued: boolean`, `reject_null: boolean`, `typeI_bound: exact number` |
| PolicyDetails | Calculated error, power and expected sample size of a two-stage policy. | `n_stage1: Option[integer]`, `n_stage2: Option[integer]`, `continue_above: Option[integer]`, `reject_above: Option[integer]`, `maximum_sample_size: Option[integer]`, `typeI: Option[exact number]`, `typeI_target_met: Option[boolean]`, `power: Option[exact number]`, `power_target_met: boolean`, `expected_sample_size_null: Option[exact number]`, `expected_sample_size_alternative: Option[exact number]`, `early_stop_probability_null: Option[exact number]`, `criterion: Option[string]`, `candidates_evaluated: Option[integer]` |
| Diagnostic | A diagnostic code, severity and message. | `code: string`, `message: string`, `severity: string` |

Claim constructors return `TypeIClaim`, `ResultClaim`, `FamilywiseClaim` or `PlanningClaim`, all represented by Claim. Exact numbers, strings, booleans and lists are value types. Optional evidence stays optional through field access.

## Modules

`use` imports built-in constructors; it does not load arbitrary files or plugins.

### `models.two_arm_continuous` — Models and hypotheses

Two arms with a continuous outcome; equal-means and mean-difference nulls. The model fixes no distribution.

- `two_arm_continuous(n_control, n_treatment) -> ContinuousModel`
- `equal_means(model) -> MeanHypothesis`
- `mean_difference_at_most(model, value) -> MeanHypothesis`
- `typeI(analysis) -> TypeIClaim`

### `tests.t` — Cited analyses

Pooled-variance and Welch t-tests for two means. The compiler checks the null and the sampling plan against each test's contract. The Type I guarantee is cited from the literature and is not checked by Lean: exact under normality and equal variances for the pooled test, a large-sample approximation for Welch.

- `t_test(design, null, alpha) -> CitedAnalysis`
  Required null: mean_treatment = mean_control; same model required.
- `t_test_one_sided(design, null, alpha) -> CitedAnalysis`
  Required null: mean_treatment - mean_control <= value; same model required.
- `welch_test(design, null, alpha) -> CitedAnalysis`
  Required null: mean_treatment = mean_control; same model required.
- `welch_test_one_sided(design, null, alpha) -> CitedAnalysis`
  Required null: mean_treatment - mean_control <= value; same model required.

### `models.two_arm_binomial` — Models and hypotheses

Two independent binomial arms; equality, difference and inequality nulls; observations and the Type I and result claims shared by two-arm analyses.

- `two_arm_binomial(n_control, n_treatment) -> Model`
- `equal_proportions(model) -> Hypothesis`
- `proportion_difference(model, value) -> Hypothesis`
- `proportion_difference_at_most(model, value) -> Hypothesis`
- `observe(analysis, control_successes, treatment_successes) -> Observation`
- `typeI(analysis) -> TypeIClaim`
- `result(observation) -> ResultClaim`

### `sampling` — Study designs

Fixed sampling is supported. Adaptive sampling is descriptive; its current Type I error requirement remains unresolved.

- `fixed(model) -> StudyDesign`
- `adaptive(model) -> StudyDesign`

### `tests.fisher` — Analyses and claims

Two-sided Fisher analysis for the equality null and one-sided analysis for "treatment no better than control", with Lean-backed result and Type I claims under fixed sampling.

- `fisher(design, null, alpha) -> Analysis`
  Required null: p_treatment = p_control (equal arm success probabilities); same model required.
- `fisher_one_sided(design, null, alpha) -> Analysis`
  Required null: p_treatment - p_control <= 0 (the treatment is no better than the control); same model required.

### `tests.difference` — Analyses and claims

Exact test of p_treatment - p_control <= margin, for non-inferiority (negative margin) or superiority (zero). Its error bound covers the whole null. Up to 120 participants per arm.

- `difference_test(design, null, alpha) -> Analysis`
  Required null: p_treatment - p_control <= margin, for a margin strictly between -1 and 1; same model required.

### `multiplicity.bonferroni` — Multiplicity and composition

Bonferroni for two to twenty endpoints; dependence between them is unrestricted. A family of two-sided Fisher analyses is proved outright. A family with cited tests is conditional: Lean checks the combination and the members are assumed.

- `bonferroni(analyses, alpha, [joint_law]) -> Family`
- `familywise(family) -> FamilywiseClaim`

### `planning` — Study planning

Exact power at a planning point, target checks and a bounded sample-size search with equal or unequal allocation for the fixed Fisher analysis. Targets also apply to one-sample tests and two-stage designs. A size can be certified as sufficient or as the smallest in the declared range.

- `binomial_rates(p_control, p_treatment) -> Rates`
- `power_target(at, minimum, maximum_typeI) -> PowerTarget`
- `meets(analysis, target) -> PlanningClaim`
- `equal_arm_sizes(analysis, min_per_arm, max_per_arm) -> Candidates`
- `allocated_arm_sizes(analysis, min_control, max_control, treatment_per_control) -> Candidates`
- `sample_sizes(analysis, min_n, max_n) -> OneArmCandidates`
- `response_rate(value) -> Rate`
- `sample_size(candidates, target) -> PlanningClaim`
- `smallest_sample_size(candidates, target) -> PlanningClaim`

### `designs.two_stage` — Adaptive designs

Single-arm two-stage binomial policy with an interim stop, using count thresholds or Beta-posterior thresholds. Type I error and power are checked for the complete policy; the error bound covers every rate at or below the null rate. Designs can be proposed or found by an optimal or minimax search. Observed counts give a checked decision.

- `two_stage_binomial(n_stage1, n_stage2) -> TwoStageModel`
- `threshold_rule(continue_above, reject_above) -> Rule`
- `beta_prior(a, b) -> Prior`
- `posterior_rule(prior, reference, continue_at_least, success_at_least) -> Rule`
- `stopped_at_interim(analysis, stage1_responses) -> TwoStageObservation`
- `completed_stages(analysis, stage1_responses, stage2_responses) -> TwoStageObservation`
- `two_stage_result(observation) -> ResultClaim`
- `two_stage_designs(null_rate, max_total, criterion) -> TwoStageCandidates`
- `two_stage_test(design, rule, null_rate) -> TwoStageAnalysis`

### `estimation` — Analyses and claims

Confidence interval for a difference of two proportions, from an exact interval per arm. Valid for every pair of rates; conservative.

- `difference_interval(model, control_successes, treatment_successes, level) -> IntervalClaim`

### `tests.binomial` — Analyses and claims

One-sided exact binomial test for a single arm. Type I error is checked for every rate at or below the null rate; power and sample size use the planning module. Observed counts give a Lean-checked p-value and decision, and an exact confidence interval with checked coverage.

- `one_arm_binomial(n) -> OneArmModel`
- `binomial_test(model, null_rate, alpha) -> OneSampleAnalysis`
- `confidence_interval(model, count, level) -> IntervalClaim`
- `responses(analysis, count) -> OneSampleObservation`
- `binomial_result(observation) -> ResultClaim`

## Built-in operations

- `verify(claim) -> VerificationResult`
- `calculate(claim) -> CalculationResult`

Verification and calculation run only on explicit execution; the editor plans them. Compilation cannot create evidence.

## Lean library concepts

The formal library also defines parameter domains, procedures, guarantees and composition rules. These are not all standalone `.stat` constructors yet. See [core object model](core-object-model.md) and [Lean objects](lean-objects.md).

For typed parameters and contracts in machine-readable form, run `statclaim catalogue --json`. See [adding modules](adding-modules.md).
