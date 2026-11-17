# Language reference and catalogue

Generated from the language registries. Update with `uv run python scripts/update_catalogue.py`; CI checks for drift.

All APIs are preview APIs. Object availability does not imply a proof adapter. See [scope](scope.md) for supported guarantees and the [language guide](stat-language.md) for a walkthrough.

Contents: [grammar](#grammar), [value types](#value-types), [objects](#objects), [modules and constructors](#modules), [operations](#built-in-operations), [statuses and other fixed values](#statuses-and-other-fixed-values), [cited methods](#cited-methods), [assumptions](#assumptions), [limits](#limits), [diagnostic codes](#diagnostic-codes).

## Grammar

```ebnf
file        = { statement NEWLINE } ;
statement   = "use" module
            | "let" NAME "=" expression
            | operation ;                      (* only verify and calculate *)
operation   = ( "verify" | "calculate" ) "(" expression ")"
            | ( "verify" | "calculate" ) expression ;      (* older spelling *)
module      = NAME { "." NAME } ;
expression  = primary { "." NAME } ;           (* field access *)
primary     = NAME                             (* a name declared earlier *)
            | NAME "(" [ arguments ] ")"       (* constructor call *)
            | "[" [ expression { "," expression } [ "," ] ] "]"
            | NUMBER | STRING ;
arguments   = argument { "," argument } [ "," ] ;
argument    = [ NAME "=" ] expression ;        (* positional before named *)
NUMBER      = [ "-" ] DIGITS [ "." DIGITS ]    (* exact decimal *)
            | [ "-" ] DIGITS "/" DIGITS ;      (* exact fraction *)
STRING      = '"' { character } '"' ;          (* JSON escapes *)
NAME        = ( letter | "_" ) { letter | digit | "_" } ;   (* ASCII *)
comment     = "#" to the end of the line ;
```

Statements end at a newline; calls and lists may span lines. Names must be declared before use and cannot be redeclared. There is no arithmetic, no control flow and no way to run other code.

## Value types

| Type | Meaning |
| --- | --- |
| `integer` | A whole number, such as `100`. |
| `exact number` | An exact decimal or fraction: `0.025` and `1/40` are the same value. Never a floating-point approximation. |
| `level` | An exact number between 0 and 1, used for alpha and confidence levels. Some tests require it strictly inside. |
| `string` | Text in double quotes, such as `"binomial_marginals"`. |
| `boolean` | `true` or `false`; appears in results only. |
| `list` | Items in square brackets. Family members and looks must be named analyses. |
| `Option[T]` | A value that may be absent, such as evidence after a failed check. Reading a field of an absent value gives an absent value. |

## Objects

A field is read with a dot: `analysis.alpha`. Only the fields listed here exist.

### Claims and results

| Object | Meaning | Public fields |
| --- | --- | --- |
| Guarantee | An error-rate statement: quantity, relation, bound, null and scope. | `quantity: string`, `relation: string`, `bound: exact number`, `null: string`, `scope: string`, `sentence: string` |
| Claim | Requested typeI, result, familywise or planning proposition. | `kind: string`, `subject: object`, `scope: string`, `guarantee: Option[Guarantee]` |
| VerificationResult | Explicit verification outcome; optional evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `evidence: Option[Evidence]` |
| CalculationResult | Calculation outcome; no proof evidence. | `request_id: integer`, `claim: Claim`, `source_sha256: string`, `status: string`, `diagnostics: list`, `calculation: Option[CalculationDetails]`, `decision: Option[string]` |

### Core statistical objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Model | Sampling model and arm sizes. | `n_control: integer`, `n_treatment: integer` |
| StudyDesign | Model with a stopping rule. | `model: Model`, `stopping: string` |
| Hypothesis | A null restriction, not an assertion of truth. | `model: Model`, `predicate: string`, `value: exact number`, `statement: string` |
| Analysis | Design, compatible null and exact alpha. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number` |
| OutcomeModel | Two arms with a continuous, survival or other registered outcome. | `outcome: string`, `n_control: integer`, `n_treatment: integer` |
| OutcomeNull | A null restriction for such a model. | `model: OutcomeModel`, `predicate: string`, `value: exact number`, `statement: string` |
| CitedAnalysis | Design, null and alpha for a test whose guarantee is cited, not proved. | `design: StudyDesign`, `null: OutcomeNull`, `alpha: exact number`, `guarantee: Guarantee` |
| Observation | Observed counts tied to an analysis. | `analysis: Analysis`, `control_successes: integer`, `treatment_successes: integer` |
| Family | Analyses, family alpha and declared joint law. | `analyses: list`, `alpha: exact number`, `joint_law: string` |
| ComposedFamily | A Bonferroni family or fixed sequence: the combination is proved, the members assumed. | `analyses: list`, `alpha: exact number` |
| OneArmModel | One arm with a fixed sample size. | `n: integer` |
| OneSampleAnalysis | One-sided exact binomial test with its null rate and alpha. | `model: OneArmModel`, `null_rate: exact number`, `alpha: exact number` |
| OneSampleObservation | Observed responses for a one-sample test. | `analysis: OneSampleAnalysis`, `responses: integer` |
| DifferenceInterval | Observed two-arm counts and a confidence level. | `model: Model`, `control_successes: integer`, `treatment_successes: integer`, `level: exact number` |
| Interval | Observed count and confidence level. | `model: OneArmModel`, `responses: integer`, `level: exact number` |

### Adaptive design objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Sequential | Looks at cumulative sample sizes, each with the level spent there. | `looks: list`, `alpha: exact number` |
| TwoStageModel | Stage sizes of a single-arm design. | `n_stage1: integer`, `n_stage2: integer` |
| TwoStageObservation | Observed counts, with stage two only if the study continued. | `analysis: TwoStageAnalysis`, `stage1_responses: integer`, `stage2_responses: Option[integer]` |
| Prior | Beta prior with positive integer parameters. | `a: integer`, `b: integer` |
| Rule | Interim continuation and final decision rule. | `kind: string` |
| TwoStageAnalysis | Complete policy: stages, rule and the null response rate. | `design: TwoStageModel`, `rule: Rule`, `null_rate: exact number` |

### Planning objects

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

### Evidence and inspection

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

`use` imports built-in constructors; it does not load arbitrary files or plugins. Arguments may be given by position or by name. A `?` marks an argument that may be left out.

### `models.two_arm_continuous` — Models and hypotheses

Two arms with a continuous outcome; equal-means and mean-difference nulls. Fixes no distribution.

- `two_arm_continuous(n_control: integer, n_treatment: integer) -> OutcomeModel`
  Two arms with a continuous outcome, such as a change in blood pressure. The model fixes no distribution; each test states the one it assumes.
- `equal_means(model: OutcomeModel) -> OutcomeNull`
  Null: the two arm means are equal.
- `mean_difference_at_most(model: OutcomeModel, value: number) -> OutcomeNull`
  Null: mean_treatment - mean_control <= value, in the outcome's units. Zero asks whether the treatment is better; a negative value is a non-inferiority margin.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `models.two_arm_survival` — Models and hypotheses

Two arms with a time-to-event outcome, possibly censored; equal-survival null. Fixes no distribution.

- `two_arm_survival(n_control: integer, n_treatment: integer) -> OutcomeModel`
  Two arms followed for the time until an event, such as death or relapse. Some participants may be censored: followed without the event being seen. The model fixes no distribution; each test states the one it assumes.
- `equal_survival(model: OutcomeModel) -> OutcomeNull`
  Null: the two arms have the same distribution of time to the event.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.t` — Cited analyses

Pooled-variance and Welch t-tests for two means. The compiler checks the null and the sampling plan against each test's contract. The Type I guarantee is cited from the literature and is not checked by Lean: exact under normality and equal variances for the pooled test, a large-sample approximation for Welch.

- `t_test(design: StudyDesign, null: OutcomeNull, alpha: level) -> CitedAnalysis`
  Two-sided pooled-variance t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `t_test_one_sided(design: StudyDesign, null: OutcomeNull, alpha: level) -> CitedAnalysis`
  One-sided pooled-variance t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment - mean_control <= value.
  Required null: mean_treatment - mean_control <= value; same model required.
- `welch_test(design: StudyDesign, null: OutcomeNull, alpha: level) -> CitedAnalysis`
  Two-sided Welch t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `welch_test_one_sided(design: StudyDesign, null: OutcomeNull, alpha: level) -> CitedAnalysis`
  One-sided Welch t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment - mean_control <= value.
  Required null: mean_treatment - mean_control <= value; same model required.

### `tests.survival` — Cited analyses

The log-rank test for two survival curves. The compiler checks the null and the sampling plan against the test's contract. The Type I guarantee is cited from the literature and is a large-sample approximation in the number of events. Proportional hazards is not needed for the error rate; it matters for power.

- `log_rank(design: StudyDesign, null: OutcomeNull, alpha: level) -> CitedAnalysis`
  Two-sided log-rank test. Its guarantee is cited from the literature and is not checked by Lean. Null: survival_treatment = survival_control at every time.
  Required null: survival_treatment = survival_control at every time; same model required.

### `models.two_arm_binomial` — Models and hypotheses

Two independent binomial arms; equality, difference and inequality nulls; observations and the Type I and result claims shared by two-arm analyses.

- `two_arm_binomial(n_control: integer, n_treatment: integer) -> Model`
- `equal_proportions(model: Model) -> Hypothesis`
  Null: p_treatment = p_control. This declares a restriction under which a guarantee is requested, not that the null is true.
- `proportion_difference(model: Model, value: number) -> Hypothesis`
  Null: p_treatment - p_control = value. The difference is absolute, not a relative percentage; value is exact and lies in [-1, 1]. A zero difference is the equal-proportions null.
- `proportion_difference_at_most(model: Model, value: number) -> Hypothesis`
  Null: p_treatment - p_control <= value. This is an inequality null, including when value=0; it is not the equality null supported by the current two-sided Fisher analysis.
- `observe(analysis: Analysis, control_successes: integer, treatment_successes: integer) -> Observation`
- `typeI(analysis: Analysis) -> TypeIClaim`
- `result(observation: Observation) -> ResultClaim`

### `sampling` — Study designs

Fixed sampling is supported. Adaptive sampling is descriptive; its current Type I error requirement remains unresolved.

- `fixed(model: Model) -> StudyDesign`
- `adaptive(model: Model) -> StudyDesign`

### `tests.fisher` — Analyses and claims

Two-sided Fisher analysis for the equality null and one-sided analysis for "treatment no better than control", with Lean-backed result and Type I claims under fixed sampling.

- `fisher(design: StudyDesign, null: Hypothesis, alpha: level) -> Analysis`
  The current Fisher analysis and its checked guarantee support equality only. Keep your declared null if it expresses the intended question and choose or implement an analysis whose contract supports it. Use equal_proportions(model=...) only if equality is the intended null; replacing the null changes the statistical question.
  Required null: p_treatment = p_control (equal arm success probabilities); same model required.
- `fisher_one_sided(design: StudyDesign, null: Hypothesis, alpha: level) -> Analysis`
  The one-sided Fisher analysis tests whether the treatment's success probability exceeds the control's. Its null is proportion_difference_at_most(model=..., value=0). A nonzero margin is a different question and needs an analysis that supports it. Use equal_proportions with fisher(...) for a two-sided question.
  Required null: p_treatment - p_control <= 0 (the treatment is no better than the control); same model required.

### `tests.difference` — Analyses and claims

Exact test of p_treatment - p_control <= margin, for non-inferiority (negative margin) or superiority (zero). Its error bound covers the whole null. Up to 120 participants per arm.

- `difference_test(design: StudyDesign, null: Hypothesis, alpha: level) -> Analysis`
  The exact difference test rejects when the treatment's observed success proportion exceeds the control's by enough. Its null is proportion_difference_at_most(model=..., value=margin). A negative margin is a non-inferiority question; zero is superiority.
  Required null: p_treatment - p_control <= margin, for a margin strictly between -1 and 1; same model required.

### `multiplicity.bonferroni` — Multiplicity and composition

Bonferroni for two to twenty endpoints; dependence between them is unrestricted. A family of two-sided Fisher analyses is proved outright. Any other family, with one-sided, margin or cited tests, is conditional: Lean checks the combination and the members are assumed.

- `bonferroni(analyses: list, alpha: level, joint_law?: string) -> Family`
  Bonferroni: the members' levels may sum to at most alpha. Members may be exact tests, cited tests, designs with interim looks, or a mix; dependence between them is unrestricted. A family of two-sided Fisher analyses is proved outright. Any other family is conditional: Lean checks the combination and each member's own bound is assumed.
- `familywise(family: Family) -> FamilywiseClaim`

### `multiplicity.fixed_sequence` — Multiplicity and composition

Hierarchical testing in a fixed order, each test at the full level and only after every earlier test rejected. Lean checks the combination; the tests' own bounds are assumed.

- `fixed_sequence(analyses: list, alpha: level) -> ComposedFamily`
  Hierarchical testing: the analyses are tested in the listed order, each at the full level alpha, and a test is carried out only if every earlier one rejected. Entries may be exact tests, cited tests or designs with interim looks. Lean checks the combination; each test's own bound is assumed.
- `familywise(family: Family) -> FamilywiseClaim`

### `planning` — Study planning

Exact power at a planning point, target checks and a bounded sample-size search with equal or unequal allocation for the fixed Fisher analysis. Targets also apply to one-sample tests and two-stage designs. A size can be certified as sufficient or as the smallest in the declared range.

- `binomial_rates(p_control: number, p_treatment: number) -> Rates`
  A planning point: one success probability per arm. It is an input for power, not the null and not an established fact.
- `power_target(at: PlanningPoint, minimum: number, maximum_typeI: level) -> PowerTarget`
  Require power of at least minimum at one planning point, and a Type I error bound of at most maximum_typeI under the null. Power at this point is not a guarantee for other alternatives.
- `meets(analysis: Analysis, target: PowerTarget) -> PlanningClaim`
  Claim that this analysis meets every component of the target. calculate computes the components; verify must establish all.
- `equal_arm_sizes(analysis: Analysis, min_per_arm: integer, max_per_arm: integer) -> Candidates`
  A finite design space: equal arm sizes within inclusive bounds, keeping the analysis's sampling, null form, test and alpha.
- `allocated_arm_sizes(analysis: Analysis, min_control: integer, max_control: integer, treatment_per_control: integer) -> Candidates`
  A finite design space with unequal allocation: each candidate has n controls and treatment_per_control * n treated participants, for n within the inclusive bounds.
- `sample_sizes(analysis: OneSampleAnalysis, min_n: integer, max_n: integer) -> OneArmCandidates`
  A finite design space: sample sizes within inclusive bounds for a one-sample test, keeping its null rate and alpha.
- `response_rate(value: number) -> Rate`
  A planning point for a single-arm design.
- `sample_size(candidates: Candidates, target: PowerTarget) -> PlanningClaim`
  Claim that some candidate meets the target. The search is ascending; a sufficient size is not claimed to be the smallest possible.
- `smallest_sample_size(candidates: Candidates, target: PowerTarget) -> PlanningClaim`
  Claim that a candidate meets the target and that no smaller candidate in the declared range does. Nothing is claimed outside the range.

### `designs.group_sequential` — Adaptive designs

One test repeated at several looks with the error level split across them, stopping at the first rejection. Lean checks that the split gives the overall bound; each look's own bound is assumed. Conservative: it ignores the correlation between looks.

- `alpha_spending(looks: list, alpha: level) -> Sequential`
  One test repeated at several looks, stopping at the first rejection. Give each look as an analysis whose model has the cumulative arm sizes at that look, with the level spent there. The levels may sum to at most alpha. Lean checks the combination; each look's own bound is assumed. The split is conservative.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `designs.two_stage` — Adaptive designs

Single-arm two-stage binomial policy with an interim stop, using count thresholds or Beta-posterior thresholds. Type I error and power are checked for the complete policy; the error bound covers every rate at or below the null rate. Designs can be proposed or found by an optimal or minimax search. Observed counts give a checked decision.

- `two_stage_binomial(n_stage1: integer, n_stage2: integer) -> TwoStageModel`
  One arm, two stages, one response rate. Stage two is observed only if the interim rule continues.
- `threshold_rule(continue_above: integer, reject_above: integer) -> Rule`
  Continue when stage-one responses exceed continue_above; reject the null when total responses exceed reject_above.
- `beta_prior(a: integer, b: integer) -> Prior`
  Beta(a, b) prior on the response rate, positive integers.
- `posterior_rule(prior: Prior, reference: number, continue_at_least: level, success_at_least: level) -> Rule`
  Continue, and finally declare success, when the posterior probability that the response rate exceeds reference reaches the given level. A posterior threshold does not by itself bound Type I error.
- `stopped_at_interim(analysis: TwoStageAnalysis, stage1_responses: integer) -> TwoStageObservation`
  Observed data when the interim rule stopped the study. Rejected if the declared rule would have continued.
- `completed_stages(analysis: TwoStageAnalysis, stage1_responses: integer, stage2_responses: integer) -> TwoStageObservation`
  Observed data from both stages. Rejected if the declared rule would have stopped after stage one.
- `two_stage_result(observation: TwoStageObservation) -> ResultClaim`
  Claim about the decision the declared design reaches for the observed counts, with the design's error bound.
- `two_stage_designs(null_rate: number, max_total: integer, criterion: string) -> TwoStageCandidates`
  Count-threshold two-stage designs with total size up to max_total. criterion="optimal" minimises the expected sample size at the null rate; "minimax" minimises the maximum sample size. The selected design is certified; the ranking is a calculation.
- `two_stage_test(design: TwoStageModel, rule: Rule, null_rate: number) -> TwoStageAnalysis`
  The complete policy: stages, interim stop, final decision and the null response rate it tests.

### `estimation` — Analyses and claims

Confidence interval for a difference of two proportions, from an exact interval per arm. Valid for every pair of rates; conservative.

- `difference_interval(model: Model, control_successes: integer, treatment_successes: integer, level: number) -> IntervalClaim`
  Confidence interval for p_treatment - p_control, built from an exact interval for each arm. It is valid for every pair of true rates and is wider than intervals built for the difference directly, so it can include zero when a test rejects.

### `tests.binomial` — Analyses and claims

One-sided exact binomial test for a single arm. Type I error is checked for every rate at or below the null rate; power and sample size use the planning module. Observed counts give a Lean-checked p-value and decision, and an exact confidence interval with checked coverage.

- `one_arm_binomial(n: integer) -> OneArmModel`
  One arm with n independent binary responses.
- `binomial_test(model: OneArmModel, null_rate: number, alpha: level) -> OneSampleAnalysis`
  One-sided exact binomial test. Null: response rate <= null_rate. Rejects at the smallest response count whose upper tail probability at null_rate is at most alpha.
- `confidence_interval(model: OneArmModel, count: integer, level: number) -> IntervalClaim`
  Exact (Clopper-Pearson) confidence interval for the response rate. Endpoints are rounded outward to four decimals, so coverage is at least the stated level for every true rate.
- `responses(analysis: OneSampleAnalysis, count: integer) -> OneSampleObservation`
  The observed number of responses for this analysis.
- `binomial_result(observation: OneSampleObservation) -> ResultClaim`
  Claim about the exact p-value and decision for the observed count, with the test's Type I bound.

## Built-in operations

- `verify(claim: Claim) -> VerificationResult`
- `calculate(claim: Claim) -> CalculationResult`

Verification and calculation run only on explicit execution; the editor plans them. Compilation cannot create evidence.

## Statuses and other fixed values

### Result status (`result.status`)

| Status | Meaning |
| --- | --- |
| `verified` | Lean proved the guarantee. Evidence grade `proved`. |
| `conditional` | Lean proved how the parts combine; each part's own guarantee is assumed. Evidence grade `conditional`. |
| `cited` | The study fits a published method's contract; the guarantee is cited, not machine-checked. Evidence grade `cited`. |
| `calculated` | A `calculate` request produced numbers. No evidence. |
| `unresolved_obligation` | A requirement is unmet or a target is missed. No evidence. Not a finding that the claim is false. |
| `backend_error` | Lean could not be run or failed for a technical reason. No evidence. |
| `not_executed` | The request was planned by `compile` and has not been run. |

### File status (`Program status`)

| Status | Meaning |
| --- | --- |
| `invalid` | The file has an error and nothing was run. |
| `elaborated` | The file compiles with no open requirement; nothing was run. |
| `unresolved_obligation` | At least one claim has an unmet requirement. |
| `cited` | Every claim went through and the weakest is cited. |
| `conditional` | Every claim went through and the weakest is conditional. |
| `verified` | Every verified claim was proved; calculations may also be present. |
| `calculated` | Only calculations were requested. |
| `stale_source` | The file changed while it was being checked. Run it again. |

### Evidence grade (`evidence.grade`)

| Grade | Meaning | `evidence.sources` | `evidence.machine_checked` |
| --- | --- | --- | --- |
| `proved` | proved in Lean | `lean_proof` | `guarantee` |
| `conditional` | combination proved in Lean; the members' own guarantees are assumed | `lean_proof`, `member_guarantees` | `composition` |
| `cited` | cited from the literature; not machine-checked | `literature` | `contract` |
| `simulated` | estimated by simulation; not a proof | `simulation` | `contract` |

### Evidence source

| Value | Meaning |
| --- | --- |
| `lean_proof` | a proof in Lean |
| `literature` | a published result |
| `member_guarantees` | the members' own guarantees, each proved or cited separately |
| `simulation` | a simulation |

### What a machine checked

| Value | Meaning |
| --- | --- |
| `guarantee` | Lean checked the guarantee itself |
| `composition` | Lean checked how the parts combine, not the parts |
| `contract` | only the fit between the study and the method's contract was checked |

### Guarantee scope (`claim.scope`)

| Value | Meaning |
| --- | --- |
| `finite_sample` | finite-sample bound |
| `asymptotic` | large-sample approximation |

### Assumption kind

| Kind | Meaning |
| --- | --- |
| `design` | About the study plan. Compared with the declared design where possible. |
| `sampling` | About how observations arise. Not checkable from a declaration. |
| `distribution` | About the outcome's distribution. Not checkable from a declaration. |
| `member` | A member test's own error bound, relied on when tests are combined. |
| `scope` | Says which null or planning point the claim is about. A condition, not a risk. |
| `data` | About the supplied data matching the declared study. |
| `unproved_step` | A mathematical identity that is used but not proved in Lean. |

### `Claim.kind`

| Value | Meaning |
| --- | --- |
| `typeI` | Type I error of an analysis or a sequential design. |
| `familywise` | Familywise error of a family. |
| `result` | The p-value and decision for observed data. |
| `meets` | A design meets a power and Type I target. |
| `sample_size` | Some, or the smallest, size in a range meets a target. |
| `interval` | A confidence interval and its coverage. |

### `StudyDesign.stopping`

| Value | Meaning |
| --- | --- |
| `fixed` | From `fixed(...)`: sizes set in advance, one analysis. |
| `data_dependent` | From `adaptive(...)`: leaves error claims unresolved. |

### `bonferroni joint_law`

| Value | Meaning |
| --- | --- |
| `binomial_marginals` | The only value, and the default. Allowed only when every member is a two-sided Fisher analysis; leave it out otherwise. |

### `two_stage_candidates criterion`

| Value | Meaning |
| --- | --- |
| `optimal` | Ranking used by the two-stage design search. |
| `minimax` | Ranking used by the two-stage design search. |

### `Diagnostic.severity`

| Value | Meaning |
| --- | --- |
| `error` | The file is invalid. |
| `obligation` | A requirement is open; the file is valid. |

### `Assumption status`

| Value | Meaning |
| --- | --- |
| `declared` | The file itself states it. |
| `assumed` | Nothing in the file can show it. |
| `condition` | Says which null or planning point the claim is about. |

## Cited methods

Guarantees taken from the literature. See [cited methods](cited-methods.md).

| Constructor | Version | Outcome | Null | Error rate | Scope | Minimum size |
| --- | --- | --- | --- | --- | --- | --- |
| `t_test` | 1 | continuous | `equal_means` | equals alpha | `finite_sample` | 1 per arm, 3 total |
| `t_test_one_sided` | 1 | continuous | `mean_difference_at_most` | at most alpha | `finite_sample` | 1 per arm, 3 total |
| `welch_test` | 1 | continuous | `equal_means` | equals alpha | `asymptotic` | 2 per arm, 4 total |
| `welch_test_one_sided` | 1 | continuous | `mean_difference_at_most` | at most alpha | `asymptotic` | 2 per arm, 4 total |
| `log_rank` | 1 | survival | `equal_survival` | equals alpha | `asymptotic` | 1 per arm, 2 total |

**`t_test`** (Two-sided pooled-variance t-test) assumes `independent_observations`, `fixed_sample_sizes`, `single_analysis`, `normal_outcomes`, `equal_variances`. References:

- Student (1908). The probable error of a mean. Biometrika 6(1), 1-25.
- Fisher, R. A. (1925). Applications of 'Student's' distribution. Metron 5, 90-104.
- Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses, 3rd ed. Springer. Chapters 5 and 11.

**`t_test_one_sided`** (One-sided pooled-variance t-test) assumes `independent_observations`, `fixed_sample_sizes`, `single_analysis`, `normal_outcomes`, `equal_variances`. References:

- Student (1908). The probable error of a mean. Biometrika 6(1), 1-25.
- Fisher, R. A. (1925). Applications of 'Student's' distribution. Metron 5, 90-104.
- Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses, 3rd ed. Springer. Chapters 5 and 11.

**`welch_test`** (Two-sided Welch t-test) assumes `independent_observations`, `fixed_sample_sizes`, `single_analysis`, `finite_variance`. References:

- Welch, B. L. (1947). The generalization of 'Student's' problem when several different population variances are involved. Biometrika 34(1-2), 28-35.
- Satterthwaite, F. E. (1946). An approximate distribution of estimates of variance components. Biometrics Bulletin 2(6), 110-114.
- Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses, 3rd ed. Springer. Chapters 5 and 11.

**`welch_test_one_sided`** (One-sided Welch t-test) assumes `independent_observations`, `fixed_sample_sizes`, `single_analysis`, `finite_variance`. References:

- Welch, B. L. (1947). The generalization of 'Student's' problem when several different population variances are involved. Biometrika 34(1-2), 28-35.
- Satterthwaite, F. E. (1946). An approximate distribution of estimates of variance components. Biometrics Bulletin 2(6), 110-114.
- Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses, 3rd ed. Springer. Chapters 5 and 11.

**`log_rank`** (Two-sided log-rank test) assumes `independent_observations`, `independent_censoring`, `prespecified_analysis_time`, `single_analysis`. References:

- Mantel, N. (1966). Evaluation of survival data and two new rank order statistics arising in its consideration. Cancer Chemotherapy Reports 50(3), 163-170.
- Peto, R. and Peto, J. (1972). Asymptotically efficient rank invariant test procedures. Journal of the Royal Statistical Society A 135(2), 185-207.
- Fleming, T. R. and Harrington, D. P. (1991). Counting Processes and Survival Analysis. Wiley.

## Assumptions

Assumptions of the cited methods and of combinations, by id. The exact modules' assumptions are classified in `methods/identify.py`.

| Id | Kind | Text |
| --- | --- | --- |
| `independent_observations` | sampling | Observations are independent within and between the two arms. |
| `fixed_sample_sizes` | design | Arm sizes are fixed before observing outcomes. |
| `single_analysis` | design | The test is run once, on the complete data. |
| `normal_outcomes` | distribution | Outcomes in each arm are normally distributed. |
| `equal_variances` | distribution | The two arms have the same variance. |
| `finite_variance` | distribution | Outcomes in each arm are identically distributed with finite, positive variance. |
| `prespecified_family` | design | The set of analyses and their levels are chosen before outcomes are observed. |
| `independent_censoring` | sampling | Within each arm, censoring is independent of the time to the event. |
| `prespecified_analysis_time` | design | When to analyse is fixed in advance, by calendar time or by a number of events, and does not depend on the observed difference between arms. |
| `prespecified_looks` | design | The looks happen at the declared cumulative sample sizes, fixed in advance, and the study stops at the first look that rejects. |
| `prespecified_order` | design | The tests and their order are fixed in advance, and a test is carried out only if every earlier test in the order rejected. |

## Limits

| Quantity | Supported |
| --- | --- |
| Analyses in a family, or looks in a sequential design | 2 to 20 |
| Participants per arm, exact test with a margin | up to 120 |
| Participants per arm, Fisher planning search | up to 500 |
| Allocation ratio in a planning search | 1 to 10 |
| Participants, one-sample binomial test | up to 1000 |
| Participants per stage, two-stage design | up to 200 |
| Total participants, two-stage design search | up to 120 |

## Diagnostic codes

An `error` makes the file invalid. An `obligation` leaves a claim unresolved; it is never a finding that the claim is false.

| Code | Severity | Reported when |
| --- | --- | --- |
| `syntax` | error | The text does not follow the grammar. |
| `number` | error | A number is malformed or has a zero denominator. |
| `string` | error | A string is unterminated or has a bad escape. |
| `name` | error | A name is not an ASCII identifier. |
| `depth` | error | An expression is nested too deeply. |
| `unknown_module` | error | `use` names a module that does not exist. |
| `module_conflict` | error | Two loaded modules define the same constructor. |
| `unknown_constructor` | error | A call names no loaded constructor; the hint names the module to `use`. |
| `unknown_name` | error | A name is used before it is declared. |
| `redefinition` | error | A name is declared twice; bindings are immutable. |
| `reserved_name` | error | A binding uses the name of a built-in operation. |
| `dependency` | error | A declaration depends on one that failed. |
| `arguments` | error | An argument is missing, unknown, repeated or surplus. |
| `type` | error | An argument has the wrong type, or belongs to another kind of outcome. |
| `domain` | error | A value is outside its allowed range. |
| `unknown_field` | error | An object has no public field of that name. |
| `absent_value` | error | A field is read from a value that is absent. |
| `runtime_dependency` | error | A constructor is given a value that exists only after execution. |
| `unsupported_claim` | error | The claim cannot be used with this operation. |
| `model_mismatch` | error | The design and the null are declared over different models. |
| `hypothesis_mismatch` | error | The test does not support the declared null. Not a finding that the null is false. |
| `alternative_in_null` | error | The planning point lies inside the null. |
| `planning_point` | error | The planning point does not fit the analysis. |
| `rule_mismatch` | error | A stopping rule does not fit the two-stage design. |
| `sampling_contract` | error | A joint law is given where none applies, or is not supported. |
| `family_size` | error | A family or sequential design has too few or too many entries. |
| `duplicate_analysis` | error | A family or sequential design lists an analysis twice. |
| `sequential_question` | error | The looks of a sequential design differ in test or null. |
| `sequence_level` | error | A test in a fixed sequence does not use the full level. |
| `sequential_order` | error | The looks are not in order of growing sample size. |
| `sampling_scope` | obligation | The design stops on the data, which the guarantee does not cover. Not evidence of inflated error. |
| `allocation` | obligation | The members' levels sum to more than the overall level. |
| `typeI_target_not_established` | obligation | The analysis's level exceeds the requested Type I bound. |
| `typeI_target_not_met` | obligation | The calculated Type I error exceeds the target. |
| `power_target_not_met` | obligation | The calculated power is below the target. |
| `no_feasible_candidate` | obligation | No design in the searched range meets the target. |
| `verification` | obligation | Lean could not establish the claim; the message says why. |
| `source_changed` | obligation | The file changed while it was being checked. |
| `snapshot_changed` | obligation | The retained copy of the file changed during the run. |

## Lean library concepts

The formal library also defines parameter domains, procedures, guarantees and composition rules. These are not all standalone `.stat` constructors yet. See [core object model](core-object-model.md) and [Lean objects](lean-objects.md).

The same content is available in machine-readable form from `statclaim catalogue --json`. See [adding modules](adding-modules.md).
