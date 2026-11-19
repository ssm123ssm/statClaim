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
| Assignment | How participants reach the two arms: the arm sizes, clusters and, when declared, the randomisation. Shared by outcomes on the same participants. | `n_control: integer`, `n_treatment: integer`, `randomisation: Option[string]`, `block_size: Option[integer]` |
| Outcome | What is measured on each participant: its kind and which direction is better. | `kind: string`, `better: Option[string]` |
| Model | Two binomial arms: an assignment and a binary outcome. | `assignment: Assignment`, `outcome: Outcome`, `n_control: integer`, `n_treatment: integer`, `better: Option[string]` |
| StudyDesign | Model with a stopping rule. | `model: Model`, `stopping: string` |
| Hypothesis | A null restriction, not an assertion of truth. | `model: Model`, `predicate: string`, `value: exact number`, `statement: string` |
| Analysis | Design, compatible null and exact alpha. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number` |
| OutcomeModel | Two arms: an assignment and a continuous, survival or other registered outcome. | `assignment: Assignment`, `outcome: Outcome`, `n_control: integer`, `n_treatment: integer`, `better: Option[string]` |
| OutcomeNull | A null restriction for such a model. | `model: OutcomeModel`, `predicate: string`, `value: exact number`, `statement: string` |
| Stratum | One stratum of a stratified or blocked assignment: randomised units per arm. | `control: integer`, `treatment: integer` |
| SharpNull | The sharp null: treatment changes no participant's outcome. Not a null about means. | `model: Model`, `predicate: string`, `statement: string` |
| RandomisationAnalysis | Design, sharp null and alpha for a randomisation test; its level is proved in Lean. | `design: StudyDesign`, `null: SharpNull`, `alpha: exact number`, `draws: Option[integer]`, `guarantee: Guarantee` |
| CitedAnalysis | Design, null and alpha for a test whose guarantee is cited, not proved. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number`, `guarantee: Guarantee` |
| Observation | Observed counts tied to an analysis. | `analysis: Analysis`, `control_successes: integer`, `treatment_successes: integer` |
| Family | Analyses, family alpha and declared joint law. | `analyses: list`, `alpha: exact number`, `joint_law: string` |
| ComposedFamily | A family, sequence or graph of analyses and other combinations; the members are assumed. | `analyses: list`, `alpha: exact number` |
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
| MeanDifference | Planning point for a continuous outcome: a mean difference and an SD. | `value: exact number`, `sd: exact number` |
| HazardRatio | Planning point for a survival outcome: a hazard ratio and a number of events. | `value: exact number`, `events: integer` |
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
| ApproximatePowerDetails | Approximate power and critical estimate of a cited test; not a bound. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `power: Option[exact number]`, `power_target_met: boolean`, `critical_estimate: Option[exact number]`, `reject_when: Option[string]`, `standard_error: Option[exact number]`, `alpha: Option[exact number]`, `typeI_target_met: Option[boolean]`, `formula: Option[string]`, `candidates_evaluated: Option[integer]` |
| Diagnostic | A diagnostic code, severity and message. | `code: string`, `message: string`, `severity: string` |

Claim constructors return `TypeIClaim`, `ResultClaim`, `FamilywiseClaim` or `PlanningClaim`, all represented by Claim. Exact numbers, strings, booleans and lists are value types. Optional evidence stays optional through field access.

## Modules

`use` imports built-in constructors; it does not load arbitrary files or plugins. Arguments may be given by position or by name. A `?` marks an argument that may be left out.

### `models.two_arm_continuous` — Models and hypotheses

Two arms with a continuous outcome; equal-means and mean-difference nulls. Fixes no distribution.

- `two_arm_continuous(n_control: integer, n_treatment: integer, better?: string) -> OutcomeModel`
  Two arms with a continuous outcome, such as a change in blood pressure. The model fixes no distribution; each test states the one it assumes. Shorthand for two_arm(assignment=assignment(n_control, n_treatment), outcome=continuous_outcome(better)). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `assignment(n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  How participants are assigned to the two arms: the two arm sizes and, when declared, how the assignment was randomised. One assignment can be shared by several outcomes measured on the same participants. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `cluster_assignment(clusters_control: integer, clusters_treatment: integer, n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  Whole clusters, such as clinics or schools, are assigned to the arms, and everyone in a cluster gets the same arm. clusters_control and clusters_treatment count the clusters; n_control and n_treatment count the participants. Sites in a trial that randomises participants are not clusters: use assignment(...) there. Tests that assume independent participants are refused. With randomisation, the units are the clusters. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `stratum(control: integer, treatment: integer) -> Stratum`
  One stratum of a stratified or blocked assignment: how many randomised units, participants or clusters, it has in each arm.
- `continuous_outcome(better?: string, measurements?: integer) -> Outcome`
  The continuous outcome measured on each participant. Combine it with an assignment in two_arm(...). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption. measurements is how many times the outcome is measured on each participant, 1 if left out. With more than one, tests that take one value per participant are refused.
- `two_arm(assignment: Assignment, outcome: Outcome) -> Model`
  A two-arm model from an assignment and an outcome. A binary outcome gives the binomial model; any other outcome gives an OutcomeModel. The same pieces give the same model as the one-call constructors, such as two_arm_continuous.
- `equal_means(model: OutcomeModel) -> OutcomeNull`
  Null: the two arm means are equal.
- `mean_difference_at_most(model: OutcomeModel, value: number) -> OutcomeNull`
  Null: mean_treatment - mean_control <= value, in the outcome's units. Zero asks whether the treatment is better; a negative value is a non-inferiority margin. This direction suits an outcome where higher is better.
- `mean_difference_at_least(model: OutcomeModel, value: number) -> OutcomeNull`
  Null: mean_treatment - mean_control >= value, for an outcome where lower is better. Zero asks whether the treatment is better (lower); a positive value is a non-inferiority margin.
- `no_effect(model: Model) -> SharpNull`
  Sharp null: treatment changes no participant's outcome, so each participant would have the same outcome in either arm. It is stronger than equal means or proportions, and only randomisation_test supports it.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `models.two_arm_survival` — Models and hypotheses

Two arms with a time-to-event outcome, possibly censored; equal-survival null. Fixes no distribution.

- `two_arm_survival(n_control: integer, n_treatment: integer, better?: string) -> OutcomeModel`
  Two arms followed for the time until an event, such as death or relapse. Some participants may be censored: followed without the event being seen. The model fixes no distribution; each test states the one it assumes. Shorthand for two_arm(assignment=assignment(n_control, n_treatment), outcome=survival_outcome(better)). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `assignment(n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  How participants are assigned to the two arms: the two arm sizes and, when declared, how the assignment was randomised. One assignment can be shared by several outcomes measured on the same participants. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `cluster_assignment(clusters_control: integer, clusters_treatment: integer, n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  Whole clusters, such as clinics or schools, are assigned to the arms, and everyone in a cluster gets the same arm. clusters_control and clusters_treatment count the clusters; n_control and n_treatment count the participants. Sites in a trial that randomises participants are not clusters: use assignment(...) there. Tests that assume independent participants are refused. With randomisation, the units are the clusters. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `stratum(control: integer, treatment: integer) -> Stratum`
  One stratum of a stratified or blocked assignment: how many randomised units, participants or clusters, it has in each arm.
- `survival_outcome(better?: string) -> Outcome`
  The survival outcome measured on each participant. Combine it with an assignment in two_arm(...). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `two_arm(assignment: Assignment, outcome: Outcome) -> Model`
  A two-arm model from an assignment and an outcome. A binary outcome gives the binomial model; any other outcome gives an OutcomeModel. The same pieces give the same model as the one-call constructors, such as two_arm_continuous.
- `equal_survival(model: OutcomeModel) -> OutcomeNull`
  Null: the two arms have the same distribution of time to the event.
- `no_effect(model: Model) -> SharpNull`
  Sharp null: treatment changes no participant's outcome, so each participant would have the same outcome in either arm. It is stronger than equal means or proportions, and only randomisation_test supports it.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.declared` — Declared analyses

A test the author names and vouches for, for analyses StatClaim has no contract for. Only its fit to the design is checked: the null and the design must describe the same model. Its result has the status 'declared', the weakest, and any plan that contains it reports that status.

- `declared_test(design: StudyDesign, null: Hypothesis, alpha: level, method: string, scope?: string, reference?: string) -> CitedAnalysis`
  A test you name and vouch for, when StatClaim has no contract for the analysis. method says what the test is. scope is finite_sample or asymptotic, and asymptotic if left out. reference is where the test is specified. Nothing about its guarantee is checked.

### `tests.t` — Cited analyses

Pooled-variance and Welch t-tests for two means. The compiler checks the null and the sampling plan against each test's contract. The Type I guarantee is cited from the literature and is not checked by Lean: exact under normality and equal variances for the pooled test, a large-sample approximation for Welch.

- `t_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided pooled-variance t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `t_test_one_sided(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  One-sided pooled-variance t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment - mean_control <= value or mean_treatment - mean_control >= value.
  Required null: mean_treatment - mean_control <= value or mean_treatment - mean_control >= value; same model required.
- `welch_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided Welch t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `welch_test_one_sided(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  One-sided Welch t-test. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment - mean_control <= value or mean_treatment - mean_control >= value.
  Required null: mean_treatment - mean_control <= value or mean_treatment - mean_control >= value; same model required.

### `tests.mixed_model` — Cited analyses

A test of a treatment contrast from a mixed model for repeated measures, such as the mean difference over all visits. The arm means in the null are the means of that contrast. The compiler checks the null and the sampling plan. The Type I guarantee is cited and is a large-sample approximation that also rests on the missing-data and model assumptions listed with each result.

- `mmrm_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided test of a treatment contrast in a mixed model for repeated measures. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `mmrm_test_one_sided(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  One-sided test of a treatment contrast in a mixed model for repeated measures. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment - mean_control <= value or mean_treatment - mean_control >= value.
  Required null: mean_treatment - mean_control <= value or mean_treatment - mean_control >= value; same model required.

### `tests.survival` — Cited analyses

The log-rank test for two survival curves. The compiler checks the null and the sampling plan against the test's contract. The Type I guarantee is cited from the literature and is a large-sample approximation in the number of events. Proportional hazards is not needed for the error rate; it matters for power.

- `log_rank(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided log-rank test. Its guarantee is cited from the literature and is not checked by Lean. Null: survival_treatment = survival_control at every time.
  Required null: survival_treatment = survival_control at every time; same model required.

### `tests.logistic` — Cited analyses

A Wald or likelihood-ratio test of the treatment coefficient in a logistic regression with covariates. The compiler checks the null and the sampling plan. The Type I guarantee is cited and is a large-sample approximation. The one-sided test supports a zero difference only: a margin on the proportion scale is not a statement about the coefficient.

- `logistic_regression(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided test of the treatment coefficient in a logistic regression. Its guarantee is cited from the literature and is not checked by Lean. Null: p_treatment = p_control.
  Required null: p_treatment = p_control; same model required.
- `logistic_regression_one_sided(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  One-sided test of the treatment coefficient in a logistic regression. Its guarantee is cited from the literature and is not checked by Lean. Null: p_treatment - p_control <= 0.
  Required null: p_treatment - p_control <= 0; same model required.

### `tests.cluster` — Cited analyses

The t-test on cluster-level summaries for a cluster-randomised trial: one value per cluster, a mean or a proportion of responders, with the clusters as the sample size. It needs cluster_assignment and at least four clusters per arm. The Type I guarantee is cited, exact if the cluster summaries are normal with a common variance, and not checked by Lean. For a proved analysis, use randomisation_test.

- `cluster_t_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided t-test on cluster-level summaries. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `cluster_proportion_t_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided t-test on cluster proportions. Its guarantee is cited from the literature and is not checked by Lean. Null: p_treatment = p_control.
  Required null: p_treatment = p_control; same model required.

### `models.two_arm_binomial` — Models and hypotheses

Two independent binomial arms, in one call or from an assignment and an outcome; equality, difference and inequality nulls; observations and the Type I and result claims shared by two-arm analyses.

- `two_arm_binomial(n_control: integer, n_treatment: integer, better?: string) -> Model`
  Two independent binomial arms. Shorthand for two_arm(assignment=assignment(n_control, n_treatment), outcome=binary_outcome(better)). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `assignment(n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  How participants are assigned to the two arms: the two arm sizes and, when declared, how the assignment was randomised. One assignment can be shared by several outcomes measured on the same participants. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `cluster_assignment(clusters_control: integer, clusters_treatment: integer, n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  Whole clusters, such as clinics or schools, are assigned to the arms, and everyone in a cluster gets the same arm. clusters_control and clusters_treatment count the clusters; n_control and n_treatment count the participants. Sites in a trial that randomises participants are not clusters: use assignment(...) there. Tests that assume independent participants are refused. With randomisation, the units are the clusters. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `stratum(control: integer, treatment: integer) -> Stratum`
  One stratum of a stratified or blocked assignment: how many randomised units, participants or clusters, it has in each arm.
- `binary_outcome(better?: string) -> Outcome`
  The binary outcome measured on each participant. Combine it with an assignment in two_arm(...). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `two_arm(assignment: Assignment, outcome: Outcome) -> Model`
  A two-arm model from an assignment and an outcome. A binary outcome gives the binomial model; any other outcome gives an OutcomeModel. The same pieces give the same model as the one-call constructors, such as two_arm_continuous.
- `equal_proportions(model: Model) -> Hypothesis`
  Null: p_treatment = p_control. This declares a restriction under which a guarantee is requested, not that the null is true.
- `proportion_difference(model: Model, value: number) -> Hypothesis`
  Null: p_treatment - p_control = value. The difference is absolute, not a relative percentage; value is exact and lies in [-1, 1]. A zero difference is the equal-proportions null.
- `proportion_difference_at_most(model: Model, value: number) -> Hypothesis`
  Null: p_treatment - p_control <= value. This is an inequality null, including when value=0; it is not the equality null supported by the current two-sided Fisher analysis.
- `observe(analysis: Analysis, control_successes: integer, treatment_successes: integer) -> Observation`
- `no_effect(model: Model) -> SharpNull`
  Sharp null: treatment changes no participant's outcome, so each participant would have the same outcome in either arm. It is stronger than equal means or proportions, and only randomisation_test supports it.
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

### `tests.randomisation` — Analyses and claims

Randomisation test of the sharp null that treatment changes no participant's outcome, for any two-arm model. Its level follows from the complete, stratified or blocked randomisation declared on the assignment; Lean proves it for every statistic fixed in advance. With clusters randomised, the test permutes clusters. Up to 10,000 randomised units and 1,000 strata or blocks.

- `randomisation_test(design: StudyDesign, null: Hypothesis, alpha: level, draws?: integer) -> RandomisationAnalysis`
  Randomisation test of the sharp null. Its level follows from the randomisation declared on the assignment, and Lean proves it for every test statistic fixed in advance; no distribution is assumed. With cluster_assignment the clusters are randomised, so the test permutes clusters. Without draws the p-value counts every possible assignment; with draws=B it compares the observed assignment with B drawn at random, which Lean also proves. The randomisation test supports only the sharp null no_effect(model=...). It does not test equal means or proportions: when effects differ between participants, its error under those nulls is not guaranteed. Keep your null if it states your question, and choose a test that supports it.
  Required null: treatment changes no participant's outcome (the sharp null); same model required.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.difference` — Analyses and claims

Exact test of p_treatment - p_control <= margin, for non-inferiority (negative margin) or superiority (zero). Its error bound covers the whole null. Up to 120 participants per arm.

- `difference_test(design: StudyDesign, null: Hypothesis, alpha: level) -> Analysis`
  The exact difference test rejects when the treatment's observed success proportion exceeds the control's by enough. Its null is proportion_difference_at_most(model=..., value=margin). A negative margin is a non-inferiority question; zero is superiority.
  Required null: p_treatment - p_control <= margin, for a margin strictly between -1 and 1; same model required.

### `multiplicity.bonferroni` — Multiplicity and composition

Bonferroni for two to twenty endpoints; dependence between them is unrestricted. A family of two-sided Fisher analyses is proved outright. Any other family, with one-sided, margin or cited tests, is conditional: Lean checks the combination and the members are assumed.

- `bonferroni(analyses: list, alpha: level, joint_law?: string) -> Family`
  Bonferroni: the members' levels may sum to at most alpha. Members may be exact tests, cited tests, designs with interim looks, sequences, graphs or other families; dependence between them is unrestricted. A family of two-sided Fisher analyses is proved outright. Any other family is conditional: Lean checks the combination and each member's own bound is assumed.
- `familywise(family: Family) -> FamilywiseClaim`

### `multiplicity.graphical` — Multiplicity and composition

A graphical procedure: each test starts with a share of the level and passes it on after a rejection. The contract checks the shares and transitions. The procedure's guarantee is cited, not checked by Lean.

- `graphical(analyses: list, weights: list, transitions: list, alpha: level) -> ComposedFamily`
  A graphical procedure with recycling. weights gives each test's starting share of alpha. Row i of transitions says how test i's level is shared among the others when it is rejected. Declare every test at the overall alpha. The procedure's guarantee is cited, not checked by Lean; the contract checks that the weights and transitions are valid.
- `familywise(family: Family) -> FamilywiseClaim`

### `multiplicity.fixed_sequence` — Multiplicity and composition

Hierarchical testing in a fixed order, each test at the full level and only after every earlier test rejected. Lean checks the combination; the tests' own bounds are assumed.

- `fixed_sequence(analyses: list, alpha: level) -> ComposedFamily`
  Hierarchical testing: the analyses are tested in the listed order, each at the full level alpha, and a test is carried out only if every earlier one rejected. An entry may be a test, a design with interim looks, or a family, sequence or graph; such an entry must be rejected in full before the next is tested. Lean checks the combination; each entry's own bound is assumed.
- `familywise(family: Family) -> FamilywiseClaim`

### `planning` — Study planning

Exact power at a planning point, target checks and a bounded sample-size search with equal or unequal allocation for the fixed Fisher analysis. Targets also apply to one-sample tests and two-stage designs. A size can be certified as sufficient or as the smallest in the declared range. Cited tests get approximate power from a normal formula, by calculation only.

- `binomial_rates(p_control: number, p_treatment: number) -> Rates`
  A planning point: one success probability per arm. It is an input for power, not the null and not an established fact.
- `mean_difference(value: number, sd: number) -> MeanDifference`
  A planning point for a continuous outcome: the true mean difference, treatment minus control, and the standard deviation of one participant's outcome on the analysed scale. For a mixed model, sd is the effective standard deviation of the contrast. Both are planning inputs.
- `hazard_ratio(value: number, events: integer) -> HazardRatio`
  A planning point for a survival outcome: the true hazard ratio, treatment over control, and the expected total number of events. Power depends on the events, not on the arm sizes. Both are planning inputs.
- `power_target(at: PlanningPoint, minimum: number, maximum_typeI: level) -> PowerTarget`
  Require power of at least minimum at one planning point, and a Type I error bound of at most maximum_typeI under the null. Power at this point is not a guarantee for other alternatives.
- `meets(analysis: Analysis, target: PowerTarget) -> PlanningClaim`
  Claim that this analysis meets every component of the target. calculate computes the components; verify must establish all. For a cited test, calculate gives approximate power and verify is refused.
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
| `verified` | Lean proved the guarantee for the procedure as declared, under the listed assumptions. It says nothing about how the study is run. Evidence grade `proved`. |
| `conditional` | Lean proved how the parts combine; each part's own guarantee is assumed. Like every status, it concerns the study as declared. Evidence grade `conditional`. |
| `cited` | The study fits a published method's contract; the guarantee is cited, not machine-checked. Evidence grade `cited`. |
| `declared` | The author named and vouched for the test or one of its parts. Nothing about that guarantee was checked or cited. Evidence grade `declared`. |
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
| `declared` | Every claim went through; the weakest part anywhere is a declared test. |
| `cited` | Every claim went through; the weakest part anywhere is cited. |
| `conditional` | Every claim went through; the weakest part is a proved combination of tests that are themselves provable. |
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
| `declared` | declared by the author; not checked and not cited | `author` | `contract` |

### Evidence source

| Value | Meaning |
| --- | --- |
| `lean_proof` | a proof in Lean |
| `literature` | a published result |
| `member_guarantees` | the members' own guarantees, each proved or cited separately |
| `simulation` | a simulation |
| `author` | the author's own statement, with no source known to StatClaim |

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
| `vouched` | The author vouches for it. StatClaim has no contract or source for it. |
| `approximation` | A simplification used to compute a number, such as a normal approximation. Not checkable from a declaration. |
| `meaning` | About what the declared quantities mean, such as which direction of the outcome is better. Checked only when the file declares it. |

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

### `assignment randomisation`

| Value | Meaning |
| --- | --- |
| `complete` | Every split of the units into arms of the declared sizes was equally likely. With cluster_assignment, the units are the clusters. |
| `stratified` | The same within each declared stratum, independently between strata. Needs strata=[stratum(control=..., treatment=...), ...] adding up to the arm sizes. |
| `blocked` | The same within each block of block_size units, independently between blocks, every block with its stratum's allocation. Needs block_size; strata optional. |

### `assignment population`

| Value | Meaning |
| --- | --- |
| `randomised` | Everyone randomised, analysed in the arm they were assigned to (intention to treat). Turns a randomisation test's analysed_as_randomised into a declaration. |
| `per_protocol` | Participants excluded after randomisation are left out; the arm sizes count those analysed. A randomisation test is refused; other claims say they cover this population only. |

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
| `condition` | Says which null, population or planning point the claim is about. |

## Cited methods

Guarantees taken from the literature. See [cited methods](cited-methods.md).

| Constructor | Version | Outcome | Null | Error rate | Scope | Minimum size | Power |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `t_test` | 1 | continuous | `equal_means` | equals alpha | `finite_sample` | 1 per arm, 3 total | `normal_two_means` |
| `t_test_one_sided` | 2 | continuous | `mean_difference_at_most` or `mean_difference_at_least` | at most alpha | `finite_sample` | 1 per arm, 3 total | `normal_two_means` |
| `welch_test` | 1 | continuous | `equal_means` | equals alpha | `asymptotic` | 2 per arm, 4 total | `normal_two_means` |
| `welch_test_one_sided` | 2 | continuous | `mean_difference_at_most` or `mean_difference_at_least` | at most alpha | `asymptotic` | 2 per arm, 4 total | `normal_two_means` |
| `mmrm_test` | 1 | continuous | `equal_means` | equals alpha | `asymptotic` | 2 per arm, 4 total | `normal_two_means` |
| `mmrm_test_one_sided` | 2 | continuous | `mean_difference_at_most` or `mean_difference_at_least` | at most alpha | `asymptotic` | 2 per arm, 4 total | `normal_two_means` |
| `log_rank` | 1 | survival | `equal_survival` | equals alpha | `asymptotic` | 1 per arm, 2 total | `schoenfeld_log_rank` |
| `logistic_regression` | 1 | binary | `equal_proportions` | equals alpha | `asymptotic` | 2 per arm, 4 total | `normal_two_proportions` |
| `logistic_regression_one_sided` | 1 | binary | `proportion_difference_at_most` | at most alpha | `asymptotic` | 2 per arm, 4 total | `normal_two_proportions` |
| `cluster_t_test` | 1 | continuous | `equal_means` | equals alpha | `finite_sample` | 4 clusters per arm, 8 total | none |
| `cluster_proportion_t_test` | 1 | binary | `equal_proportions` | equals alpha | `finite_sample` | 4 clusters per arm, 8 total | none |

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

**`mmrm_test`** (Two-sided test of a treatment contrast in a mixed model for repeated measures) assumes `independent_participants`, `fixed_sample_sizes`, `single_analysis`, `missing_at_random`, `correct_mean_model`, `covariance_structure`, `approximately_normal_estimate`. References:

- Laird, N. M. and Ware, J. H. (1982). Random-effects models for longitudinal data. Biometrics 38(4), 963-974.
- Kenward, M. G. and Roger, J. H. (1997). Small sample inference for fixed effects from restricted maximum likelihood. Biometrics 53(3), 983-997.
- Mallinckrodt, C. H., Lane, P. W., Schnell, D., Peng, Y. and Mancuso, J. P. (2008). Recommendations for the primary analysis of continuous endpoints in longitudinal clinical trials. Drug Information Journal 42(4), 303-319.

**`mmrm_test_one_sided`** (One-sided test of a treatment contrast in a mixed model for repeated measures) assumes `independent_participants`, `fixed_sample_sizes`, `single_analysis`, `missing_at_random`, `correct_mean_model`, `covariance_structure`, `approximately_normal_estimate`. References:

- Laird, N. M. and Ware, J. H. (1982). Random-effects models for longitudinal data. Biometrics 38(4), 963-974.
- Kenward, M. G. and Roger, J. H. (1997). Small sample inference for fixed effects from restricted maximum likelihood. Biometrics 53(3), 983-997.
- Mallinckrodt, C. H., Lane, P. W., Schnell, D., Peng, Y. and Mancuso, J. P. (2008). Recommendations for the primary analysis of continuous endpoints in longitudinal clinical trials. Drug Information Journal 42(4), 303-319.

**`log_rank`** (Two-sided log-rank test) assumes `independent_observations`, `independent_censoring`, `prespecified_analysis_time`, `single_analysis`. References:

- Mantel, N. (1966). Evaluation of survival data and two new rank order statistics arising in its consideration. Cancer Chemotherapy Reports 50(3), 163-170.
- Peto, R. and Peto, J. (1972). Asymptotically efficient rank invariant test procedures. Journal of the Royal Statistical Society A 135(2), 185-207.
- Fleming, T. R. and Harrington, D. P. (1991). Counting Processes and Survival Analysis. Wiley.

**`logistic_regression`** (Two-sided test of the treatment coefficient in a logistic regression) assumes `independent_participants`, `fixed_sample_sizes`, `single_analysis`, `logit_linear`, `null_is_zero_coefficient`, `enough_events`. References:

- Cox, D. R. (1958). The regression analysis of binary sequences. Journal of the Royal Statistical Society B 20(2), 215-242.
- Hosmer, D. W., Lemeshow, S. and Sturdivant, R. X. (2013). Applied Logistic Regression, 3rd ed. Wiley.

**`logistic_regression_one_sided`** (One-sided test of the treatment coefficient in a logistic regression) assumes `independent_participants`, `fixed_sample_sizes`, `single_analysis`, `logit_linear`, `null_is_zero_coefficient`, `enough_events`. References:

- Cox, D. R. (1958). The regression analysis of binary sequences. Journal of the Royal Statistical Society B 20(2), 215-242.
- Hosmer, D. W., Lemeshow, S. and Sturdivant, R. X. (2013). Applied Logistic Regression, 3rd ed. Wiley.

**`cluster_t_test`** (Two-sided t-test on cluster-level summaries) assumes `independent_clusters`, `fixed_sample_sizes`, `single_analysis`, `normal_cluster_summaries`. References:

- Donner, A. and Klar, N. (2000). Design and Analysis of Cluster Randomization Trials in Health Research. Arnold, London. [to verify]
- Hayes, R. J. and Moulton, L. H. (2017). Cluster Randomised Trials, 2nd ed. Chapman and Hall/CRC, Boca Raton. [to verify]

**`cluster_proportion_t_test`** (Two-sided t-test on cluster proportions) assumes `independent_clusters`, `fixed_sample_sizes`, `single_analysis`, `normal_cluster_proportions`. References:

- Donner, A. and Klar, N. (2000). Design and Analysis of Cluster Randomization Trials in Health Research. Arnold, London. [to verify]
- Hayes, R. J. and Moulton, L. H. (2017). Cluster Randomised Trials, 2nd ed. Chapman and Hall/CRC, Boca Raton. [to verify]

### Power formulas

Approximate power for cited tests, by calculation only. See [power for cited tests](planning.md#power-for-cited-tests).

| Formula | Version | Planning point | Assumes |
| --- | --- | --- | --- |
| `normal_two_means` | 2 | `mean_difference` | `normal_approximation_power`, `planning_standard_deviation` |
| `schoenfeld_log_rank` | 2 | `hazard_ratio` | `normal_approximation_power`, `proportional_hazards`, `planning_events`, `at_risk_shares` |
| `normal_two_proportions` | 2 | `binomial_rates` | `normal_approximation_power`, `unadjusted_proportions` |

**`normal_two_means`** (Difference of two means, normal approximation with a known standard deviation). References:

- Chow, S.-C., Shao, J. and Wang, H. (2008). Sample Size Calculations in Clinical Research, 2nd ed. Chapman and Hall/CRC. Chapter 3.
- Julious, S. A. (2004). Sample sizes for clinical trials with normal data. Statistics in Medicine 23(12), 1921-1986.

**`schoenfeld_log_rank`** (Log-rank test, Schoenfeld's formula in the number of events). References:

- Schoenfeld, D. (1981). The asymptotic properties of nonparametric tests for comparing survival distributions. Biometrika 68(1), 316-319.
- Schoenfeld, D. A. (1983). Sample-size formula for the proportional-hazards regression model. Biometrics 39(2), 499-503.

**`normal_two_proportions`** (Difference of two proportions, normal approximation). References:

- Fleiss, J. L., Levin, B. and Paik, M. C. (2003). Statistical Methods for Rates and Proportions, 3rd ed. Wiley. Chapter 4.
- R Core Team. power.prop.test, in the stats package of R.

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
| `prespecified_graph` | design | The tests, their starting shares of the level and the rules for passing a share on are fixed in advance, and a share is passed on only after a rejection. Each test controls its error at every level up to the overall level, not only at one. |
| `declared_test_is_valid` | vouched | The declared test rejects its true null with probability at most its level. StatClaim has no contract or source for this test. |
| `independent_participants` | sampling | Participants are independent of one another. Measurements on one participant may be correlated. |
| `independent_clusters` | sampling | Clusters are independent of one another. Participants in one cluster may be correlated. |
| `normal_cluster_summaries` | distribution | Each cluster's summary, such as its mean outcome, is normally distributed with the same variance in both arms. Clusters of very different sizes make this doubtful. |
| `normal_cluster_proportions` | distribution | Each cluster's proportion of responders is close enough to normally distributed, with the same variance in both arms, for a t-test. Small clusters, rare or very common responses, and clusters of very different sizes make this doubtful. |
| `missing_at_random` | sampling | Missing measurements are missing at random given the observed data and the model. |
| `correct_mean_model` | distribution | The model for the mean, with its covariates, is fixed in advance and correctly specified. |
| `covariance_structure` | distribution | The covariance between a participant's measurements is correctly specified. An unstructured matrix imposes no structure. |
| `approximately_normal_estimate` | distribution | Errors are multivariate normal, or the study is large enough for the estimated treatment contrast to be approximately normal. |
| `logit_linear` | distribution | The log odds of response are linear in the model's covariates, which are fixed in advance. |
| `null_is_zero_coefficient` | scope | The test is of the treatment coefficient. Under the declared null, treatment has no effect on response given the covariates. |
| `enough_events` | distribution | There are enough responders and non-responders in each arm for the estimated coefficient to be approximately normal, with no separation. |
| `higher_is_better` | meaning | Higher values of the outcome are better: the one-sided null asks whether the treatment's are higher. The file does not say so; declare better="higher" on the model to have this checked. |
| `lower_is_better` | meaning | Lower values of the outcome are better: the one-sided null asks whether the treatment's are lower. The file does not say so; declare better="lower" on the model to have this checked. |
| `randomised_population` | scope | The bound covers the randomised population: everyone randomised, analysed in the arm they were assigned to, as the assignment declares. |
| `per_protocol_population` | scope | The bound covers the per-protocol population only, as the assignment declares: participants excluded after randomisation are left out. Randomisation does not make the arms' remaining groups comparable, so a difference between them need not be caused by treatment. |
| `normal_approximation_power` | approximation | Power comes from a normal approximation to the test statistic, with its variance at the planning values. It is an approximation, not a bound. |
| `planning_standard_deviation` | scope | The standard deviation is a planning input, not an established fact. It is the standard deviation of one participant's outcome on the analysed scale; for a mixed model, the effective standard deviation of the contrast. |
| `unadjusted_proportions` | approximation | Power is for an unadjusted comparison of two proportions. Covariates in the analysis model change it. |
| `proportional_hazards` | distribution | The hazard ratio is constant over time. The log-rank test's error rate does not need this; its power formula does. |
| `planning_events` | scope | The number of events is a planning input, not an established fact. Power depends on the events, not on the arm sizes. |
| `at_risk_shares` | approximation | Each arm's share of the participants at risk stays close to its share at randomisation, as when the hazard ratio is near 1. |
| `accounts_for_repeated_measures` | vouched | The declared test accounts for the several measurements on each participant, which may be correlated. |
| `accounts_for_clusters` | vouched | The declared test accounts for randomisation by cluster: participants in one cluster may be correlated. |

## Limits

| Quantity | Supported |
| --- | --- |
| Analyses in a family, or looks in a sequential design | 2 to 20 |
| Participants per arm, exact test with a margin | up to 120 |
| Participants per arm, Fisher planning search | up to 500 |
| Participants per arm, cited-test planning search | up to 100000 |
| Allocation ratio in a planning search | 1 to 10 |
| Participants, one-sample binomial test | up to 1000 |
| Randomised units, participants or clusters, randomisation test | up to 10000 |
| Strata or blocks, randomisation test | up to 1000 |
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
| `no_power_formula` | error | A cited or declared test with no power formula is planned. |
| `direction_mismatch` | error | A one-sided null asks about the direction the model's better= does not call better. |
| `unit_mismatch` | error | The test's unit does not fit the declared design: it assumes independent participants or observations where clusters or repeated measurements are declared, or it takes one summary per cluster where participants were randomised. |
| `undeclared_randomisation` | error | A randomisation test is declared on an assignment that does not say how it was randomised. |
| `population_mismatch` | error | A randomisation test is declared on an assignment whose analysis leaves out randomised units (population="per_protocol"). |
| `never_rejects` | error | A randomisation test has too few equally likely splits to reach its level, so it could never reject. |
| `planning_point` | error | The planning point does not fit the analysis. |
| `rule_mismatch` | error | A stopping rule does not fit the two-stage design. |
| `sampling_contract` | error | A joint law is given where none applies, or is not supported. |
| `family_size` | error | A family or sequential design has too few or too many entries. |
| `duplicate_analysis` | error | A family or sequential design lists an analysis twice. |
| `sequential_question` | error | The looks of a sequential design differ in test or null. |
| `sequence_level` | error | A test in a fixed sequence or a graph is not declared at the overall level. |
| `graph_definition` | error | The weights or transitions of a graph are not valid. |
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
