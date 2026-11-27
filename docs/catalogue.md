# Language reference and catalogue

Generated from the language registries. Update with `uv run python scripts/update_catalogue.py`; CI checks for drift.

All APIs are preview APIs. Object availability does not imply a proof adapter. See [scope](scope.md) for supported guarantees and the [language guide](stat-language.md) for a walkthrough.

Contents: [grammar](#grammar), [value types](#value-types), [objects](#objects), [modules and constructors](#modules), [operations](#built-in-operations), [statuses and other fixed values](#statuses-and-other-fixed-values), [cited methods](#cited-methods), [assumptions](#assumptions), [limits](#limits), [diagnostic codes](#diagnostic-codes).

## Grammar

```ebnf
file        = { statement NEWLINE } ;
statement   = "use" module
            | "let" NAME "=" expression
            | operation ;                      (* verify, calculate or simulate *)
operation   = ( "verify" | "calculate" ) "(" expression ")"
            | ( "verify" | "calculate" ) expression       (* older spelling *)
            | "simulate" "(" expression "," arguments ")" ;   (* seed, and runs *)
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
| Assignment | How participants reach the two arms: the arm sizes, clusters and, when declared, the randomisation. Shared by outcomes on the same participants. | `n_control: integer`, `n_treatment: integer`, `randomisation: Option[string]`, `block_size: Option[integer]`, `population: Option[string]` |
| Outcome | What is measured on each participant: its kind and which direction is better. | `kind: string`, `better: Option[string]`, `name: Option[string]` |
| Model | Two binomial arms: an assignment and a binary outcome. | `assignment: Assignment`, `outcome: Outcome`, `n_control: integer`, `n_treatment: integer`, `better: Option[string]` |
| StudyDesign | Model with a stopping rule. | `model: Model`, `stopping: string` |
| Hypothesis | A null restriction, not an assertion of truth. | `model: Model`, `predicate: string`, `value: exact number`, `statement: string` |
| Analysis | Design, compatible null and exact alpha. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number` |
| WaldAnalysis | Design, equality null, squared Wald critical value and requested finite-sample error ceiling. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number`, `squared_cutoff: exact number` |
| ScoreAnalysis | Design, equality null, squared score critical value and requested finite-sample error ceiling. | `design: StudyDesign`, `null: Hypothesis`, `alpha: exact number`, `squared_cutoff: exact number` |
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
| Reestimation | Student's t-test with its size per arm re-estimated from the blinded interim variance. | `analysis: CitedAnalysis`, `interim_per_arm: integer`, `initial_per_arm: integer`, `max_per_arm: integer`, `difference: exact number`, `power: exact number` |
| TwoStageModel | Stage sizes of a single-arm design. | `n_stage1: integer`, `n_stage2: integer` |
| TwoStageObservation | Observed counts, with stage two only if the study continued. | `analysis: TwoStageAnalysis`, `stage1_responses: integer`, `stage2_responses: Option[integer]` |
| Prior | Beta prior with positive integer parameters. | `a: integer`, `b: integer` |
| Rule | Interim continuation and final decision rule. | `kind: string` |
| TwoStageAnalysis | Complete policy: stages, rule and the null response rate. | `design: TwoStageModel`, `rule: Rule`, `null_rate: exact number` |

### Planning objects

| Object | Meaning | Public fields |
| --- | --- | --- |
| Rates | Planning point for two arms; an input, not a fact. | `p_control: exact number`, `p_treatment: exact number`, `icc: Option[exact number]`, `cluster_size_cv: Option[exact number]` |
| Rate | Planning point for a single response rate. | `value: exact number` |
| MeanDifference | Planning point for a continuous outcome: a mean difference and an SD. | `value: exact number`, `sd: exact number`, `icc: Option[exact number]`, `cluster_size_cv: Option[exact number]`, `sd_treatment: Option[exact number]`, `skewness: Option[exact number]` |
| HazardRatio | Planning point for a survival outcome: a hazard ratio and a number of events. | `value: exact number`, `events: integer` |
| Correlation | Planning point for two continuous variables. | `value: exact number`, `skewness: Option[exact number]`, `exposure_skewness: Option[exact number]` |
| OutcomeMeans | Planning point for a measured outcome by a yes-or-no exposure: two means and an SD. | `unexposed: exact number`, `exposed: exact number`, `sd: exact number`, `exposed_share: Option[exact number]`, `design_effect: Option[exact number]` |
| OddsPerSd | Planning point for logistic regression on a measured exposure: odds ratio per SD. | `odds_ratio: exact number`, `baseline: exact number`, `exposure_r2: Option[exact number]`, `design_effect: Option[exact number]` |
| Slope | Planning point for a linear regression: a slope and two standard deviations. | `value: exact number`, `exposure_sd: exact number`, `residual_sd: exact number`, `exposure_r2: Option[exact number]`, `design_effect: Option[exact number]`, `skewness: Option[exact number]`, `exposure_skewness: Option[exact number]` |
| ExponentialSurvival | Planning point for a survival outcome given by times: hazard ratio, median, accrual. | `hazard_ratio: exact number`, `control_median: exact number`, `accrual: exact number`, `follow_up: exact number`, `dropout: Option[exact number]`, `dropout_time: Option[exact number]`, `effect_delay: Option[exact number]` |
| Risks | Planning point for a cohort: the risk without and with exposure; an input, not a fact. | `unexposed: exact number`, `exposed: exact number`, `exposed_share: Option[exact number]` |
| ExposurePrevalence | Planning point for a case-control study: the share of controls and of cases exposed. | `controls: exact number`, `cases: exact number` |
| GroupCandidates | Cohort or case-control designs searched by the number exposed or of cases. | `analysis: AssociationAnalysis`, `min_size: integer`, `max_size: integer`, `ratio: integer` |
| OutcomePrevalence | Planning point for a cross-sectional study: prevalence by exposure, and share exposed. | `unexposed: exact number`, `exposed: exact number`, `exposed_share: exact number`, `design_effect: Option[exact number]` |
| TotalCandidates | Studies that fix only their total, searched by the total; sufficiency only. | `analysis: Analysis`, `min_n: integer`, `max_n: integer` |
| DiscordantPairs | Planning point for a matched study: the share of discordant pairs and the odds ratio. | `share: exact number`, `odds_ratio: exact number` |
| IncidenceRates | Planning point for a person-time cohort: the rate ratio, person-time and events. | `rate_ratio: exact number`, `exposed_time: exact number`, `unexposed_time: exact number`, `events: Option[integer]` |
| ClusterCandidates | Cluster-randomised trials searched by clusters per arm or by cluster size. | `analysis: Analysis`, `min_size: integer`, `max_size: integer`, `cluster_size: Option[integer]` |
| CountCandidates | Matched studies searched by their pairs, or the rate test by its events. | `analysis: Analysis`, `min_size: integer`, `max_size: integer` |
| SingleProportion | Planning point for one proportion, such as a prevalence. | `value: exact number`, `design_effect: Option[exact number]`, `population_size: Option[integer]` |
| PrecisionTarget | Required margin of error of an interval, absolute or relative, with an optional assurance. | `at: PlanningPoint`, `level: exact number`, `margin_of_error: Option[exact number]`, `relative_margin_of_error: Option[exact number]`, `assurance: Option[exact number]` |
| PlannedInterval | An interval a study plans to report, for a precision target. | `model: EstimableModel`, `measure: string`, `method: string`, `group: Option[string]` |
| IntervalCandidates | Sizes searched for a planned interval. | `interval: PlannedInterval`, `min_size: integer`, `max_size: integer`, `ratio: integer` |
| PowerTarget | Required power at a point and a Type I bound. | `at: PlanningPoint`, `minimum: exact number`, `maximum_typeI: exact number` |
| EndpointPoints | One planning point per member of a family, and the correlation between endpoints. | `endpoints: list`, `correlation: exact number` |
| NullScenarios | Points at the null where a simulated Type I error is judged, for a design whose level is not proved. | `scenarios: list` |
| Feasibility | One analysis assessed against one target. | `analysis: Analysis`, `target: Target` |
| Candidates | Finite equal-arm design space for a search. | `analysis: Analysis`, `min_per_arm: integer`, `max_per_arm: integer`, `ratio: integer` |
| Sizing | Candidates searched for a design meeting a target. | `candidates: Candidates`, `target: Target` |
| OneArmCandidates | Sample sizes searched for a one-sample test. | `analysis: OneSampleAnalysis`, `min_n: integer`, `max_n: integer` |
| TwoStageCandidates | Two-stage designs searched by an optimal or minimax criterion. | `null_rate: exact number`, `max_total: integer`, `criterion: string` |
| LookCandidates | Designs with looks whose look sizes are searched freely, ranked by a minimax or optimal criterion. | `min_per_arm: integer`, `max_per_arm: integer`, `step: integer`, `criterion: string` |

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
| RateResultDetails | Exact p-value and decision of the rate test for observed events. | `events: integer`, `p_value: exact number`, `alpha: exact number`, `reject_null: boolean`, `test: string` |
| MatchedResultDetails | Exact p-value and decision of McNemar's test for observed pairs. | `discordant_pairs: integer`, `p_value: exact number`, `alpha: exact number`, `reject_null: boolean`, `test: string` |
| AssociationResultDetails | Exact p-value and decision of Fisher's test for an observed table. | `p_value: exact number`, `observed_table_probability: exact number`, `alpha: exact number`, `reject_null: boolean`, `test: string` |
| EffectIntervalDetails | An effect measure's interval, estimate and the level used per group. | `measure: string`, `level: exact number`, `arm_level: exact number`, `estimate: Option[exact number]`, `lower: exact number`, `upper: Option[exact number]`, `method: string` |
| AssociationPowerDetails | Group sizes, the planning point's measures and the exact power of Fisher's test of association; not proof evidence. | `design: Option[string]`, `exposed: Option[integer]`, `unexposed: Option[integer]`, `cases: Option[integer]`, `controls: Option[integer]`, `total_sample_size: Option[integer]`, `risk_ratio: Option[exact number]`, `risk_difference: Option[exact number]`, `prevalence_ratio: Option[exact number]`, `prevalence_difference: Option[exact number]`, `exposed_share: Option[exact number]`, `expected_exposed: Option[exact number]`, `odds_ratio: Option[exact number]`, `power: Option[exact number]`, `power_target_met: boolean`, `typeI_bound: Option[exact number]`, `typeI_target_met: Option[boolean]`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| MatchedPowerDetails | Pairs, the planning point and the exact power of McNemar's test; not proof evidence. | `pairs: Option[integer]`, `discordant: Option[exact number]`, `odds_ratio: Option[exact number]`, `case_exposed_share: Option[exact number]`, `expected_discordant_pairs: Option[exact number]`, `power: Option[exact number]`, `power_target_met: boolean`, `typeI_bound: Option[exact number]`, `typeI_target_met: Option[boolean]`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| RatePowerDetails | Events, the planning point and the exact power of the rate test; not proof evidence. | `events: Option[integer]`, `rate_ratio: Option[exact number]`, `exposed_time_share: Option[exact number]`, `exposed_event_share: Option[exact number]`, `power: Option[exact number]`, `power_target_met: boolean`, `typeI_bound: Option[exact number]`, `typeI_target_met: Option[boolean]`, `candidates_evaluated: Option[integer]`, `minimum_sample_size_claim: Option[string]` |
| PrecisionDetails | Margin of error of a planned interval at the expected counts, and its assurance; a calculation. | `total_sample_size: Option[integer]`, `n_control: Option[integer]`, `n_treatment: Option[integer]`, `exposed: Option[integer]`, `unexposed: Option[integer]`, `cases: Option[integer]`, `controls: Option[integer]`, `pairs: Option[integer]`, `events: Option[integer]`, `measure: Option[string]`, `method: Option[string]`, `level: Option[exact number]`, `estimate: Option[exact number]`, `lower: Option[exact number]`, `upper: Option[exact number]`, `relative: Option[boolean]`, `margin_achieved: Option[exact number]`, `target_margin: Option[exact number]`, `assurance: Option[exact number]`, `minimum_assurance: Option[exact number]`, `precision_target_met: boolean`, `candidates_evaluated: Option[integer]`, `note: Option[string]` |
| ApproximatePowerDetails | Approximate power and critical estimate of a cited test; not a bound. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `clusters_control: Option[integer]`, `clusters_treatment: Option[integer]`, `total_clusters: Option[integer]`, `cluster_size_control: Option[exact number]`, `cluster_size_treatment: Option[exact number]`, `icc: Option[exact number]`, `design_effect: Option[exact number]`, `degrees_of_freedom: Option[integer]`, `covariates: Option[integer]`, `effective_sample_size: Option[exact number]`, `typeI_at_control_rate: Option[exact number]`, `exposed: Option[integer]`, `unexposed: Option[integer]`, `cases: Option[integer]`, `controls: Option[integer]`, `pairs: Option[integer]`, `events: Option[integer]`, `expected_events: Option[exact number]`, `event_probability_control: Option[exact number]`, `event_probability_treatment: Option[exact number]`, `power: Option[exact number]`, `power_ceiling: Option[exact number]`, `power_target_met: boolean`, `power_settled: Option[boolean]`, `critical_estimate: Option[exact number]`, `reject_when: Option[string]`, `standard_error: Option[exact number]`, `alpha: Option[exact number]`, `typeI_target_met: Option[boolean]`, `formula: Option[string]`, `candidates_evaluated: Option[integer]` |
| LooksPowerDetails | Exact power of Fisher's test at interim looks, the expected size and the exact Type I at the control rate; a calculation. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `power: Option[exact number]`, `power_target_met: boolean`, `power_settled: Option[boolean]`, `expected_sample_size: Option[exact number]`, `expected_sample_size_null: Option[exact number]`, `typeI_at_control_rate: Option[exact number]`, `alpha: Option[exact number]`, `typeI_target_met: Option[boolean]`, `criterion: Option[string]`, `candidates: Option[integer]`, `candidates_evaluated: Option[integer]`, `feasible: Option[integer]` |
| SimulationDetails | Power and Type I error estimated by simulate(...), with 95% intervals, the number of runs and the seed. Estimates, not bounds and not evidence. | `n_control: Option[integer]`, `n_treatment: Option[integer]`, `total_sample_size: Option[integer]`, `power: Option[exact number]`, `power_lower: Option[exact number]`, `power_upper: Option[exact number]`, `power_target_met: boolean`, `typeI: Option[exact number]`, `typeI_lower: Option[exact number]`, `typeI_upper: Option[exact number]`, `alpha: Option[exact number]`, `typeI_target_met: Option[boolean]`, `runs: Option[integer]`, `seed: Option[integer]`, `candidates_evaluated: Option[integer]`, `clusters_control: Option[integer]`, `clusters_treatment: Option[integer]`, `total_clusters: Option[integer]`, `cluster_size_control: Option[exact number]`, `cluster_size_treatment: Option[exact number]`, `icc: Option[exact number]`, `cluster_size_cv: Option[exact number]`, `degrees_of_freedom: Option[integer]`, `expected_sample_size: Option[exact number]`, `expected_sample_size_null: Option[exact number]`, `initial_per_arm: Option[integer]`, `interim_per_arm: Option[integer]`, `max_per_arm: Option[integer]`, `power_any: Option[exact number]`, `power_all: Option[exact number]`, `typeI_judged: Option[boolean]` |
| Diagnostic | A diagnostic code, severity and message. | `code: string`, `message: string`, `severity: string` |

### Observational studies

| Object | Meaning | Public fields |
| --- | --- | --- |
| CrossSectionalStudy | A sample from one population with exposure and outcome measured at once; only the total is fixed. | `n: integer`, `exposure: string`, `outcome: string`, `exposure_scale: string`, `outcome_scale: string`, `survey: string`, `clusters: Option[integer]` |
| CohortStudy | Participants followed from exposure to outcome, with the groups or only the total fixed. | `exposed: Option[integer]`, `unexposed: Option[integer]`, `n: Option[integer]`, `exposure: string`, `outcome: string`, `exposure_scale: string`, `outcome_scale: string`, `survey: string`, `clusters: Option[integer]` |
| CaseControlStudy | Cases and controls sampled in fixed numbers; estimates odds ratios only. | `cases: integer`, `controls: integer`, `exposure: string`, `outcome: string`, `exposure_scale: string`, `outcome_scale: string`, `survey: string`, `clusters: Option[integer]` |
| AssociationNull | No association between exposure and outcome: an odds ratio of 1. | `model: Model`, `predicate: string`, `statement: string` |
| PersonTimeStudy | A cohort followed over person-time; it measures incidence rates. | `exposure: string`, `outcome: string`, `exposure_scale: string`, `outcome_scale: string`, `survey: string`, `clusters: Option[integer]` |
| RateAnalysis | The exact test of equal incidence rates, given the total events. | `design: StudyDesign`, `null: AssociationNull`, `alpha: exact number`, `guarantee: Guarantee` |
| ObservedEvents | Events and person-time in the exposed and unexposed groups. | `model: PersonTimeStudy`, `exposed_events: integer`, `exposed_time: exact number`, `unexposed_events: integer`, `unexposed_time: exact number` |
| RateResult | The rate test applied to observed events. | `analysis: RateAnalysis`, `events: ObservedEvents` |
| RateRatio | An interval for the incidence rate ratio. | `events: ObservedEvents`, `level: exact number` |
| Proportion | Prevalence or cumulative incidence with its exact interval. | `measure: string`, `model: Model`, `cases: integer`, `level: exact number`, `group: Option[string]` |
| MatchedStudy | A 1:1 matched case-control study: pairs of one case and one control. | `pairs: integer`, `exposure: string`, `outcome: string`, `exposure_scale: string`, `outcome_scale: string`, `survey: string`, `clusters: Option[integer]` |
| MatchedAnalysis | McNemar's exact test of no association within matched pairs. | `design: StudyDesign`, `null: AssociationNull`, `alpha: exact number`, `guarantee: Guarantee` |
| MatchedPairs | Observed pairs by who was exposed: both, only the case, only the control, neither. | `model: MatchedStudy`, `both_exposed: integer`, `case_exposed_only: integer`, `control_exposed_only: integer`, `neither_exposed: integer` |
| MatchedResult | McNemar's test applied to observed pairs. | `analysis: MatchedAnalysis`, `pairs: MatchedPairs` |
| MatchedInterval | An interval for the conditional odds ratio of a matched study. | `pairs: MatchedPairs`, `level: exact number` |
| CitedAssociation | A cited test of no association: regression with covariates, correlation or a survey analysis. | `design: StudyDesign`, `null: AssociationNull`, `alpha: exact number`, `adjusted_for: list`, `guarantee: Guarantee` |
| AssociationTable | An observed 2x2 table: exposed and unexposed cases and noncases. | `model: Model`, `exposed_cases: integer`, `exposed_noncases: integer`, `unexposed_cases: integer`, `unexposed_noncases: integer` |
| AssociationResult | Fisher's test applied to an observed table. | `analysis: AssociationAnalysis`, `table: AssociationTable` |
| EffectInterval | An interval for an effect measure the design can estimate. | `measure: string`, `table: AssociationTable`, `level: exact number` |
| AssociationAnalysis | Fisher's exact test of no association, with an exact alpha. | `design: StudyDesign`, `null: AssociationNull`, `alpha: exact number`, `guarantee: Guarantee` |

Claim constructors return `TypeIClaim`, `ResultClaim`, `FamilywiseClaim` or `PlanningClaim`, all represented by Claim. Exact numbers, strings, booleans and lists are value types. Optional evidence stays optional through field access.

## Modules

`use` imports built-in constructors; it does not load arbitrary files or plugins. Arguments may be given by position or by name. A `?` marks an argument that may be left out.

### `models.two_arm_continuous` — Models and hypotheses

Two arms with a continuous outcome; equal-means and mean-difference nulls. Fixes no distribution.

- `two_arm_continuous(n_control: integer, n_treatment: integer, better?: string, population?: string, name?: string) -> OutcomeModel`
  Two arms with a continuous outcome, such as a change in blood pressure. The model fixes no distribution; each test states the one it assumes. Shorthand for two_arm(assignment=assignment(n_control, n_treatment, population), outcome=continuous_outcome(better, name)); population and name mean the same as there. better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `assignment(n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  How participants are assigned to the two arms: the two arm sizes and, when declared, how the assignment was randomised. One assignment can be shared by several outcomes measured on the same participants. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `cluster_assignment(clusters_control: integer, clusters_treatment: integer, n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  Whole clusters, such as clinics or schools, are assigned to the arms, and everyone in a cluster gets the same arm. clusters_control and clusters_treatment count the clusters; n_control and n_treatment count the participants. Sites in a trial that randomises participants are not clusters: use assignment(...) there. Tests that assume independent participants are refused. With randomisation, the units are the clusters. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `stratum(control: integer, treatment: integer) -> Stratum`
  One stratum of a stratified or blocked assignment: how many randomised units, participants or clusters, it has in each arm.
- `continuous_outcome(better?: string, measurements?: integer, name?: string) -> Outcome`
  The continuous outcome measured on each participant. Combine it with an assignment in two_arm(...). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption. measurements is how many times the outcome is measured on each participant, 1 if left out. With more than one, tests that take one value per participant are refused. name labels the outcome, such as "response". One name is one outcome: models that share it must agree on its kind and better. A family, sequence or graph that asks the same question of a named outcome twice, the same test of the same null on the same participants, is refused.
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

- `two_arm_survival(n_control: integer, n_treatment: integer, better?: string, population?: string, name?: string) -> OutcomeModel`
  Two arms followed for the time until an event, such as death or relapse. Some participants may be censored: followed without the event being seen. The model fixes no distribution; each test states the one it assumes. Shorthand for two_arm(assignment=assignment(n_control, n_treatment, population), outcome=survival_outcome(better, name)); population and name mean the same as there. better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `assignment(n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  How participants are assigned to the two arms: the two arm sizes and, when declared, how the assignment was randomised. One assignment can be shared by several outcomes measured on the same participants. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `cluster_assignment(clusters_control: integer, clusters_treatment: integer, n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  Whole clusters, such as clinics or schools, are assigned to the arms, and everyone in a cluster gets the same arm. clusters_control and clusters_treatment count the clusters; n_control and n_treatment count the participants. Sites in a trial that randomises participants are not clusters: use assignment(...) there. Tests that assume independent participants are refused. With randomisation, the units are the clusters. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `stratum(control: integer, treatment: integer) -> Stratum`
  One stratum of a stratified or blocked assignment: how many randomised units, participants or clusters, it has in each arm.
- `survival_outcome(better?: string, name?: string) -> Outcome`
  The survival outcome measured on each participant. Combine it with an assignment in two_arm(...). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption. name labels the outcome, such as "response". One name is one outcome: models that share it must agree on its kind and better. A family, sequence or graph that asks the same question of a named outcome twice, the same test of the same null on the same participants, is refused.
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

The t-test on cluster-level summaries for a cluster-randomised trial: one value per cluster, a mean or a proportion of responders, with the clusters as the sample size. It needs cluster_assignment and at least four clusters per arm. The Type I guarantee is cited, exact if the cluster summaries are normal with a common variance, and not checked by Lean. Power comes from the noncentral t, given the intracluster correlation. For a proved analysis, use randomisation_test.

- `cluster_t_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided t-test on cluster-level summaries. Its guarantee is cited from the literature and is not checked by Lean. Null: mean_treatment = mean_control.
  Required null: mean_treatment = mean_control; same model required.
- `cluster_proportion_t_test(design: StudyDesign, null: Hypothesis, alpha: level) -> CitedAnalysis`
  Two-sided t-test on cluster proportions. Its guarantee is cited from the literature and is not checked by Lean. Null: p_treatment = p_control.
  Required null: p_treatment = p_control; same model required.

### `models.two_arm_binomial` — Models and hypotheses

Two independent binomial arms, in one call or from an assignment and an outcome; equality, difference and inequality nulls; observations and the Type I and result claims shared by two-arm analyses.

- `two_arm_binomial(n_control: integer, n_treatment: integer, better?: string, population?: string, name?: string) -> Model`
  Two independent binomial arms. Shorthand for two_arm(assignment=assignment(n_control, n_treatment, population), outcome=binary_outcome(better, name)); population and name mean the same as there. better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption.
- `assignment(n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  How participants are assigned to the two arms: the two arm sizes and, when declared, how the assignment was randomised. One assignment can be shared by several outcomes measured on the same participants. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `cluster_assignment(clusters_control: integer, clusters_treatment: integer, n_control: integer, n_treatment: integer, randomisation?: string, strata?: list, block_size?: integer, population?: string) -> Assignment`
  Whole clusters, such as clinics or schools, are assigned to the arms, and everyone in a cluster gets the same arm. clusters_control and clusters_treatment count the clusters; n_control and n_treatment count the participants. Sites in a trial that randomises participants are not clusters: use assignment(...) there. Tests that assume independent participants are refused. With randomisation, the units are the clusters. randomisation is "complete" when every split of the units into arms of these sizes was equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each stratum; "blocked" with block_size=... (and optional strata) when it holds within each block of that size. Strata and blocks count randomised units. Leave it out otherwise; only randomisation_test reads it, and it refuses an assignment without it. population says who is analysed: "randomised" for everyone randomised, in the arm they were assigned to (intention to treat), or "per_protocol" when participants excluded after randomisation are left out, with the arm sizes counting those analysed. randomisation_test needs "randomised" and refuses "per_protocol". Other tests take either, and their claims say which population the bound covers.
- `stratum(control: integer, treatment: integer) -> Stratum`
  One stratum of a stratified or blocked assignment: how many randomised units, participants or clusters, it has in each arm.
- `binary_outcome(better?: string, name?: string) -> Outcome`
  The binary outcome measured on each participant. Combine it with an assignment in two_arm(...). better is "higher" or "lower": which direction of the outcome is better. When given, a one-sided null must ask whether the treatment is better in that direction. When left out, a one-sided null's direction is listed as an assumption. name labels the outcome, such as "response". One name is one outcome: models that share it must agree on its kind and better. A family, sequence or graph that asks the same question of a named outcome twice, the same test of the same null on the same participants, is refused.
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

### `tests.wald` — Analyses and claims

Two-sided unpooled Wald rule for equal binomial proportions and balanced fixed arms. Lean checks a uniform finite-sample Type I error ceiling for the specified cutoff.

- `wald_test(design: StudyDesign, null: Hypothesis, squared_cutoff: number, alpha: level) -> WaldAnalysis`
  The two-sided unpooled Wald analysis uses equal arm sizes and a positive rational squared critical value. Alpha is the requested finite-sample error ceiling.
  Required null: p_treatment = p_control (equal arm success probabilities); same model required.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.score` — Analyses and claims

Two-sided pooled score test for equal binomial proportions and balanced fixed arms. Lean checks a finite-sample Type I error ceiling or an exact counterexample.

- `score_test(design: StudyDesign, null: Hypothesis, squared_cutoff: number, alpha: level) -> ScoreAnalysis`
  The two-sided pooled score test uses equal arm sizes and a positive rational squared critical value. Alpha is the requested finite-sample error ceiling.
  Required null: p_treatment = p_control (equal arm success probabilities); same model required.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.randomisation` — Analyses and claims

Randomisation test of the sharp null that treatment changes no participant's outcome, for any two-arm model. Its level follows from the complete, stratified or blocked randomisation declared on the assignment; Lean proves it for every statistic fixed in advance. With clusters randomised, the test permutes clusters. Up to 10,000 randomised units and 1,000 strata or blocks.

- `randomisation_test(design: StudyDesign, null: Hypothesis, alpha: level, draws?: integer) -> RandomisationAnalysis`
  Randomisation test of the sharp null. Its level follows from the randomisation declared on the assignment, and Lean proves it for every test statistic fixed in advance; no distribution is assumed. With cluster_assignment the clusters are randomised, so the test permutes clusters. Without draws the p-value counts every possible assignment; with draws=B it compares the observed assignment with B drawn at random, which Lean also proves. The randomisation test supports only the sharp null no_effect(model=...). It does not test equal means or proportions: when effects differ between participants, its error under those nulls is not guaranteed. Keep your null if it states your question, and choose a test that supports it.
  Required null: treatment changes no participant's outcome (the sharp null); same model required.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `models.observational` — Observational studies

Cross-sectional, cohort, person-time cohort, case-control and 1:1 matched case-control studies, whose exposure was not assigned. Each says what its sampling fixed: only the total, the exposed and unexposed groups, the numbers of cases and controls, the pairs, or nothing but person-time. The null of no association, and observed tables, pairs and events.

- `cross_sectional(n: integer, exposure?: string, outcome?: string, exposure_scale?: string, outcome_scale?: string, survey?: string, clusters?: integer) -> CrossSectionalStudy`
  A cross-sectional study: n participants sampled from one population, with exposure and outcome measured at the same time. Only n is fixed, not how many are exposed. It measures prevalence, not incidence. exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.
- `cohort(exposed?: integer, unexposed?: integer, n?: integer, exposure?: string, outcome?: string, exposure_scale?: string, outcome_scale?: string) -> CohortStudy`
  A cohort study: participants followed from exposure to outcome. Give exposed and unexposed when the groups were sampled in fixed numbers, or n when one population was sampled and exposure measured. exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.
- `case_control(cases: integer, controls: integer, exposure?: string, outcome?: string, exposure_scale?: string) -> CaseControlStudy`
  A case-control study: cases with the outcome and controls without it, sampled in fixed numbers and asked about past exposure. It estimates odds ratios only, never risk or prevalence, because the design fixed how many have the outcome. exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.
- `person_time_cohort(exposure?: string, outcome?: string, exposure_scale?: string) -> PersonTimeStudy`
  A cohort followed over person-time, counting events in the exposed and unexposed. It measures incidence rates; no group size is fixed. exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.
- `observed_events(model: PersonTimeStudy, exposed_events: integer, exposed_time: number, unexposed_events: integer, unexposed_time: number) -> ObservedEvents`
  Events and person-time, such as person-years, in the exposed and unexposed groups of a person-time cohort.
- `matched_case_control(pairs: integer, exposure?: string, outcome?: string, exposure_scale?: string) -> MatchedStudy`
  A 1:1 matched case-control study: each case matched to one control on chosen characteristics. Its tests and intervals use the pairs where exactly one was exposed; unmatched analyses refuse it. exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.
- `observed_pairs(model: MatchedStudy, both_exposed: integer, case_exposed_only: integer, control_exposed_only: integer, neither_exposed: integer) -> MatchedPairs`
  The observed pairs of a matched study: both exposed, only the case, only the control, or neither. They must add up to the pairs.
- `observed_table(model: ObservationalStudy, exposed_cases: integer, exposed_noncases: integer, unexposed_cases: integer, unexposed_noncases: integer) -> AssociationTable`
  The observed 2x2 table: exposed and unexposed cases, who have the outcome, and noncases. It must fit what the design fixed: a cohort's group sizes, a case-control study's numbers of cases and controls, or the total.
- `no_association(model: ObservationalStudy) -> AssociationNull`
  Null: no association between the study's exposure and outcome, an odds ratio of 1. For a cohort, equal risk with and without exposure; for a case-control study, exposure as common among cases as among controls; for a cross-sectional study, equal prevalence.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.association` — Observational studies

Fisher's exact test of no association in an observational 2x2 study, proved in Lean for every design: with the group sizes fixed, and with only the total fixed, by averaging over the number exposed. McNemar's exact test for matched pairs, proved given the discordant pairs and on average. The exact test of equal incidence rates for any person-time, proved given the total events and on average. Checked p-values for observed data. A bound concerns association, not an effect of the exposure.

- `fisher_exact(design: StudyDesign, null: AssociationNull, alpha: level) -> AssociationAnalysis`
  Fisher's exact test of no association in an observational 2x2 study. Lean proves its level for every design: with group sizes fixed by a cohort or case-control study, and with only the total fixed, by averaging over the number exposed. The bound concerns association, not an effect of the exposure.
- `rate_test(design: StudyDesign, null: AssociationNull, alpha: level) -> RateAnalysis`
  The exact test of equal incidence rates: given the total events, a two-sided binomial test of the exposed share at the exposed share of person-time. Lean proves its level for every rate and any person-time, given the total and on average over it.
- `rate_result(analysis: RateAnalysis, events: ObservedEvents) -> ResultClaim`
  Claim about the exact p-value and decision of the rate test for the observed events, with the test's Type I bound.
- `mcnemar(design: StudyDesign, null: AssociationNull, alpha: level) -> MatchedAnalysis`
  McNemar's exact test of no association within matched pairs: given the discordant pairs, a two-sided binomial test at one half. Lean proves its level given the number of discordant pairs and on average over it.
- `matched_result(analysis: MatchedAnalysis, pairs: MatchedPairs) -> ResultClaim`
  Claim about the exact p-value and decision of McNemar's test for the observed pairs, with the test's Type I bound.
- `association_result(analysis: AssociationAnalysis, table: AssociationTable) -> ResultClaim`
  Claim about the exact p-value and decision of Fisher's test for the observed table, with the test's Type I bound. For a design that fixed only the total, the p-value is given the number exposed.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `estimation.observational` — Observational studies

Prevalence (cross-sectional) and cumulative incidence (cohort) with exact intervals; the incidence rate ratio of a person-time cohort; the conditional odds ratio of matched pairs. Intervals for the odds ratio (any design), the risk ratio and difference (cohort) and the prevalence ratio and difference (cross-sectional) from an observed table. Each comes from exact intervals for the two groups' probabilities, with joint coverage proved in Lean; valid for every pair of probabilities, and conservative. A design refuses what it cannot estimate.

- `rate_ratio(events: ObservedEvents, level: level) -> IntervalClaim`
  Interval for the incidence rate ratio of a person-time cohort, from the exact interval for the exposed share of events.
- `prevalence(model: ObservationalStudy, cases: integer, level: level, group?: string) -> IntervalClaim`
  The prevalence with its exact interval. Only a cross-sectional study estimates it. For a cohort that sampled groups separately, group="exposed" or "unexposed" says which.
- `cumulative_incidence(model: ObservationalStudy, cases: integer, level: level, group?: string) -> IntervalClaim`
  The cumulative incidence with its exact interval. Only a cohort study estimates it. For a cohort that sampled groups separately, group="exposed" or "unexposed" says which.
- `conditional_odds_ratio(pairs: MatchedPairs, level: level) -> IntervalClaim`
  Interval for the conditional odds ratio of a matched study, the odds that the case is the exposed one in a discordant pair, from the exact interval for that probability.
- `odds_ratio(table: AssociationTable, level: level) -> IntervalClaim`
  Interval for the odds ratio at the given confidence level, from exact intervals for each group's probability; valid for every pair of probabilities, and conservative. Any design: for a case-control study it is the odds ratio of exposure, which equals that of the outcome.
- `risk_ratio(table: AssociationTable, level: level) -> IntervalClaim`
  Interval for the risk ratio at the given confidence level, from exact intervals for each group's probability; valid for every pair of probabilities, and conservative. Only a cohort study estimates it.
- `risk_difference(table: AssociationTable, level: level) -> IntervalClaim`
  Interval for the risk difference at the given confidence level, from exact intervals for each group's probability; valid for every pair of probabilities, and conservative. Only a cohort study estimates it.
- `prevalence_ratio(table: AssociationTable, level: level) -> IntervalClaim`
  Interval for the prevalence ratio at the given confidence level, from exact intervals for each group's probability; valid for every pair of probabilities, and conservative. Only a cross-sectional study estimates it.
- `prevalence_difference(table: AssociationTable, level: level) -> IntervalClaim`
  Interval for the prevalence difference at the given confidence level, from exact intervals for each group's probability; valid for every pair of probabilities, and conservative. Only a cross-sectional study estimates it.

### `tests.regression` — Cited analyses

Regression tests of the exposure with covariates for observational studies: logistic (cross-sectional, cohort, case-control), conditional logistic (matched pairs), Poisson rates (person-time cohorts), modified Poisson for risk and prevalence ratios, and linear regression for a continuous outcome. Guarantees are cited.

- `logistic_association(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  Wald or likelihood-ratio test of the exposure in a logistic regression. Fits cross-sectional, cohort or case-control studies with a binary outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `conditional_logistic(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  Test of the exposure in a conditional logistic regression of matched pairs. Fits matched-case-control studies with a binary outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `poisson_rate_regression(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  Test of the exposure in a Poisson regression of rates with a person-time offset. Fits person-time-cohort studies with a binary outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `modified_poisson(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  Test of the exposure's risk or prevalence ratio by Poisson regression with a robust variance. Fits cross-sectional or cohort studies with a binary outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `linear_association(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  t-test of the exposure's slope in a linear regression. Fits cross-sectional or cohort studies with a continuous outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.correlation` — Cited analyses

Pearson's correlation under bivariate normality and Spearman's rank correlation by exact permutation, for two continuous variables of a cross-sectional study. Guarantees are cited.

- `pearson_correlation(design: StudyDesign, null: AssociationNull, alpha: level) -> CitedAssociation`
  t-test of Pearson's correlation coefficient. Fits cross-sectional studies with a continuous outcome. Its guarantee is cited from the literature and not checked by Lean.
- `spearman_correlation(design: StudyDesign, null: AssociationNull, alpha: level) -> CitedAssociation`
  Exact permutation test of Spearman's rank correlation. Fits cross-sectional studies with a continuous outcome. Its guarantee is cited from the literature and not checked by Lean.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `tests.survey` — Cited analyses

Design-based tests for complex survey samples, with strata, clusters or weights: survey-weighted logistic and linear regression and the Rao-Scott test of a 2x2 table. Guarantees are cited and need enough sampled clusters.

- `survey_logistic(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  Design-based Wald test of the exposure in a survey-weighted logistic regression. Fits cross-sectional studies with a binary outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `survey_linear(design: StudyDesign, null: AssociationNull, alpha: level, adjusted_for?: list) -> CitedAssociation`
  Design-based Wald test of the exposure in a survey-weighted linear regression. Fits cross-sectional studies with a continuous outcome. Its guarantee is cited from the literature and not checked by Lean. adjusted_for lists the covariates, by name.
- `rao_scott_test(design: StudyDesign, null: AssociationNull, alpha: level) -> CitedAssociation`
  Rao-Scott adjusted chi-squared test of association in a 2x2 survey table. Fits cross-sectional studies with a binary outcome. Its guarantee is cited from the literature and not checked by Lean.
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

Exact power at a planning point, target checks and a bounded sample-size search with equal or unequal allocation for the fixed Fisher analysis, for Fisher's test of association in every observational design, for McNemar's test and for the rate test given its events. Targets also apply to one-sample tests and two-stage designs. A size can be certified as sufficient or as the smallest in the declared range. Cited tests get approximate power from a normal formula, or the noncentral t for tests of cluster summaries, by calculation only.

- `binomial_rates(p_control: number, p_treatment: number, icc?: number, cluster_size_cv?: number) -> Rates`
  A planning point: one success probability per arm. It is an input for power, not the null and not an established fact. A test of cluster proportions also needs icc, the intracluster correlation, and simulate(...) takes cluster_size_cv, how much cluster sizes vary.
- `mean_difference(value: number, sd: number, icc?: number, cluster_size_cv?: number, sd_treatment?: number, skewness?: number) -> MeanDifference`
  A planning point for a continuous outcome: the true mean difference, treatment minus control, and the standard deviation of one participant's outcome on the analysed scale. For a mixed model, sd is the effective standard deviation of the contrast. A test of cluster means also needs icc, the intracluster correlation: the share of the variance that lies between clusters; simulate(...) also takes cluster_size_cv, the coefficient of variation of cluster sizes. To simulate a two-sample t-test in another scenario, give sd_treatment, the treatment arm's SD (sd is then the control arm's), or skewness, for a gamma-shaped outcome. All are planning inputs.
- `hazard_ratio(value: number, events: integer) -> HazardRatio`
  A planning point for a survival outcome: the true hazard ratio, treatment over control, and the expected total number of events. Power depends on the events, not on the arm sizes. Both are planning inputs.
- `correlation(value: number, skewness?: number, exposure_skewness?: number) -> Correlation`
  A planning point for two continuous variables: their correlation, strictly between -1 and 1. For pearson_correlation. To simulate skewed data, give skewness (of the outcome's error) or exposure_skewness. Planning inputs, not established facts.
- `outcome_means(unexposed: number, exposed: number, sd: number, exposed_share?: number, design_effect?: number) -> OutcomeMeans`
  A planning point for a measured outcome by a yes-or-no exposure, for linear_association or survey_linear: the outcome's mean without and with the exposure, and its standard deviation about them. A study that fixes only its total also needs exposed_share; a survey of a complex sample, design_effect. Planning inputs, not established facts.
- `odds_per_sd(odds_ratio: number, baseline: number, exposure_r2?: number, design_effect?: number) -> OddsPerSd`
  A planning point for logistic_association with a measured exposure: the odds ratio per standard deviation of the exposure, the outcome's probability at the exposure's mean, and optionally exposure_r2, the share of the exposure's variance the covariates explain. A survey test of a complex sample also takes design_effect. Planning inputs, not established facts.
- `slope(value: number, exposure_sd: number, residual_sd: number, exposure_r2?: number, design_effect?: number, skewness?: number, exposure_skewness?: number) -> Slope`
  A planning point for linear_association with a continuous exposure: the change in the outcome's mean per unit of exposure, the exposure's standard deviation, the outcome's standard deviation about the regression, and optionally exposure_r2, the share of the exposure's variance the covariates explain. A survey test of a complex sample also takes design_effect. To simulate skewed data, give skewness (of the residual) or exposure_skewness. All are planning inputs.
- `exponential_survival(hazard_ratio: number, control_median: number, accrual: number, follow_up: number, dropout?: number, dropout_time?: number, effect_delay?: number) -> ExponentialSurvival`
  A planning point for a survival outcome given by its times: the hazard ratio, treatment over control; the control arm's median time to the event; participants entering steadily over accrual and followed for follow_up after it; and optionally the probability of dropping out by dropout_time. Times are exponential and in one unit, such as months. The arm sizes then give the expected events, so arm sizes can be searched. simulate(...) also takes effect_delay: the hazard ratio applies only from that time after entry. All are planning inputs.
- `risks(unexposed: number, exposed?: number, risk_ratio?: number, exposed_share?: number) -> Risks`
  A planning point for a cohort: the risk of the outcome without exposure, and with it, given as exposed or as risk_ratio, exposed over unexposed. A cohort of one population, declared with n, also needs exposed_share, the probability that a participant is exposed. A planning input, not an established fact.
- `outcome_prevalence(unexposed: number, exposed?: number, prevalence_ratio?: number, exposed_share: number, design_effect?: number) -> OutcomePrevalence`
  A planning point for a cross-sectional study: the prevalence of the outcome without exposure, and with it, given as exposed or as prevalence_ratio, and exposed_share, the probability that a participant is exposed. A survey test of a complex sample also takes design_effect. A planning input, not an established fact.
- `exposure_prevalence(controls: number, cases?: number, odds_ratio?: number) -> ExposurePrevalence`
  A planning point for a case-control study: the share of controls who were exposed, and of cases, given as cases or as odds_ratio, the odds of exposure among cases over the odds among controls. A planning input, not an established fact.
- `discordant_pairs(share: number, odds_ratio: number) -> DiscordantPairs`
  A planning point for a 1:1 matched study: the probability that a pair is discordant, with exactly one of the two exposed, and the conditional odds ratio. A planning input, not an established fact.
- `incidence_rates(rate_ratio: number, exposed_time: number, unexposed_time: number, events?: integer) -> IncidenceRates`
  A planning point for a person-time cohort: the rate ratio, exposed over unexposed, the expected person-time in each group, of which only the exposed share matters, and the total number of events power is calculated for. Leave events out to search them with event_counts.
- `proportion(value: number, design_effect?: number, population_size?: integer) -> SingleProportion`
  A planning point for one proportion, such as a prevalence or a cumulative incidence: its value, strictly between 0 and 1. For the normal interval of a survey, design_effect and population_size, the number in the population sampled, for a finite population correction. A planning input, not an established fact.
- `precision_target(at: PlanningPoint, level: level, margin_of_error?: number, relative_margin_of_error?: number, assurance?: number) -> PrecisionTarget`
  Require an interval at the given level to be narrow enough at the planning point: its margin of error, half its width, at most margin_of_error, or its relative margin of error at most relative_margin_of_error, a fraction of the planning value. For a ratio the relative margin r asks that the lower limit be at least (1 - r) times the estimate, on the log scale. Without assurance, the interval is taken at the counts the point expects; with it, the chance that the interval is narrow enough must be at least assurance.
- `planned_interval(model: EstimableModel, measure: string, method?: string, group?: string) -> PlannedInterval`
  The interval a study plans to report, for a precision target: response_rate for one arm, difference for a two-arm trial, prevalence, cumulative_incidence, risk or prevalence ratios and differences and odds_ratio for observational studies, conditional_odds_ratio for matched pairs and rate_ratio for person-time. method="exact" (the default) is StatClaim's own exact interval; method="normal" is the usual large-sample interval, and allows a survey's design effect and a finite population. For a cohort that sampled two groups, group says whose cumulative incidence.
- `interval_sizes(interval: PlannedInterval, min_size: integer, max_size: integer, ratio?: integer) -> IntervalCandidates`
  Sizes for a planned interval, in the design's own units: the participants of one group or population; for two fixed groups, the first (exposed, cases, or the control arm of a trial) with ratio of the other for each; or the pairs or events.
- `power_target(at: PlanningPoint, minimum: number, maximum_typeI: level, nulls?: NullScenarios, rejecting?: string) -> PowerTarget`
  Require power of at least minimum at one planning point, and a Type I error bound of at most maximum_typeI under the null. Power at this point is not a guarantee for other alternatives. For a design whose level is not proved, nulls lists where simulate(...) judges its Type I error. For a family, rejecting says whether power means rejecting "any" endpoint or "all" of them.
- `endpoint_points(at: list, correlation: number) -> EndpointPoints`
  A planning point for a family: one point per member, in order (binomial_rates for Fisher's test, mean_difference for a t-test), and the correlation between endpoints measured on the same participants, from 0 for independent endpoints to below 1. Planning inputs.
- `null_scenarios(at: list) -> NullScenarios`
  Points at the null, such as mean_difference(value=0, sd=10), at which simulate(...) judges the Type I error of a design whose level is not proved. Planning inputs; the error at other points is not claimed.
- `meets(analysis: Analysis, target: Target) -> PlanningClaim`
  Claim that this analysis meets every component of the target. calculate computes the components; verify must establish all. For a cited test, calculate gives approximate power and verify is refused.
- `equal_arm_sizes(analysis: Analysis, min_per_arm: integer, max_per_arm: integer) -> Candidates`
  A finite design space: equal arm sizes within inclusive bounds, keeping the analysis's sampling, null form, test and alpha.
- `allocated_arm_sizes(analysis: Analysis, min_control: integer, max_control: integer, treatment_per_control: integer) -> Candidates`
  A finite design space with unequal allocation: each candidate has n controls and treatment_per_control * n treated participants, for n within the inclusive bounds.
- `cluster_counts(analysis: Analysis, cluster_size: integer, min_per_arm: integer, max_per_arm: integer) -> ClusterCandidates`
  Cluster-randomised trials for a test of cluster summaries: min_per_arm to max_per_arm clusters in each arm, each of cluster_size participants. Each keeps the analysis's null, test and alpha.
- `cluster_sizes(analysis: Analysis, min_size: integer, max_size: integer) -> ClusterCandidates`
  Cluster-randomised trials for a test of cluster summaries: the declared clusters per arm, with min_size to max_size participants in each cluster. Each keeps the analysis's null, test and alpha. With few clusters, no number of participants may be enough.
- `cohort_sizes(analysis: Analysis, min_exposed: integer, max_exposed: integer, unexposed_per_exposed?: integer) -> GroupCandidates`
  Designs of a cohort that samples its exposed and unexposed groups: n exposed and unexposed_per_exposed * n unexposed (1 unless given), for n within the inclusive bounds. Each keeps the analysis's study, null and alpha.
- `case_control_sizes(analysis: Analysis, min_cases: integer, max_cases: integer, controls_per_case?: integer) -> GroupCandidates`
  Designs of a case-control study: n cases and controls_per_case * n controls (1 unless given), for n within the inclusive bounds. Each keeps the analysis's study, null and alpha.
- `total_sizes(analysis: Analysis, min_n: integer, max_n: integer) -> TotalCandidates`
  Cross-sectional studies, or cohorts of one population, with min_n to max_n participants, keeping the analysis's study, null and alpha. For Fisher's test, sample_size certifies a sufficient total and smallest_sample_size is not offered; for a cited test with a power formula, both are calculated.
- `matched_sizes(analysis: Analysis, min_pairs: integer, max_pairs: integer) -> CountCandidates`
  Matched studies with min_pairs to max_pairs pairs, keeping the analysis's null and alpha: McNemar's test, or a conditional logistic regression.
- `event_counts(analysis: Analysis, min_events: integer, max_events: integer) -> CountCandidates`
  Totals of min_events to max_events events for the rate test or a Poisson rate regression, keeping its null and alpha. The planning point gives no events.
- `sample_sizes(analysis: OneSampleAnalysis, min_n: integer, max_n: integer) -> OneArmCandidates`
  A finite design space: sample sizes within inclusive bounds for a one-sample test, keeping its null rate and alpha.
- `response_rate(value: number) -> Rate`
  A planning point for a single-arm design.
- `sample_size(candidates: Candidates, target: Target) -> PlanningClaim`
  Claim that some candidate meets the target. The search is ascending; a sufficient size is not claimed to be the smallest possible.
- `smallest_sample_size(candidates: Candidates, target: Target) -> PlanningClaim`
  Claim that a candidate meets the target and that no smaller candidate in the declared range does. Nothing is claimed outside the range.

### `designs.group_sequential` — Adaptive designs

One test repeated at several looks, stopping at the first rejection. alpha_spending splits the level across the looks, and Lean checks that the split gives the overall bound; it ignores the correlation between looks. group_sequential uses it: each look's level is at most the nominal level an O'Brien-Fleming or Pocock spending function gives it, a cited rule. Each look's own bound is assumed.

- `alpha_spending(looks: list, alpha: level) -> Sequential`
  One test repeated at several looks, stopping at the first rejection. Give each look as an analysis whose model has the cumulative arm sizes at that look, with the level spent there. The levels may sum to at most alpha. Lean checks the combination; each look's own bound is assumed. The split is conservative.
- `group_sequential(looks: list, alpha: level, spending: string) -> Sequential`
  One test repeated at several looks, stopping at the first rejection, with boundaries that use the correlation between looks. spending is "obrien_fleming" or "pocock" (Lan and DeMets). Give each look as an analysis whose model has the cumulative arm sizes at that look, with its nominal level: at most the level the spending function gives it at its share of the information. The error message lists those levels. For Fisher's test and the t-tests. The rule is cited.
- `look_sizes(design: Sequential, min_per_arm: integer, max_per_arm: integer, step: integer, criterion: string) -> LookCandidates`
  Designs with the declared looks whose sizes per control arm are free: every increasing choice from min_per_arm to max_per_arm in steps of step, keeping the final look's allocation, test and null. Each candidate keeps the declared levels, or takes its own spending boundaries. criterion="minimax" ranks the smallest final size first; "optimal" the smallest expected size at the planning point. Exact for Fisher's test, simulated for t-tests; the ranking is a calculation.
- `typeI(analysis: Analysis) -> TypeIClaim`

### `designs.adaptive` — Adaptive designs

Student's t-test whose size per arm is re-estimated at an interim look from the blinded variance. Its Type I error is not proved; simulate(...) judges it at the target's null scenarios.

- `blinded_reestimation(analysis: CitedAnalysis, interim_per_arm: integer, difference: number, power: number, max_per_arm: integer) -> Reestimation`
  Student's t-test whose size per arm is re-estimated after interim_per_arm per arm, from the variance of all outcomes with the arms pooled, so no one sees the groups. The new size gives power at the planned difference; it is never below the analysis's size per arm nor above max_per_arm. Its Type I error is not proved: simulate(...) judges it at the target's null scenarios.

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
- `simulate(claim: Claim, seed: integer, runs?: integer) -> CalculationResult`

Verification and calculation run only on explicit execution; the editor plans them. Compilation cannot create evidence.

## Statuses and other fixed values

### Result status (`result.status`)

| Status | Meaning |
| --- | --- |
| `verified` | Lean proved the guarantee for the procedure as declared, under the listed assumptions. It says nothing about how the study is run. Evidence grade `proved`. |
| `refuted` | Lean verified a counterexample to the guarantee for the declared procedure. |
| `conditional` | Lean proved how the parts combine; each part's own guarantee is assumed. Like every status, it concerns the study as declared. Evidence grade `conditional`. |
| `cited` | The study fits a published method's contract; the guarantee is cited, not machine-checked. Evidence grade `cited`. |
| `declared` | The author named and vouched for the test or one of its parts. Nothing about that guarantee was checked or cited. Evidence grade `declared`. |
| `calculated` | A `calculate` request produced numbers. No evidence. |
| `simulated` | A `simulate` request estimated power and Type I error from simulated studies, with 95% intervals. An estimate with Monte Carlo error. No evidence. |
| `unresolved_obligation` | A requirement is unmet or a target is missed. No evidence. Not a finding that the claim is false. |
| `backend_error` | Lean could not be run or failed for a technical reason. No evidence. |
| `not_executed` | The request was planned by `compile` and has not been run. |

### File status (`Program status`)

| Status | Meaning |
| --- | --- |
| `invalid` | The file has an error and nothing was run. |
| `elaborated` | The file compiles with no open requirement; nothing was run. |
| `refuted` | Lean verified a counterexample to at least one claim. |
| `unresolved_obligation` | At least one claim has an unmet requirement. |
| `declared` | Every claim went through; the weakest part anywhere is a declared test. |
| `cited` | Every claim went through; the weakest part anywhere is cited. |
| `conditional` | Every claim went through; the weakest part is a proved combination of tests that are themselves provable. |
| `verified` | Every verified claim was proved; calculations and simulations may also be present. |
| `simulated` | Only calculations and simulations were requested; simulated values are estimates. |
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
| `monte_carlo` | About a simulation: the data it draws and the Monte Carlo error of its estimates. The intervals show the error; the scenario is not checkable. |

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
| `per_protocol` | Participants excluded after randomisation are left out; the arm sizes count those analysed. A randomisation test is refused; other claims say they cover this population only, and list as assumed that exclusions were not chosen from the results. |

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

### String inputs with fixed values

Other string inputs, such as `name`, take free text.

| Input | Values | Constructors |
| --- | --- | --- |
| `rejecting` | `any`, `all` | `power_target` |
| `better` | `higher`, `lower` | `two_arm_continuous`, `continuous_outcome`, `two_arm_survival`, `survival_outcome`, `two_arm_binomial`, `binary_outcome` |
| `population` | `randomised`, `per_protocol` | `two_arm_continuous`, `assignment`, `cluster_assignment`, `two_arm_survival`, `two_arm_binomial` |
| `randomisation` | `complete`, `stratified`, `blocked` | `assignment`, `cluster_assignment` |
| `joint_law` | `binomial_marginals` | `bonferroni` |
| `criterion` | `optimal`, `minimax` | `look_sizes`, `two_stage_designs` |
| `scope` | `finite_sample`, `asymptotic` | `declared_test` |
| `spending` | `obrien_fleming`, `pocock` | `group_sequential` |
| `group` | `exposed`, `unexposed` | `prevalence`, `cumulative_incidence`, `planned_interval` |
| `measure` | `response_rate`, `prevalence`, `cumulative_incidence`, `difference`, `risk_difference`, `prevalence_difference`, `risk_ratio`, `prevalence_ratio`, `odds_ratio`, `conditional_odds_ratio`, `rate_ratio` | `planned_interval` |
| `exposure_scale` | `binary`, `continuous` | `cross_sectional`, `cohort`, `case_control`, `person_time_cohort`, `matched_case_control` |
| `outcome_scale` | `binary`, `continuous` | `cross_sectional`, `cohort` |
| `survey` | `simple_random`, `stratified`, `cluster`, `weighted` | `cross_sectional` |

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
| `log_rank` | 1 | survival | `equal_survival` | equals alpha | `asymptotic` | 1 per arm, 2 total | `schoenfeld_log_rank`, `schoenfeld_exponential_times` |
| `logistic_regression` | 1 | binary | `equal_proportions` | equals alpha | `asymptotic` | 2 per arm, 4 total | `logistic_wald_enumeration` |
| `logistic_regression_one_sided` | 1 | binary | `proportion_difference_at_most` | at most alpha | `asymptotic` | 2 per arm, 4 total | `logistic_wald_enumeration` |
| `cluster_t_test` | 1 | continuous | `equal_means` | equals alpha | `finite_sample` | 4 clusters per arm, 8 total | `cluster_t_means` |
| `cluster_proportion_t_test` | 1 | binary | `equal_proportions` | equals alpha | `finite_sample` | 4 clusters per arm, 8 total | `cluster_t_proportions` |

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
| `schoenfeld_exponential_times` | 1 | `exponential_survival` | `normal_approximation_power`, `proportional_hazards`, `at_risk_shares`, `exponential_times`, `uniform_accrual`, `exponential_dropout` |
| `logistic_wald_enumeration` | 1 | `binomial_rates` | `wald_enumeration`, `unadjusted_proportions` |
| `cluster_t_means` | 1 | `mean_difference` | `noncentral_t_power`, `planning_standard_deviation`, `planning_icc`, `equal_cluster_sizes` |
| `cluster_t_proportions` | 1 | `binomial_rates` | `noncentral_t_power`, `planning_icc`, `equal_cluster_sizes` |

**`normal_two_means`** (Difference of two means, normal approximation with a known standard deviation). References:

- Chow, S.-C., Shao, J. and Wang, H. (2008). Sample Size Calculations in Clinical Research, 2nd ed. Chapman and Hall/CRC. Chapter 3.
- Julious, S. A. (2004). Sample sizes for clinical trials with normal data. Statistics in Medicine 23(12), 1921-1986.

**`schoenfeld_log_rank`** (Log-rank test, Schoenfeld's formula in the number of events). References:

- Schoenfeld, D. (1981). The asymptotic properties of nonparametric tests for comparing survival distributions. Biometrika 68(1), 316-319.
- Schoenfeld, D. A. (1983). Sample-size formula for the proportional-hazards regression model. Biometrics 39(2), 499-503.

**`schoenfeld_exponential_times`** (Log-rank test, Schoenfeld's formula at the events expected from exponential times). References:

- Schoenfeld, D. (1981). The asymptotic properties of nonparametric tests for comparing survival distributions. Biometrika 68(1), 316-319.
- Schoenfeld, D. A. (1983). Sample-size formula for the proportional-hazards regression model. Biometrics 39(2), 499-503.
- Lachin, J. M. and Foulkes, M. A. (1986). Evaluation of sample size and power for analyses of survival with allowance for nonuniform patient entry, losses to follow-up, noncompliance, and stratification. Biometrics 42(3), 507-519. [to verify]
- Anderson, K. M. gsDesign (nSurv, eEvents), and Wassmer, G. and Pahlke, F. rpact (getSampleSizeSurvival), R packages for survival designs.

**`logistic_wald_enumeration`** (Wald test of the treatment coefficient, summed over both arms' binomial counts). References:

- Agresti, A. (2013). Categorical Data Analysis, 3rd ed. Wiley. Sections 3.1 and 5.2.
- Hauck, W. W. and Donner, A. (1977). Wald's test as applied to hypotheses in logit analysis. Journal of the American Statistical Association 72(360), 851-853.

**`cluster_t_means`** (t-test on cluster means, noncentral t with the design effect). References:

- Donner, A., Birkett, N. and Buck, C. (1981). Randomization by cluster: sample size requirements and analysis. American Journal of Epidemiology 114(6), 906-914. [to verify]
- R Core Team. power.t.test, in the stats package of R.
- Lenth, R. V. (1989). Algorithm AS 243: cumulative distribution function of the non-central t distribution. Applied Statistics 38(1), 185-189.
- Benton, D. and Krishnamoorthy, K. (2003). Computing discrete mixtures of continuous distributions: noncentral chisquare, noncentral t and the distribution of the square of the sample multiple correlation coefficient. Computational Statistics and Data Analysis 43(2), 249-267.

**`cluster_t_proportions`** (t-test on cluster proportions, noncentral t with the design effect). References:

- Donner, A., Birkett, N. and Buck, C. (1981). Randomization by cluster: sample size requirements and analysis. American Journal of Epidemiology 114(6), 906-914. [to verify]
- R Core Team. power.t.test, in the stats package of R.
- Lenth, R. V. (1989). Algorithm AS 243: cumulative distribution function of the non-central t distribution. Applied Statistics 38(1), 185-189.
- Benton, D. and Krishnamoorthy, K. (2003). Computing discrete mixtures of continuous distributions: noncentral chisquare, noncentral t and the distribution of the square of the sample multiple correlation coefficient. Computational Statistics and Data Analysis 43(2), 249-267.

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
| `canonical_joint_distribution` | distribution | The test statistics at the looks are approximately normal with the canonical joint distribution: the data added between looks is independent of the data before, and the information at each look is proportional to n_control n_treatment / (n_control + n_treatment). |
| `prespecified_spending` | design | The looks happen at the declared cumulative sample sizes, the spending function is chosen in advance, and the study stops at the first look that rejects. |
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
| `prespecified_exclusions` | sampling | Who is excluded after randomisation was decided by rules fixed before outcomes were observed, so the arm sizes analysed were not chosen by looking at the results. |
| `normal_approximation_power` | approximation | Power comes from a normal approximation to the test statistic, with its variance at the planning values. It is an approximation, not a bound. |
| `simulated_two_means` | monte_carlo | The simulation draws normal outcomes with the planning standard deviation in both arms, or the declared scenario: with sd_treatment, each arm its own SD; with skewness, a gamma distribution shifted and scaled to the arm's mean and SD, mirrored when the skewness is negative. Outcomes with another distribution may give other power and Type I error. |
| `monte_carlo_error` | monte_carlo | Simulated power and Type I error are estimates with Monte Carlo error. Each 95% interval covers the true rate in 95% of simulations; a size found by search is confirmed by an independent run. An estimate is not a bound. |
| `planning_standard_deviation` | scope | The standard deviation is a planning input, not an established fact. It is the standard deviation of one participant's outcome on the analysed scale; for a mixed model, the effective standard deviation of the contrast. |
| `unadjusted_proportions` | approximation | Power is for an unadjusted comparison of two proportions. Covariates in the analysis model change it. |
| `proportional_hazards` | distribution | The hazard ratio is constant over time. The log-rank test's error rate does not need this; its power formula does. |
| `planning_events` | scope | The number of events is a planning input, not an established fact. Power depends on the events, not on the arm sizes. |
| `at_risk_shares` | approximation | Each arm's share of the participants at risk stays close to its share at randomisation, as when the hazard ratio is near 1. |
| `noncentral_t_power` | approximation | Power comes from the noncentral t distribution of the t-test on cluster summaries, with the variance of a cluster's summary at the planning values. Exact for normal cluster means of equal variance; otherwise an approximation, not a bound. |
| `planning_icc` | scope | The intracluster correlation is a planning input, not an established fact: the share of the outcome's variance that lies between clusters. A cluster of m participants has a summary with variance (1 + (m - 1) icc) / m times that of one participant. |
| `equal_cluster_sizes` | approximation | Every cluster in an arm has the arm's mean size. Clusters of unequal sizes give less power than this. |
| `exponential_times` | approximation | Times to the event are exponential in each arm: the control hazard comes from its median, and the treatment hazard is the hazard ratio times it. Power from these times is an approximation, not a bound. |
| `uniform_accrual` | approximation | Participants enter at a steady rate over the accrual period, and the analysis is at its end plus the follow-up. Entry that is slower at first gives fewer events. |
| `exponential_dropout` | approximation | Dropout is at a constant rate, the same in both arms, and independent of the event. With no dropout declared, nobody is lost before the analysis. |
| `simulated_clusters` | monte_carlo | The simulation gives each cluster a normal effect with variance icc times the planning variance, and its participants normal outcomes about it. Cluster sizes are the arm's mean, or with cluster_size_cv, gamma draws with that coefficient of variation, rounded and at least 1. The test is the unweighted t-test of the cluster means. |
| `simulated_cluster_proportions` | monte_carlo | The simulation gives each cluster a response rate drawn from a beta distribution with the arm's planning rate as its mean and icc as the intracluster correlation, and binomial responses; sizes as for cluster means. The test is the unweighted t-test of the cluster proportions. |
| `simulated_survival` | monte_carlo | The simulation draws exponential event times with the control hazard log 2 / median, and in the treatment arm that hazard times the hazard ratio, from effect_delay after entry on when one is given. Entry is uniform over the accrual period, dropout exponential, and follow-up ends at the accrual period plus the follow-up. The test is the log-rank test with its normal approximation. |
| `simulated_association` | monte_carlo | The simulation draws the exposure and the outcome's error from the declared scenario: each normal, or with its skewness, a gamma distribution shifted and scaled to mean 0 and the planning SD, mirrored when the skewness is negative. The outcome is linear in the exposure, with the planning correlation or slope; other shapes may give other power and Type I error. |
| `reestimation_type_i` | monte_carlo | The re-estimated design's Type I error is not proved. It is judged by simulation at the declared null scenarios only; at other values of the standard deviation it may differ. |
| `simulated_endpoints` | monte_carlo | The simulation draws every endpoint at its planning point. Endpoints with a correlation are measured on the same participants through latent normals with that exchangeable correlation: a yes-or-no outcome is a success when its latent is high, a measured outcome rises with its latent. Other forms of dependence may give other power. |
| `wald_enumeration` | approximation | Power is summed exactly over both arms' binomial counts for the Wald test of the treatment coefficient, the log odds ratio over its standard error, with normal critical values. A table with an empty cell has no finite estimate; like glm's Wald test, it is counted as not rejecting. |
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
| `no_simulation_model` | error | A test with no simulation model is simulated, or simulate(...) is given a claim it cannot simulate. |
| `direction_mismatch` | error | A one-sided null asks about the direction the model's better= does not call better. |
| `complex_sample` | error | A method that assumes simple random sampling is given a stratified, cluster or weighted survey. |
| `matched_design` | error | An unmatched analysis or table is given a matched study, whose matching it ignores. |
| `not_estimable` | error | The design cannot estimate the measure, such as a risk ratio from a case-control study. |
| `observational_design` | error | A test that relies on randomised arms is given an observational study, whose exposure was not assigned. |
| `unequal_arm_sizes` | error | The test requires the same size in both arms. |
| `unit_mismatch` | error | The test's unit does not fit the declared design: it assumes independent participants or observations where clusters or repeated measurements are declared, or it takes one summary per cluster where participants were randomised. |
| `undeclared_randomisation` | error | A randomisation test is declared on an assignment that does not say how it was randomised. |
| `population_mismatch` | error | A randomisation test is declared on an assignment whose analysis leaves out randomised units (population="per_protocol"). |
| `never_rejects` | error | A randomisation test has too few equally likely splits to reach its level, so it could never reject. |
| `planning_point` | error | The planning point does not fit the analysis. |
| `rule_mismatch` | error | A stopping rule does not fit the two-stage design. |
| `sampling_contract` | error | A joint law is given where none applies, or is not supported. |
| `family_size` | error | A family or sequential design has too few or too many entries. |
| `duplicate_analysis` | error | A family or sequential design lists an analysis twice, or asks the same question of a named outcome twice. |
| `outcome_conflict` | error | One outcome name is given to outcomes of different kinds or better directions. |
| `sequential_question` | error | The looks of a sequential design differ in test or null. |
| `sequence_level` | error | A test in a fixed sequence or a graph is not declared at the overall level. |
| `graph_definition` | error | The weights or transitions of a graph are not valid. |
| `sequential_order` | error | The looks are not in order of growing sample size. |
| `sequential_boundary` | error | A look's level exceeds the nominal level its spending boundary allows there. |
| `wald_bound_unproved` | obligation | The checked Wald bounds over the null intervals do not establish the requested ceiling. |
| `score_bound_unproved` | obligation | The checked score bounds over the null intervals do not establish the requested ceiling. |
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

The [exact claim interface](lean-objects.md#exact-claim-interface) connects exact modules' statements and kernel checks to the program semantics.

The same content is available in machine-readable form from `statclaim catalogue --json`. See [adding modules](adding-modules.md).
