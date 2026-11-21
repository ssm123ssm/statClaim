"""The public field schema shared by elaboration, runtime, and editor tooling.

Only explicitly listed fields are exposed. Optional receivers propagate absence;
their fields remain optional, so they cannot be mistaken for checked evidence.
"""

from dataclasses import dataclass
from fractions import Fraction

from statclaim.language import (
    AnalysisIR,
    AssignmentIR,
    AssociationAnalysisIR,
    AssociationNullIR,
    AssociationResultIR,
    AssociationTableIR,
    CalculationResultIR,
    CandidatesIR,
    CandidateSpaceIR,
    CaseControlStudyIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    ClaimIR,
    ClusterCandidatesIR,
    CohortStudyIR,
    ComposedFamilyIR,
    CorrelationIR,
    CountCandidatesIR,
    CrossSectionalStudyIR,
    DifferenceIntervalIR,
    DiscordantPairsIR,
    EffectIntervalIR,
    EstimableModelIR,
    ExponentialSurvivalIR,
    ExposurePrevalenceIR,
    FamilyIR,
    FeasibilityIR,
    FieldIR,
    GroupCandidatesIR,
    HazardRatioIR,
    HypothesisIR,
    IncidenceRatesIR,
    IntervalCandidatesIR,
    IntervalIR,
    LocatedValue,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedPairsIR,
    MatchedResultIR,
    MatchedStudyIR,
    MeanDifferenceIR,
    ModelIR,
    NullIR,
    ObservationIR,
    ObservedEventsIR,
    OddsPerSdIR,
    OneArmCandidatesIR,
    OneArmModelIR,
    OneSampleAnalysisIR,
    OneSampleObservationIR,
    OutcomeIR,
    OutcomeMeansIR,
    OutcomeModelIR,
    OutcomeNullIR,
    OutcomePrevalenceIR,
    PersonTimeStudyIR,
    PlanIR,
    PlannableIR,
    PlannedIntervalIR,
    PlanningPointIR,
    PowerTargetIR,
    PrecisionTargetIR,
    PriorIR,
    ProportionIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateIR,
    RateRatioIR,
    RateResultIR,
    RatesIR,
    RisksIR,
    RuleIR,
    SequentialIR,
    SharpNullIR,
    SingleProportionIR,
    SizingIR,
    SlopeIR,
    StratumIR,
    StudyModelIR,
    TargetIR,
    TotalCandidatesIR,
    TwoArmTestIR,
    TwoStageAnalysisIR,
    TwoStageCandidatesIR,
    TwoStageModelIR,
    TwoStageObservationIR,
    ValueType,
    VerificationResultIR,
    fail,
)
from statclaim.language_syntax import Diagnostic, Span
from statclaim.language_values import (
    ApproximatePowerDetails,
    AssociationPowerDetails,
    AssociationResultDetails,
    CalculationDetails,
    CalculationResult,
    CertificateReference,
    DifferenceDetails,
    EffectIntervalDetails,
    Evidence,
    IntervalDetails,
    MarginDetails,
    MatchedPowerDetails,
    MatchedResultDetails,
    OneSampleDetails,
    OneSampleResultDetails,
    PlanningDetails,
    PolicyDetails,
    PrecisionDetails,
    RatePowerDetails,
    RateResultDetails,
    SimulationDetails,
    StageResultDetails,
    VerificationResult,
)
from statclaim.methods.core import Guarantee


@dataclass(frozen=True)
class FieldSpec:
    kind: str | type
    optional: bool = False
    attribute: str | None = None
    description: str = ""


BETTER = FieldSpec(str, optional=True, description="higher or lower, when declared.")
# A two-arm model's pieces, and the fields of the one-call constructors.
TWO_ARM_FIELDS = {
    "assignment": FieldSpec(AssignmentIR),
    "outcome": FieldSpec(OutcomeIR, attribute="measured"),
    "n_control": FieldSpec(int),
    "n_treatment": FieldSpec(int),
    "better": BETTER,
}

# What an observational study measures, by name.
STUDY_FIELDS = {
    "exposure": FieldSpec(str, description="The exposure's name."),
    "outcome": FieldSpec(str, description="The outcome's name."),
    "exposure_scale": FieldSpec(str, description="binary or continuous."),
    "outcome_scale": FieldSpec(str, description="binary or continuous."),
    "survey": FieldSpec(str, description="simple_random, stratified, cluster or weighted."),
    "clusters": FieldSpec(
        int, optional=True, description="Sampled clusters, for a cluster survey."
    ),
}

SCHEMAS = {
    AssignmentIR: {
        "n_control": FieldSpec(int),
        "n_treatment": FieldSpec(int),
        "randomisation": FieldSpec(
            str,
            optional=True,
            description="complete, stratified or blocked, when the file declares it.",
        ),
        "block_size": FieldSpec(int, optional=True, description="Units per block, if blocked."),
        "population": FieldSpec(
            str,
            optional=True,
            description="randomised or per_protocol: who is analysed, when declared.",
        ),
    },
    StratumIR: {"control": FieldSpec(int), "treatment": FieldSpec(int)},
    CrossSectionalStudyIR: {
        "n": FieldSpec(int, description="Participants sampled; how many are exposed is not fixed."),
        **STUDY_FIELDS,
    },
    CohortStudyIR: {
        "exposed": FieldSpec(int, optional=True, description="Exposed group size, if fixed."),
        "unexposed": FieldSpec(int, optional=True, description="Unexposed group size, if fixed."),
        "n": FieldSpec(int, optional=True, description="Total, when exposure was not fixed."),
        **STUDY_FIELDS,
    },
    CaseControlStudyIR: {
        "cases": FieldSpec(int),
        "controls": FieldSpec(int),
        **STUDY_FIELDS,
    },
    AssociationNullIR: {
        "model": FieldSpec(StudyModelIR),
        "predicate": FieldSpec(str),
        "statement": FieldSpec(str),
    },
    PersonTimeStudyIR: dict(STUDY_FIELDS),
    RateAnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(AssociationNullIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction, description="Exact declared significance level."),
        "guarantee": FieldSpec(Guarantee, description="The error-rate statement Lean proves."),
    },
    ObservedEventsIR: {
        "model": FieldSpec(PersonTimeStudyIR),
        "exposed_events": FieldSpec(int),
        "exposed_time": FieldSpec(Fraction, description="Exposed person-time."),
        "unexposed_events": FieldSpec(int),
        "unexposed_time": FieldSpec(Fraction, description="Unexposed person-time."),
    },
    RateResultIR: {
        "analysis": FieldSpec(RateAnalysisIR),
        "events": FieldSpec(ObservedEventsIR),
    },
    RateRatioIR: {"events": FieldSpec(ObservedEventsIR), "level": FieldSpec(Fraction)},
    ProportionIR: {
        "measure": FieldSpec(str, description="prevalence or cumulative_incidence."),
        "model": FieldSpec(StudyModelIR),
        "cases": FieldSpec(int),
        "level": FieldSpec(Fraction),
        "group": FieldSpec(str, optional=True, description="exposed or unexposed, if given."),
    },
    RateResultDetails: {
        "events": FieldSpec(int, description="Total events."),
        "p_value": FieldSpec(Fraction, description="Exact two-sided p-value."),
        "alpha": FieldSpec(Fraction),
        "reject_null": FieldSpec(bool),
        "test": FieldSpec(str),
    },
    MatchedStudyIR: {
        "pairs": FieldSpec(int, description="Pairs of one case and one control."),
        **STUDY_FIELDS,
    },
    MatchedAnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(AssociationNullIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction, description="Exact declared significance level."),
        "guarantee": FieldSpec(Guarantee, description="The error-rate statement Lean proves."),
    },
    MatchedPairsIR: {
        "model": FieldSpec(MatchedStudyIR),
        **{cell: FieldSpec(int) for cell in ("both_exposed", "case_exposed_only")},
        **{cell: FieldSpec(int) for cell in ("control_exposed_only", "neither_exposed")},
    },
    MatchedResultIR: {
        "analysis": FieldSpec(MatchedAnalysisIR),
        "pairs": FieldSpec(MatchedPairsIR, attribute="observed"),
    },
    MatchedIntervalIR: {
        "pairs": FieldSpec(MatchedPairsIR, attribute="observed"),
        "level": FieldSpec(Fraction),
    },
    MatchedResultDetails: {
        "discordant_pairs": FieldSpec(int),
        "p_value": FieldSpec(Fraction, description="Exact two-sided p-value."),
        "alpha": FieldSpec(Fraction),
        "reject_null": FieldSpec(bool),
        "test": FieldSpec(str),
    },
    CitedAssociationIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(AssociationNullIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction),
        "adjusted_for": FieldSpec("list", attribute="covariates"),
        "guarantee": FieldSpec(Guarantee, description="The cited error-rate statement."),
    },
    AssociationTableIR: {
        "model": FieldSpec(StudyModelIR),
        **{cell: FieldSpec(int) for cell in ("exposed_cases", "exposed_noncases")},
        **{cell: FieldSpec(int) for cell in ("unexposed_cases", "unexposed_noncases")},
    },
    AssociationResultIR: {
        "analysis": FieldSpec(AssociationAnalysisIR),
        "table": FieldSpec(AssociationTableIR),
    },
    EffectIntervalIR: {
        "measure": FieldSpec(str, description="odds_ratio, risk_ratio, prevalence_ratio, ..."),
        "table": FieldSpec(AssociationTableIR),
        "level": FieldSpec(Fraction),
    },
    AssociationResultDetails: {
        "p_value": FieldSpec(Fraction, description="Exact two-sided p-value."),
        "observed_table_probability": FieldSpec(Fraction),
        "alpha": FieldSpec(Fraction),
        "reject_null": FieldSpec(bool),
        "test": FieldSpec(str),
    },
    EffectIntervalDetails: {
        "measure": FieldSpec(str),
        "level": FieldSpec(Fraction),
        "arm_level": FieldSpec(Fraction, description="Level used for each group's interval."),
        "estimate": FieldSpec(Fraction, optional=True, description="Absent when undefined."),
        "lower": FieldSpec(Fraction),
        "upper": FieldSpec(Fraction, optional=True, description="Absent when unbounded."),
        "method": FieldSpec(str),
    },
    AssociationAnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(AssociationNullIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction, description="Exact declared significance level."),
        "guarantee": FieldSpec(Guarantee, description="The error-rate statement Lean proves."),
    },
    OutcomeIR: {
        "kind": FieldSpec(str, description="binary, continuous, survival, ..."),
        "better": BETTER,
        "name": FieldSpec(str, optional=True, description="The outcome's name, when declared."),
    },
    ModelIR: TWO_ARM_FIELDS,
    PlanIR: {"model": FieldSpec(StudyModelIR), "stopping": FieldSpec(str)},
    OutcomeModelIR: TWO_ARM_FIELDS,
    OutcomeNullIR: {
        "model": FieldSpec(OutcomeModelIR),
        "predicate": FieldSpec(str),
        "value": FieldSpec(Fraction),
        "statement": FieldSpec(str),
    },
    CitedAnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(NullIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction),
        "guarantee": FieldSpec(Guarantee, description="The cited error-rate statement."),
    },
    SharpNullIR: {
        "model": FieldSpec(StudyModelIR),
        "predicate": FieldSpec(str),
        "statement": FieldSpec(str),
    },
    RandomisationAnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(SharpNullIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction, description="Exact declared significance level."),
        "draws": FieldSpec(int, optional=True, description="Random draws, if Monte Carlo."),
        "guarantee": FieldSpec(Guarantee, description="The error-rate statement Lean proves."),
    },
    HypothesisIR: {
        "model": FieldSpec(ModelIR),
        "predicate": FieldSpec(str),
        "value": FieldSpec(Fraction),
        "statement": FieldSpec(str),
    },
    AnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(HypothesisIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction, description="Exact declared significance level."),
    },
    ComposedFamilyIR: {"analyses": FieldSpec("list"), "alpha": FieldSpec(Fraction)},
    SequentialIR: {
        "looks": FieldSpec("list", attribute="analyses"),
        "alpha": FieldSpec(Fraction, description="Overall error level across all looks."),
    },
    FamilyIR: {
        "analyses": FieldSpec("list"),
        "alpha": FieldSpec(Fraction),
        "joint_law": FieldSpec(str),
    },
    ObservationIR: {
        "analysis": FieldSpec(AnalysisIR),
        "control_successes": FieldSpec(int),
        "treatment_successes": FieldSpec(int),
    },
    ClaimIR: {
        "kind": FieldSpec(str),
        "subject": FieldSpec(object),
        "scope": FieldSpec(str, description="finite_sample or asymptotic."),
        "guarantee": FieldSpec(
            Guarantee, optional=True, description="Present when the claim is one error bound."
        ),
    },
    Guarantee: {
        "quantity": FieldSpec(str),
        "relation": FieldSpec(str, description="equals or at_most."),
        "bound": FieldSpec(Fraction),
        "null": FieldSpec(str),
        "scope": FieldSpec(str),
        "sentence": FieldSpec(str),
    },
    Evidence: {
        "grade": FieldSpec(str, description="proved, conditional, cited or simulated."),
        "sources": FieldSpec("list", description="Where the guarantee's statement comes from."),
        "machine_checked": FieldSpec(str, description="guarantee, composition or contract."),
        "claim": FieldSpec(ClaimIR),
        "certificate": FieldSpec(
            CertificateReference, optional=True, description="Absent for cited evidence."
        ),
        "references": FieldSpec("list", description="Publications a cited guarantee rests on."),
        "established_properties": FieldSpec("list"),
        "required_assumptions": FieldSpec("list"),
    },
    CertificateReference: {
        name: FieldSpec(str) for name in ("certificate_id", "file", "directory", "sha256")
    },
    CalculationDetails: {
        "p_value": FieldSpec(Fraction),
        "alpha": FieldSpec(Fraction),
        "observed_table_probability": FieldSpec(Fraction),
        "p_value_le_alpha": FieldSpec(bool),
        "test": FieldSpec(str),
        "test_version": FieldSpec(str),
    },
    RatesIR: {
        "p_control": FieldSpec(Fraction),
        "p_treatment": FieldSpec(Fraction),
        "icc": FieldSpec(
            Fraction, optional=True, description="Intracluster correlation, for cluster tests."
        ),
        "cluster_size_cv": FieldSpec(
            Fraction, optional=True, description="How much cluster sizes vary, for simulation."
        ),
    },
    RateIR: {"value": FieldSpec(Fraction)},
    MeanDifferenceIR: {
        "value": FieldSpec(Fraction, description="True mean difference, treatment minus control."),
        "sd": FieldSpec(Fraction, description="Standard deviation of one participant's outcome."),
        "icc": FieldSpec(
            Fraction, optional=True, description="Intracluster correlation, for cluster tests."
        ),
        "cluster_size_cv": FieldSpec(
            Fraction, optional=True, description="How much cluster sizes vary, for simulation."
        ),
        "sd_treatment": FieldSpec(
            Fraction, optional=True, description="The treatment arm's SD, for simulation."
        ),
        "skewness": FieldSpec(
            Fraction, optional=True, description="The outcome's skewness, for simulation."
        ),
    },
    ExponentialSurvivalIR: {
        "hazard_ratio": FieldSpec(Fraction, description="Hazard ratio, treatment over control."),
        "control_median": FieldSpec(Fraction, description="Median time to the event in control."),
        "accrual": FieldSpec(Fraction, description="Time over which participants enter."),
        "follow_up": FieldSpec(Fraction, description="Follow-up after accrual ends."),
        "dropout": FieldSpec(
            Fraction, optional=True, description="Probability of dropping out by dropout_time."
        ),
        "dropout_time": FieldSpec(Fraction, optional=True),
    },
    CorrelationIR: {"value": FieldSpec(Fraction, description="Correlation of the two variables.")},
    OutcomeMeansIR: {
        "unexposed": FieldSpec(Fraction, description="Outcome's mean without the exposure."),
        "exposed": FieldSpec(Fraction, description="Outcome's mean with the exposure."),
        "sd": FieldSpec(Fraction, description="Outcome's standard deviation about the means."),
        "exposed_share": FieldSpec(
            Fraction, optional=True, description="Probability that a participant is exposed."
        ),
        "design_effect": FieldSpec(
            Fraction, optional=True, description="A survey's design effect, a planning input."
        ),
    },
    OddsPerSdIR: {
        "odds_ratio": FieldSpec(Fraction, description="Odds ratio per SD of the exposure."),
        "baseline": FieldSpec(Fraction, description="Outcome's probability at the mean exposure."),
        "exposure_r2": FieldSpec(
            Fraction, optional=True, description="Share of the exposure the covariates explain."
        ),
        "design_effect": FieldSpec(
            Fraction, optional=True, description="A survey's design effect, a planning input."
        ),
    },
    SlopeIR: {
        "value": FieldSpec(Fraction, description="Change in the outcome per unit of exposure."),
        "exposure_sd": FieldSpec(Fraction, description="Standard deviation of the exposure."),
        "residual_sd": FieldSpec(Fraction, description="Outcome's SD about the regression."),
        "exposure_r2": FieldSpec(
            Fraction, optional=True, description="Share of the exposure the covariates explain."
        ),
        "design_effect": FieldSpec(
            Fraction, optional=True, description="A survey's design effect, a planning input."
        ),
    },
    HazardRatioIR: {
        "value": FieldSpec(Fraction, description="True hazard ratio, treatment over control."),
        "events": FieldSpec(int, description="Expected total number of events."),
    },
    RisksIR: {
        "unexposed": FieldSpec(Fraction, description="Risk of the outcome without exposure."),
        "exposed": FieldSpec(Fraction, description="Risk of the outcome with exposure."),
        "exposed_share": FieldSpec(
            Fraction, optional=True, description="Probability that a participant is exposed."
        ),
    },
    OutcomePrevalenceIR: {
        "unexposed": FieldSpec(Fraction, description="Prevalence without exposure."),
        "exposed": FieldSpec(Fraction, description="Prevalence with exposure."),
        "exposed_share": FieldSpec(
            Fraction, description="Probability that a participant is exposed."
        ),
        "design_effect": FieldSpec(
            Fraction, optional=True, description="A survey's design effect, a planning input."
        ),
    },
    TotalCandidatesIR: {
        "analysis": FieldSpec(PlannableIR),
        "min_n": FieldSpec(int),
        "max_n": FieldSpec(int),
    },
    ExposurePrevalenceIR: {
        "controls": FieldSpec(Fraction, description="Share of controls who were exposed."),
        "cases": FieldSpec(Fraction, description="Share of cases who were exposed."),
    },
    GroupCandidatesIR: {
        "analysis": FieldSpec(AssociationAnalysisIR),
        "min_size": FieldSpec(int, description="Fewest exposed participants or cases."),
        "max_size": FieldSpec(int, description="Most exposed participants or cases."),
        "ratio": FieldSpec(int, description="Unexposed per exposed, or controls per case."),
    },
    DiscordantPairsIR: {
        "share": FieldSpec(Fraction, description="Probability that a pair is discordant."),
        "odds_ratio": FieldSpec(Fraction, description="Conditional odds ratio."),
    },
    IncidenceRatesIR: {
        "rate_ratio": FieldSpec(Fraction, description="Rate ratio, exposed over unexposed."),
        "exposed_time": FieldSpec(Fraction, description="Expected exposed person-time."),
        "unexposed_time": FieldSpec(Fraction, description="Expected unexposed person-time."),
        "events": FieldSpec(int, optional=True, description="Total number of events."),
    },
    ClusterCandidatesIR: {
        "analysis": FieldSpec(TwoArmTestIR),
        "min_size": FieldSpec(
            int, attribute="low", description="Fewest clusters per arm, or participants each."
        ),
        "max_size": FieldSpec(
            int, attribute="high", description="Most clusters per arm, or participants each."
        ),
        "cluster_size": FieldSpec(
            int, optional=True, description="Participants per cluster, when clusters vary."
        ),
    },
    CountCandidatesIR: {
        "analysis": FieldSpec(PlannableIR),
        "min_size": FieldSpec(int, description="Fewest pairs or events."),
        "max_size": FieldSpec(int, description="Most pairs or events."),
    },
    MatchedPowerDetails: {
        "pairs": FieldSpec(int, optional=True),
        "discordant": FieldSpec(Fraction, optional=True),
        "odds_ratio": FieldSpec(Fraction, optional=True),
        "case_exposed_share": FieldSpec(
            Fraction, optional=True, description="Share of discordant pairs with the case exposed."
        ),
        "expected_discordant_pairs": FieldSpec(Fraction, optional=True),
        "power": FieldSpec(
            Fraction, optional=True, description="Exact calculated power; not checked evidence."
        ),
        "power_target_met": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    RatePowerDetails: {
        "events": FieldSpec(int, optional=True),
        "rate_ratio": FieldSpec(Fraction, optional=True),
        "exposed_time_share": FieldSpec(Fraction, optional=True),
        "exposed_event_share": FieldSpec(
            Fraction, optional=True, description="Share of events among the exposed at the point."
        ),
        "power": FieldSpec(
            Fraction, optional=True, description="Exact calculated power, given the events."
        ),
        "power_target_met": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    AssociationPowerDetails: {
        "design": FieldSpec(str, optional=True),
        "exposed": FieldSpec(int, optional=True),
        "unexposed": FieldSpec(int, optional=True),
        "cases": FieldSpec(int, optional=True),
        "controls": FieldSpec(int, optional=True),
        "total_sample_size": FieldSpec(int, optional=True),
        "risk_ratio": FieldSpec(
            Fraction, optional=True, description="Risk ratio at the planning point (cohort)."
        ),
        "risk_difference": FieldSpec(
            Fraction, optional=True, description="Risk difference at the planning point (cohort)."
        ),
        "prevalence_ratio": FieldSpec(
            Fraction, optional=True, description="Prevalence ratio at the point (cross-sectional)."
        ),
        "prevalence_difference": FieldSpec(Fraction, optional=True),
        "exposed_share": FieldSpec(
            Fraction, optional=True, description="Probability that a participant is exposed."
        ),
        "expected_exposed": FieldSpec(Fraction, optional=True),
        "odds_ratio": FieldSpec(
            Fraction, optional=True, description="Odds ratio at the planning point, when finite."
        ),
        "power": FieldSpec(
            Fraction, optional=True, description="Exact calculated power; not checked evidence."
        ),
        "power_target_met": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    SingleProportionIR: {
        "value": FieldSpec(Fraction, description="The proportion, such as a prevalence."),
        "design_effect": FieldSpec(
            Fraction, optional=True, description="A survey's design effect, a planning input."
        ),
        "population_size": FieldSpec(int, optional=True, description="Population sampled."),
    },
    PrecisionTargetIR: {
        "at": FieldSpec(PlanningPointIR),
        "level": FieldSpec(Fraction, description="The interval's confidence level."),
        "margin_of_error": FieldSpec(
            Fraction, optional=True, attribute="margin", description="Half the width at most."
        ),
        "relative_margin_of_error": FieldSpec(
            Fraction, optional=True, attribute="relative", description="Fraction of the value."
        ),
        "assurance": FieldSpec(
            Fraction, optional=True, description="Chance the interval is narrow enough."
        ),
    },
    PlannedIntervalIR: {
        "model": FieldSpec(EstimableModelIR),
        "measure": FieldSpec(str),
        "method": FieldSpec(str, description="exact or normal."),
        "group": FieldSpec(str, optional=True),
    },
    IntervalCandidatesIR: {
        "interval": FieldSpec(PlannedIntervalIR),
        "min_size": FieldSpec(int),
        "max_size": FieldSpec(int),
        "ratio": FieldSpec(int, description="Of the second group for each of the first."),
    },
    PrecisionDetails: {
        "total_sample_size": FieldSpec(int, optional=True),
        "n_control": FieldSpec(int, optional=True),
        "n_treatment": FieldSpec(int, optional=True),
        "exposed": FieldSpec(int, optional=True),
        "unexposed": FieldSpec(int, optional=True),
        "cases": FieldSpec(int, optional=True),
        "controls": FieldSpec(int, optional=True),
        "pairs": FieldSpec(int, optional=True),
        "events": FieldSpec(int, optional=True),
        "measure": FieldSpec(str, optional=True),
        "method": FieldSpec(str, optional=True),
        "level": FieldSpec(Fraction, optional=True),
        "estimate": FieldSpec(Fraction, optional=True, description="At the planning point."),
        "lower": FieldSpec(Fraction, optional=True, description="At the expected counts."),
        "upper": FieldSpec(
            Fraction, optional=True, description="At the expected counts; absent if unbounded."
        ),
        "relative": FieldSpec(bool, optional=True),
        "margin_achieved": FieldSpec(
            Fraction, optional=True, description="Margin at the expected counts, six decimals."
        ),
        "target_margin": FieldSpec(Fraction, optional=True),
        "assurance": FieldSpec(
            Fraction, optional=True, description="Chance the interval is narrow enough."
        ),
        "minimum_assurance": FieldSpec(Fraction, optional=True),
        "precision_target_met": FieldSpec(bool),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "note": FieldSpec(str, optional=True),
    },
    PowerTargetIR: {
        "at": FieldSpec(PlanningPointIR),
        "minimum": FieldSpec(Fraction, description="Required power at the planning point."),
        "maximum_typeI": FieldSpec(Fraction, description="Requested Type I error bound."),
    },
    FeasibilityIR: {"analysis": FieldSpec(PlannableIR), "target": FieldSpec(TargetIR)},
    CandidatesIR: {
        "analysis": FieldSpec(TwoArmTestIR),
        "min_per_arm": FieldSpec(int),
        "max_per_arm": FieldSpec(int),
        "ratio": FieldSpec(int, description="Treated participants per control."),
    },
    SizingIR: {"candidates": FieldSpec(CandidateSpaceIR), "target": FieldSpec(TargetIR)},
    OneArmModelIR: {"n": FieldSpec(int)},
    OneSampleAnalysisIR: {
        "model": FieldSpec(OneArmModelIR),
        "null_rate": FieldSpec(Fraction),
        "alpha": FieldSpec(Fraction),
    },
    OneSampleObservationIR: {
        "analysis": FieldSpec(OneSampleAnalysisIR),
        "responses": FieldSpec(int),
    },
    OneSampleResultDetails: {
        "n": FieldSpec(int),
        "responses": FieldSpec(int),
        "critical_value": FieldSpec(int),
        "p_value": FieldSpec(Fraction, description="Exact one-sided p-value."),
        "alpha": FieldSpec(Fraction),
        "reject_null": FieldSpec(bool),
        "test": FieldSpec(str),
    },
    DifferenceIntervalIR: {
        "model": FieldSpec(ModelIR),
        "control_successes": FieldSpec(int),
        "treatment_successes": FieldSpec(int),
        "level": FieldSpec(Fraction),
    },
    DifferenceDetails: {
        "level": FieldSpec(Fraction),
        "arm_level": FieldSpec(Fraction, description="Level used for each arm's interval."),
        "estimate": FieldSpec(Fraction),
        "lower": FieldSpec(Fraction),
        "upper": FieldSpec(Fraction),
        "method": FieldSpec(str),
    },
    MarginDetails: {
        "n_control": FieldSpec(int, optional=True),
        "n_treatment": FieldSpec(int, optional=True),
        "total_sample_size": FieldSpec(int, optional=True),
        "margin": FieldSpec(Fraction, optional=True),
        "thresholds": FieldSpec(
            "list",
            optional=True,
            description="Treatment successes needed to reject, by control successes.",
        ),
        "needed_treatment_successes": FieldSpec(int, optional=True),
        "typeI_bound": FieldSpec(Fraction, optional=True),
        "cells": FieldSpec(int, optional=True, description="Intervals used to bound the error."),
        "power": FieldSpec(Fraction, optional=True),
        "power_target_met": FieldSpec(bool, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "control_successes": FieldSpec(int, optional=True),
        "treatment_successes": FieldSpec(int, optional=True),
        "observed_difference": FieldSpec(Fraction, optional=True),
        "reject_null": FieldSpec(bool, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
    },
    IntervalIR: {
        "model": FieldSpec(OneArmModelIR),
        "responses": FieldSpec(int),
        "level": FieldSpec(Fraction),
    },
    IntervalDetails: {
        "n": FieldSpec(int),
        "responses": FieldSpec(int),
        "level": FieldSpec(Fraction),
        "estimate": FieldSpec(Fraction),
        "lower": FieldSpec(Fraction, description="Lower endpoint, rounded down."),
        "upper": FieldSpec(Fraction, description="Upper endpoint, rounded up."),
        "method": FieldSpec(str),
    },
    OneArmCandidatesIR: {
        "analysis": FieldSpec(OneSampleAnalysisIR),
        "min_n": FieldSpec(int),
        "max_n": FieldSpec(int),
    },
    OneSampleDetails: {
        "n": FieldSpec(int, optional=True),
        "critical_value": FieldSpec(
            int, optional=True, description="Smallest response count that rejects."
        ),
        "typeI": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "power": FieldSpec(Fraction, optional=True),
        "power_target_met": FieldSpec(bool),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    TwoStageModelIR: {"n_stage1": FieldSpec(int), "n_stage2": FieldSpec(int)},
    PriorIR: {"a": FieldSpec(int), "b": FieldSpec(int)},
    RuleIR: {"kind": FieldSpec(str)},
    TwoStageAnalysisIR: {
        "design": FieldSpec(TwoStageModelIR),
        "rule": FieldSpec(RuleIR),
        "null_rate": FieldSpec(Fraction),
    },
    PlanningDetails: {
        "n_control": FieldSpec(int, optional=True),
        "n_treatment": FieldSpec(int, optional=True),
        "total_sample_size": FieldSpec(int, optional=True),
        "power": FieldSpec(
            Fraction, optional=True, description="Exact calculated power; not checked evidence."
        ),
        "power_target_met": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    SimulationDetails: {
        "n_control": FieldSpec(int, optional=True),
        "n_treatment": FieldSpec(int, optional=True),
        "total_sample_size": FieldSpec(int, optional=True),
        "power": FieldSpec(
            Fraction,
            optional=True,
            description="Share of simulated studies in which the test rejected at the planning "
            "point. An estimate with Monte Carlo error; not a bound.",
        ),
        "power_lower": FieldSpec(
            Fraction, optional=True, description="Lower end of the 95% interval for power."
        ),
        "power_upper": FieldSpec(
            Fraction, optional=True, description="Upper end of the 95% interval for power."
        ),
        "power_target_met": FieldSpec(
            bool, description="Whether the whole 95% interval is at or above the minimum."
        ),
        "typeI": FieldSpec(
            Fraction,
            optional=True,
            description="Share of simulated studies at the null's boundary in which the test "
            "rejected. An estimate.",
        ),
        "typeI_lower": FieldSpec(Fraction, optional=True),
        "typeI_upper": FieldSpec(Fraction, optional=True),
        "alpha": FieldSpec(Fraction, optional=True, description="The test's declared level."),
        "typeI_target_met": FieldSpec(
            bool, optional=True, description="Whether alpha is at most maximum_typeI."
        ),
        "runs": FieldSpec(int, optional=True, description="Simulated studies per estimate."),
        "seed": FieldSpec(int, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "clusters_control": FieldSpec(int, optional=True),
        "clusters_treatment": FieldSpec(int, optional=True),
        "total_clusters": FieldSpec(int, optional=True),
        "cluster_size_control": FieldSpec(
            Fraction, optional=True, description="Mean participants per control cluster."
        ),
        "cluster_size_treatment": FieldSpec(
            Fraction, optional=True, description="Mean participants per treated cluster."
        ),
        "icc": FieldSpec(Fraction, optional=True, description="Intracluster correlation."),
        "cluster_size_cv": FieldSpec(
            Fraction, optional=True, description="Coefficient of variation of cluster sizes."
        ),
        "degrees_of_freedom": FieldSpec(int, optional=True),
        "typeI_judged": FieldSpec(
            bool,
            optional=True,
            description="Whether Type I is judged on the simulation, as in a scenario that "
            "leaves normal outcomes with a common SD.",
        ),
    },
    ApproximatePowerDetails: {
        "n_control": FieldSpec(int, optional=True),
        "n_treatment": FieldSpec(int, optional=True),
        "total_sample_size": FieldSpec(int, optional=True),
        "clusters_control": FieldSpec(int, optional=True),
        "clusters_treatment": FieldSpec(int, optional=True),
        "total_clusters": FieldSpec(int, optional=True),
        "cluster_size_control": FieldSpec(
            Fraction, optional=True, description="Mean participants per control cluster."
        ),
        "cluster_size_treatment": FieldSpec(
            Fraction, optional=True, description="Mean participants per treated cluster."
        ),
        "icc": FieldSpec(Fraction, optional=True, description="Intracluster correlation."),
        "design_effect": FieldSpec(
            Fraction,
            optional=True,
            description="1 + (m - 1) icc for clusters of m: how much clustering inflates the "
            "variance of a mean.",
        ),
        "degrees_of_freedom": FieldSpec(int, optional=True),
        "covariates": FieldSpec(int, optional=True, description="Covariates adjusted for."),
        "effective_sample_size": FieldSpec(
            Fraction, optional=True, description="n over the survey's design effect."
        ),
        "exposed": FieldSpec(int, optional=True),
        "unexposed": FieldSpec(int, optional=True),
        "cases": FieldSpec(int, optional=True),
        "controls": FieldSpec(int, optional=True),
        "pairs": FieldSpec(int, optional=True),
        "events": FieldSpec(int, optional=True),
        "expected_events": FieldSpec(
            Fraction,
            optional=True,
            description="Events expected by the analysis, from the survival times; six decimals.",
        ),
        "event_probability_control": FieldSpec(Fraction, optional=True),
        "event_probability_treatment": FieldSpec(Fraction, optional=True),
        "power": FieldSpec(
            Fraction,
            optional=True,
            description="Approximate power from the formula, to six decimals. Not a bound.",
        ),
        "power_ceiling": FieldSpec(
            Fraction,
            optional=True,
            description="Power as clusters grow without bound, when no cluster size is enough.",
        ),
        "power_target_met": FieldSpec(bool),
        "critical_estimate": FieldSpec(
            Fraction,
            optional=True,
            description="The value the estimate must pass for the test to reject, to six decimals.",
        ),
        "reject_when": FieldSpec(
            str, optional=True, description="above or below the critical estimate."
        ),
        "standard_error": FieldSpec(
            Fraction,
            optional=True,
            description="Standard error at the planning point; for a hazard ratio, of its log.",
        ),
        "alpha": FieldSpec(Fraction, optional=True, description="The test's declared level."),
        "typeI_target_met": FieldSpec(
            bool, optional=True, description="Whether alpha is at most maximum_typeI."
        ),
        "formula": FieldSpec(str, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
    },
    TwoStageObservationIR: {
        "analysis": FieldSpec(TwoStageAnalysisIR),
        "stage1_responses": FieldSpec(int),
        "stage2_responses": FieldSpec(int, optional=True),
    },
    StageResultDetails: {
        "n_stage1": FieldSpec(int),
        "n_stage2": FieldSpec(int),
        "stage1_responses": FieldSpec(int),
        "stage2_responses": FieldSpec(int, optional=True),
        "continued": FieldSpec(bool),
        "reject_null": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, description="Checked bound on the design's error."),
    },
    TwoStageCandidatesIR: {
        "null_rate": FieldSpec(Fraction),
        "max_total": FieldSpec(int),
        "criterion": FieldSpec(str),
    },
    PolicyDetails: {
        "n_stage1": FieldSpec(int, optional=True),
        "n_stage2": FieldSpec(int, optional=True),
        "continue_above": FieldSpec(int, optional=True),
        "reject_above": FieldSpec(int, optional=True),
        "maximum_sample_size": FieldSpec(int, optional=True),
        "typeI": FieldSpec(
            Fraction, optional=True, description="Exact rejection probability at the null rate."
        ),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "power": FieldSpec(Fraction, optional=True),
        "power_target_met": FieldSpec(bool),
        "expected_sample_size_null": FieldSpec(Fraction, optional=True),
        "expected_sample_size_alternative": FieldSpec(Fraction, optional=True),
        "early_stop_probability_null": FieldSpec(Fraction, optional=True),
        "criterion": FieldSpec(str, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
    },
    Diagnostic: {"code": FieldSpec(str), "message": FieldSpec(str), "severity": FieldSpec(str)},
}
COMMON_RESULT = {
    "request_id": FieldSpec(int),
    "claim": FieldSpec(ClaimIR),
    "source_sha256": FieldSpec(str),
    "status": FieldSpec(str, description="Execution status, not a boolean proof of a proposition."),
    "diagnostics": FieldSpec("list"),
}
VERIFICATION_FIELDS = {
    **COMMON_RESULT,
    "evidence": FieldSpec(
        Evidence,
        optional=True,
        description="Evidence after a verified or cited result; read its grade. "
        "Absent on unmet requirements or backend errors; unevaluated during compilation. "
        "Optional field access propagates absence.",
    ),
}
CALCULATION_FIELDS = {
    **COMMON_RESULT,
    "calculation": FieldSpec(CalculationDetails, optional=True),
    "decision": FieldSpec(str, optional=True),
}
for kind in (VerificationResultIR, VerificationResult):
    SCHEMAS[kind] = VERIFICATION_FIELDS
for kind in (CalculationResultIR, CalculationResult):
    SCHEMAS[kind] = CALCULATION_FIELDS


def details_kind(claim: ClaimIR, operation: str = "calculate") -> type:
    """The calculation record published for this claim's kind and the request's operation."""
    if operation == "simulate":
        return SimulationDetails
    if isinstance(claim.subject, TwoStageObservationIR):
        return StageResultDetails
    margin = claim.subject
    if isinstance(margin, ObservationIR):
        margin = margin.analysis
    elif isinstance(margin, FeasibilityIR):
        margin = margin.analysis
    elif isinstance(margin, SizingIR):
        margin = getattr(margin.candidates, "analysis", None)
    if isinstance(margin, AnalysisIR) and margin.alternative == "margin":
        return MarginDetails
    if isinstance(claim.subject, DifferenceIntervalIR):
        return DifferenceDetails
    if isinstance(claim.subject, (EffectIntervalIR, MatchedIntervalIR, RateRatioIR, ProportionIR)):
        return EffectIntervalDetails
    if isinstance(claim.subject, RateResultIR):
        return RateResultDetails
    if isinstance(claim.subject, MatchedResultIR):
        return MatchedResultDetails
    if isinstance(claim.subject, AssociationResultIR):
        return AssociationResultDetails
    if isinstance(claim.subject, IntervalIR):
        return IntervalDetails
    if isinstance(claim.subject, OneSampleObservationIR):
        return OneSampleResultDetails
    if claim.kind not in ("meets", "sample_size"):
        return CalculationDetails
    subject = claim.subject
    analysis = (
        subject.analysis if isinstance(subject, FeasibilityIR) else subject.candidates.analysis
    )
    if isinstance(analysis, PlannedIntervalIR):
        return PrecisionDetails
    if isinstance(analysis, (CitedAnalysisIR, CitedAssociationIR)):
        return ApproximatePowerDetails
    if isinstance(analysis, AssociationAnalysisIR):
        return AssociationPowerDetails
    if isinstance(analysis, MatchedAnalysisIR):
        return MatchedPowerDetails
    if isinstance(analysis, RateAnalysisIR):
        return RatePowerDetails
    if isinstance(analysis, OneSampleAnalysisIR):
        return OneSampleDetails
    if isinstance(analysis, TwoStageAnalysisIR):
        return PolicyDetails
    return PlanningDetails


def fields_for(value: object) -> dict[str, FieldSpec]:
    kind = value.value_type.kind if isinstance(value, FieldIR) else type(value)
    fields = SCHEMAS.get(kind, {})
    if isinstance(value, ClaimIR):
        return {**fields, "subject": FieldSpec(type(value.subject))}
    return fields


def read_field(value: object, name: str, span: Span) -> object:
    """Read only the published schema; never arbitrary Python attributes."""
    spec = fields_for(value).get(name)
    if spec is None:
        fail("unknown_field", f"{type(value).__name__} has no public field {name!r}.", span)
    if isinstance(value, Evidence) and name == "certificate":
        if value.certificate is None:
            return None
        return CertificateReference(**dict(value.certificate))
    if isinstance(value, CalculationResult) and name == "calculation":
        if value.calculation is None:
            return None
        return details_kind(value.claim, value.operation)(value.calculation)
    if isinstance(value, (FamilyIR, ComposedFamilyIR)) and name in ("analyses", "looks"):
        return tuple(LocatedValue(analysis, span, label) for label, analysis in value.analyses)
    return getattr(value, spec.attribute or name)


def project(value: object, name: str, span: Span, requests) -> object:
    if value is None:
        fail("absent_value", f"There is no value here to read {name!r} from.", span)
    spec = fields_for(value).get(name)
    if spec is None:
        kind = (
            value.value_type.label
            if isinstance(value, FieldIR)
            else type(value).__name__.removesuffix("IR")
        )
        available = ", ".join(fields_for(value)) or "none"
        fail(
            "unknown_field",
            f"{kind} has no public field {name!r}. Available fields: {available}.",
            span,
        )
    if isinstance(value, (VerificationResultIR, CalculationResultIR)) and name == "claim":
        return requests[value.request_id - 1].claim
    if isinstance(value, CalculationResultIR) and name == "calculation":
        request = requests[value.request_id - 1]
        kind = details_kind(request.claim, request.operation)
        return FieldIR(value, name, ValueType(kind, True), span)
    if isinstance(value, (FieldIR, VerificationResultIR, CalculationResultIR)):
        optional = spec.optional or (isinstance(value, FieldIR) and value.value_type.optional)
        return FieldIR(value, name, ValueType(spec.kind, optional), span)
    return read_field(value, name, span)
