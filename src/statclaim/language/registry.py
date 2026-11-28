"""Every module a .stat file can use, with its constructors and documentation."""

from statclaim.association import (
    CELLS,
    MEASURES,
)
from statclaim.incidence import (
    MAX_EVENTS,
    PROPORTIONS,
)
from statclaim.language.analyses import (
    _association_result,
    _case_control,
    _cited_association_constructor,
    _cited_test,
    _claim,
    _cohort,
    _conditional_odds_ratio,
    _cross_sectional,
    _declared_test,
    _difference,
    _difference_test,
    _effect_interval,
    _family,
    _familywise,
    _farrington_manning,
    _fisher,
    _fisher_exact,
    _fixed_sequence,
    _graphical,
    _group_sequential,
    _likelihood_ratio_test,
    _matched_case_control,
    _matched_result,
    _mcnemar,
    _mcnemar_asymptotic,
    _no_association,
    _no_effect,
    _observe,
    _observed_events,
    _observed_pairs,
    _observed_table,
    _pearson_test,
    _person_time_cohort,
    _proportion,
    _proportion_z,
    _randomisation_test,
    _rate_ratio,
    _rate_result,
    _rate_test,
    _sequential,
)
from statclaim.language.checks import (
    _interval_sizes,
    _meets,
    _planned_interval,
    _precision_target,
    _single_proportion,
)
from statclaim.language.core import (
    Constructor,
    Module,
    _constructor,
)
from statclaim.language.coverage import (
    APPROXIMATE,
    ASSOCIATION,
    BINOMIAL,
    CITED,
    COMPOSITION,
    CORE,
    INCIDENCE,
    INTERVAL,
    INTERVALS,
    MATCHED,
    METHODS,
    ONE_SAMPLE,
    OUTCOME_LAWS,
    PLANS,
    POLICY,
    PRECISION,
    PREMISES,
    PROGRAM,
    RANDOMISATION,
    RESULTS,
    TWO_STAGE,
    NotInLean,
    in_lean,
)
from statclaim.language.designs import (
    _assignment,
    _cluster_assignment,
    _model_from_sizes,
    _outcome_null,
    _outcome_piece,
    _stratum,
    _two_arm,
)
from statclaim.language.ir import (
    AnalysisIR,
    AssignmentIR,
    AssociationAnalysisIR,
    AssociationNullIR,
    AssociationTableIR,
    CandidateSpaceIR,
    CitedAnalysisIR,
    ClaimIR,
    EstimableModelIR,
    FamilyLikeIR,
    FarringtonManningAnalysisIR,
    HypothesisIR,
    LevelTestIR,
    LikelihoodRatioAnalysisIR,
    MatchedAnalysisIR,
    MatchedPairsIR,
    MatchedStudyIR,
    ModelIR,
    NullIR,
    NullScenariosIR,
    ObservationalStudyIR,
    ObservationIR,
    ObservedEventsIR,
    OneArmModelIR,
    OneSampleAnalysisIR,
    OneSampleObservationIR,
    OutcomeIR,
    OutcomeModelIR,
    PearsonAnalysisIR,
    PersonTimeStudyIR,
    PlanIR,
    PlannableIR,
    PlannedIntervalIR,
    PlanningPointIR,
    PriorIR,
    RateAnalysisIR,
    RateIR,
    RuleIR,
    ScoreAnalysisIR,
    SequentialIR,
    StudyModelIR,
    TargetIR,
    TwoArmTestIR,
    TwoStageAnalysisIR,
    TwoStageModelIR,
    TwoStageObservationIR,
    WaldAnalysisIR,
)
from statclaim.language.operations import (
    _calculation,
    _simulation,
    _verification,
)
from statclaim.language.points import (
    _correlation,
    _count_sizes,
    _discordant_pairs,
    _endpoint_points,
    _exponential_survival,
    _exposure_prevalence,
    _group_sizes,
    _hazard_ratio,
    _incidence_rates,
    _mean_difference,
    _null_scenarios,
    _odds_per_sd,
    _outcome_means,
    _outcome_prevalence,
    _power_target,
    _probability,
    _rates,
    _reestimation,
    _risks,
    _slope,
    _total_sizes,
)
from statclaim.language.searches import (
    _allocated,
    _binomial_score_test,
    _binomial_test,
    _candidates,
    _cluster_counts,
    _cluster_sizes,
    _difference_interval,
    _interval,
    _look_sizes,
    _one_arm,
    _one_arm_candidates,
    _posterior_rule,
    _prior,
    _responses,
    _sizing,
    _stage_data,
    _threshold_rule,
    _two_stage_candidates,
    _two_stage_model,
    _two_stage_test,
)
from statclaim.language_contracts import (
    FISHER_CONTRACT,
    MARGIN_CONTRACT,
    ONE_SIDED_FISHER_CONTRACT,
    RANDOMISATION_CONTRACT,
    HypothesisContract,
)
from statclaim.matched import (
    PAIR_CELLS,
)
from statclaim.methods import METHOD_MODULES, NULL_FORMS, OUTCOMES, SHARP_NULL, methods_for
from statclaim.methods.core import CitedMethod
from statclaim.methods.observational import (
    CORRELATION,
    REGRESSION,
    SURVEY,
)
from statclaim.observational_planning import (
    MAX_PLANNED_PAIRS,
)

# Always available, with the same argument checking as module constructors.
# Their builders validate claims only; evaluate records execution slots below.
OPERATIONS = {
    "verify": _constructor(
        "verify",
        (("claim", ClaimIR),),
        "VerificationResult",
        _verification,
        lean=in_lean("operation", PROGRAM),
    ),
    "calculate": _constructor(
        "calculate",
        (("claim", ClaimIR),),
        "CalculationResult",
        _calculation,
        lean=NotInLean("A calculation gives numbers, not a proposition to prove."),
    ),
    "simulate": _constructor(
        "simulate",
        (("claim", ClaimIR), ("seed", int), ("runs", int, True)),
        "CalculationResult",
        _simulation,
        documentation=(
            "Estimate power by simulating the study runs times from seed, for a cited test "
            "with a simulation model. Gives estimates with 95% intervals; never evidence."
        ),
        lean=NotInLean("A simulation gives estimates with Monte Carlo error, never proof."),
    ),
}

# What each operation needs to run. "lean" builds a formal proof, so it needs a StatClaim
# checkout with Lean; "python" runs wherever StatClaim runs, including the web studio,
# which reports a "lean" operation as needing Lean. A test checks every operation is here.
OPERATION_BACKENDS = {"verify": "lean", "calculate": "python", "simulate": "python"}


FAMILYWISE = _constructor(
    "familywise",
    (("family", FamilyLikeIR),),
    "FamilywiseClaim",
    _familywise,
    lean=in_lean("claim", PROGRAM, COMPOSITION),
)


# One constructor shared by every module whose analyses carry a Type I claim.
TYPE_I = _constructor(
    "typeI",
    (("analysis", LevelTestIR),),
    "TypeIClaim",
    _claim("typeI", "analysis"),
    lean=in_lean("claim", PROGRAM, CORE, POLICY),
)


def _cited_contract(method: CitedMethod) -> HypothesisContract:
    """Built from the registry, so the guidance always lists the current alternatives."""
    value = "value" if method.null_value is None else method.null_value
    statements = " or ".join(
        NULL_FORMS[null][1].statement.format(value=value) for null in method.nulls
    )
    others = "; ".join(
        f"{other.key} takes {' or '.join(other.nulls)}" for other in methods_for(method.outcome)
    )
    fixed = "" if method.null_value is None else f", with value {method.null_value}"
    return HypothesisContract(
        method.nulls,
        statements,
        f"{method.title} supports the null {' or '.join(method.nulls)}{fixed}. Keep your null "
        f"if it states your question, and choose the test that supports it. For this "
        f"outcome: {others}.",
        required_value=method.null_value,
        version=method.version,
    )


def _cited_constructor(method: CitedMethod) -> Constructor:
    contract = _cited_contract(method)
    return _constructor(
        method.key,
        (("design", PlanIR), ("null", NullIR), ("alpha", "level")),
        "CitedAnalysis",
        _cited_test(method),
        hypothesis_contract=contract,
        lean=CITED,
        documentation=f"{method.title}. Its guarantee is cited from the literature and is "
        f"not checked by Lean. Null: {contract.expected}.",
    )


BETTER_DOCUMENTATION = (
    'better is "higher" or "lower": which direction of the outcome is better. When given, '
    "a one-sided null must ask whether the treatment is better in that direction. When "
    "left out, a one-sided null's direction is listed as an assumption."
)


DECLARED_MODULE_SUMMARY = (
    "A test the author names and vouches for, for analyses StatClaim has no contract for. "
    "Only its fit to the design is checked: the null and the design must describe the same "
    "model. Its result has the status 'declared', the weakest, and any plan that contains it "
    "reports that status."
)


RANDOMISATION_DOCUMENTATION = (
    'randomisation is "complete" when every split of the units into arms of these sizes was '
    'equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each '
    'stratum; "blocked" with block_size=... (and optional strata) when it holds within each '
    "block of that size. Strata and blocks count randomised units. Leave it out otherwise; "
    "only randomisation_test reads it, and it refuses an assignment without it."
)


POPULATION_DOCUMENTATION = (
    'population says who is analysed: "randomised" for everyone randomised, in the arm they '
    'were assigned to (intention to treat), or "per_protocol" when participants excluded '
    "after randomisation are left out, with the arm sizes counting those analysed. "
    'randomisation_test needs "randomised" and refuses "per_protocol". Other tests take '
    "either, and their claims say which population the bound covers."
)


RANDOMISATION_PARAMETERS = (
    ("randomisation", "string", True),
    ("strata", "list", True),
    ("block_size", "integer", True),
    ("population", "string", True),
)


# Shared by every two-arm model module, so a file that loads several gets one copy.
ASSIGNMENT = _constructor(
    "assignment",
    (("n_control", "integer"), ("n_treatment", "integer"), *RANDOMISATION_PARAMETERS),
    "Assignment",
    _assignment,
    documentation="How participants are assigned to the two arms: the two arm sizes and, "
    "when declared, how the assignment was randomised. One assignment can be shared by "
    f"several outcomes measured on the same participants. {RANDOMISATION_DOCUMENTATION} "
    f"{POPULATION_DOCUMENTATION}",
    lean=in_lean("model", OUTCOME_LAWS, RANDOMISATION),
)


CLUSTER_ASSIGNMENT = _constructor(
    "cluster_assignment",
    (
        ("clusters_control", "integer"),
        ("clusters_treatment", "integer"),
        ("n_control", "integer"),
        ("n_treatment", "integer"),
        *RANDOMISATION_PARAMETERS,
    ),
    "Assignment",
    _cluster_assignment,
    documentation="Whole clusters, such as clinics or schools, are assigned to the arms, and "
    "everyone in a cluster gets the same arm. clusters_control and clusters_treatment count "
    "the clusters; n_control and n_treatment count the participants. Sites in a trial that "
    "randomises participants are not clusters: use assignment(...) there. Tests that assume "
    "independent participants are refused. With randomisation, the units are the clusters. "
    + f"{RANDOMISATION_DOCUMENTATION} {POPULATION_DOCUMENTATION}",
    lean=in_lean("model", OUTCOME_LAWS, RANDOMISATION),
)


STRATUM = _constructor(
    "stratum",
    (("control", "integer"), ("treatment", "integer")),
    "Stratum",
    _stratum,
    documentation="One stratum of a stratified or blocked assignment: how many randomised "
    "units, participants or clusters, it has in each arm.",
    lean=in_lean("model", RANDOMISATION),
)


NO_EFFECT = _constructor(
    "no_effect",
    (("model", StudyModelIR),),
    "SharpNull",
    _no_effect,
    documentation=SHARP_NULL.documentation,
    lean=in_lean("null", RANDOMISATION),
)


TWO_ARM = _constructor(
    "two_arm",
    (("assignment", AssignmentIR), ("outcome", OutcomeIR)),
    "Model",
    _two_arm,
    documentation="A two-arm model from an assignment and an outcome. A binary outcome "
    "gives the binomial model; any other outcome gives an OutcomeModel. The same pieces "
    "give the same model as the one-call constructors, such as two_arm_continuous.",
    lean=in_lean("model", BINOMIAL, OUTCOME_LAWS),
)


def outcome_constructor_name(kind: str) -> str:
    return f"{kind}_outcome"


MEASUREMENTS_DOCUMENTATION = (
    "measurements is how many times the outcome is measured on each participant, 1 if left "
    "out. With more than one, tests that take one value per participant are refused."
)


NAME_DOCUMENTATION = (
    'name labels the outcome, such as "response". One name is one outcome: models that '
    "share it must agree on its kind and better. A family, sequence or graph that asks the "
    "same question of a named outcome twice, the same test of the same null on the same "
    "participants, is refused."
)


def _law(outcome) -> str:
    """Binary outcomes have a Lean law; continuous and survival outcomes are abstract models
    whose claims hold for any law meeting the premises."""
    return BINOMIAL if outcome.key == "binary" else OUTCOME_LAWS


# Nulls whose meaning a test's own module states.
NULL_FILES = {"proportion_difference_at_most": "Modules/DifferenceTest"}


def _outcome_piece_constructor(outcome) -> Constructor:
    repeated = (("measurements", "integer", True),) if outcome.repeatable else ()
    return _constructor(
        outcome_constructor_name(outcome.key),
        (("better", "string", True), *repeated, ("name", "string", True)),
        "Outcome",
        _outcome_piece(outcome.key),
        lean=in_lean("model", _law(outcome)),
        documentation=f"The {outcome.key} outcome measured on each participant. Combine "
        f"it with an assignment in two_arm(...). {BETTER_DOCUMENTATION}"
        + (f" {MEASUREMENTS_DOCUMENTATION}" if outcome.repeatable else "")
        + f" {NAME_DOCUMENTATION}",
    )


def _shorthand_note(outcome) -> str:
    return (
        f"Shorthand for two_arm(assignment=assignment(n_control, n_treatment, population), "
        f"outcome={outcome_constructor_name(outcome.key)}(better, name)); population and name "
        "mean the same as there."
    )


# The one-call model constructors: arm sizes, and the assignment's and outcome's optional
# declarations that fit in one call. Randomisation and repeated measurements need the pieces.
SHORTHAND_PARAMETERS = (
    ("n_control", "integer"),
    ("n_treatment", "integer"),
    ("better", "string", True),
    ("population", "string", True),
    ("name", "string", True),
)


def _outcome_module(outcome) -> "Module":
    nulls = tuple(
        _constructor(
            form.key,
            (("model", OutcomeModelIR), *((("value", "number"),) if form.takes_value else ())),
            "OutcomeNull",
            _outcome_null(outcome, form),
            documentation=form.documentation,
            lean=in_lean("null", NULL_FILES.get(form.key, _law(outcome))),
        )
        for form in outcome.nulls
    )
    model = _constructor(
        outcome.constructor,
        SHORTHAND_PARAMETERS,
        "OutcomeModel",
        _model_from_sizes(outcome.key),
        lean=in_lean("model", _law(outcome)),
        documentation=f"{outcome.documentation} The model fixes no distribution; each test "
        f"states the one it assumes. {_shorthand_note(outcome)} {BETTER_DOCUMENTATION}",
    )
    pieces = (
        ASSIGNMENT,
        CLUSTER_ASSIGNMENT,
        STRATUM,
        _outcome_piece_constructor(outcome),
        TWO_ARM,
    )
    return Module(outcome.module, (model, *pieces, *nulls, NO_EFFECT, TYPE_I))


STUDY_NAMES = (("exposure", "string", True), ("outcome", "string", True))


STUDY_SCALES = (("exposure_scale", "string", True), ("outcome_scale", "string", True))


STUDY_NAMES_DOCUMENTATION = (
    'exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.'
)


# Extending this registry adds vocabulary and typed builders; parsing is unchanged.
MODULES = {
    module.name: module
    for module in (
        *(_outcome_module(outcome) for outcome in OUTCOMES.values() if not outcome.builtin),
        Module(
            "tests.declared",
            (
                _constructor(
                    "declared_test",
                    (
                        ("design", PlanIR),
                        ("null", NullIR),
                        ("alpha", "level"),
                        ("method", "string"),
                        ("scope", "string", True),
                        ("reference", "string", True),
                    ),
                    "CitedAnalysis",
                    _declared_test,
                    documentation="A test you name and vouch for, when StatClaim has no "
                    "contract for the analysis. method says what the test is. scope is "
                    "finite_sample or asymptotic, and asymptotic if left out. reference is "
                    "where the test is specified. Nothing about its guarantee is checked.",
                    lean=in_lean("premise", PREMISES),
                ),
            ),
        ),
        *(
            Module(group.name, tuple(_cited_constructor(method) for method in group.methods))
            for group in METHOD_MODULES
        ),
        Module(
            "models.two_arm_binomial",
            (
                _constructor(
                    "two_arm_binomial",
                    SHORTHAND_PARAMETERS,
                    "Model",
                    _model_from_sizes("binary"),
                    documentation="Two independent binomial arms. "
                    + _shorthand_note(OUTCOMES["binary"])
                    + " "
                    + BETTER_DOCUMENTATION,
                    lean=in_lean("model", BINOMIAL),
                ),
                ASSIGNMENT,
                CLUSTER_ASSIGNMENT,
                STRATUM,
                _outcome_piece_constructor(OUTCOMES["binary"]),
                TWO_ARM,
                _constructor(
                    "equal_proportions",
                    (("model", ModelIR),),
                    "Hypothesis",
                    lambda args, span: HypothesisIR(args["model"].value),
                    documentation="Null: p_treatment = p_control. This declares a restriction "
                    "under which a guarantee is requested, not that the null is true.",
                    lean=in_lean("null", BINOMIAL),
                ),
                _constructor(
                    "proportion_difference",
                    (("model", ModelIR), ("value", "number")),
                    "Hypothesis",
                    _difference("proportion_difference"),
                    documentation="Null: p_treatment - p_control = value. The difference is "
                    "absolute, not a relative percentage; value is exact and lies in [-1, 1]. "
                    "A zero difference is the equal-proportions null.",
                    lean=in_lean("null", BINOMIAL),
                ),
                _constructor(
                    "proportion_difference_at_most",
                    (("model", ModelIR), ("value", "number")),
                    "Hypothesis",
                    _difference("proportion_difference_at_most"),
                    documentation="Null: p_treatment - p_control <= value. This is an inequality "
                    "null, including when value=0; it is not the equality null supported by "
                    "the current two-sided Fisher analysis.",
                    lean=in_lean("null", "Modules/DifferenceTest"),
                ),
                _constructor(
                    "observe",
                    (
                        ("analysis", AnalysisIR),
                        ("control_successes", "integer"),
                        ("treatment_successes", "integer"),
                    ),
                    "Observation",
                    _observe,
                    lean=in_lean("data", BINOMIAL),
                ),
                NO_EFFECT,
                TYPE_I,
                _constructor(
                    "result",
                    (("observation", ObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                    lean=in_lean("claim", RESULTS, "Modules/Fisher", "Computation"),
                ),
            ),
        ),
        Module(
            "sampling",
            (
                _constructor(
                    "fixed",
                    (("model", StudyModelIR),),
                    "StudyDesign",
                    lambda args, span: PlanIR(args["model"].value, "fixed"),
                    lean=in_lean("design", CORE),
                ),
                _constructor(
                    "adaptive",
                    (("model", StudyModelIR),),
                    "StudyDesign",
                    lambda args, span: PlanIR(args["model"].value, "data_dependent"),
                    lean=in_lean("design", CORE),
                ),
            ),
        ),
        Module(
            "tests.fisher",
            (
                _constructor(
                    "fisher",
                    (("design", PlanIR), ("null", HypothesisIR), ("alpha", "level")),
                    "Analysis",
                    _fisher("two_sided"),
                    hypothesis_contract=FISHER_CONTRACT,
                    documentation=FISHER_CONTRACT.guidance,
                    lean=in_lean("analysis", "Modules/Fisher"),
                ),
                _constructor(
                    "fisher_one_sided",
                    (("design", PlanIR), ("null", HypothesisIR), ("alpha", "level")),
                    "Analysis",
                    _fisher("greater"),
                    hypothesis_contract=ONE_SIDED_FISHER_CONTRACT,
                    documentation=ONE_SIDED_FISHER_CONTRACT.guidance,
                    lean=in_lean("analysis", "Modules/FisherOneSided"),
                ),
            ),
        ),
        *(
            Module(
                f"tests.{name}",
                (
                    _constructor(
                        analysis.test,
                        (
                            ("design", PlanIR),
                            ("null", HypothesisIR),
                            ("squared_cutoff", "number"),
                            ("alpha", "level"),
                        ),
                        analysis.__name__.removesuffix("IR"),
                        _proportion_z(analysis),
                        hypothesis_contract=analysis.contract,
                        documentation=analysis.contract.guidance,
                        lean=in_lean("analysis", "Modules/Wald", "WaldBound"),
                    ),
                    TYPE_I,
                ),
            )
            for name, analysis in (("wald", WaldAnalysisIR), ("score", ScoreAnalysisIR))
        ),
        Module(
            "tests.likelihood_ratio",
            (
                _constructor(
                    "likelihood_ratio_test",
                    (
                        ("design", PlanIR),
                        ("null", HypothesisIR),
                        ("ratio_cutoff", "number"),
                        ("alpha", "level"),
                    ),
                    "LikelihoodRatioAnalysis",
                    _likelihood_ratio_test,
                    hypothesis_contract=LikelihoodRatioAnalysisIR.contract,
                    documentation=LikelihoodRatioAnalysisIR.contract.guidance,
                    lean=in_lean("analysis", "Modules/LikelihoodRatio"),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "tests.pearson",
            (
                _constructor(
                    "pearson_test",
                    (
                        ("design", PlanIR),
                        ("null", HypothesisIR),
                        ("squared_cutoff", "number"),
                        ("alpha", "level"),
                        ("correction", "string", True),
                    ),
                    "PearsonAnalysis",
                    _pearson_test,
                    hypothesis_contract=PearsonAnalysisIR.contract,
                    documentation=PearsonAnalysisIR.contract.guidance,
                    lean=in_lean("analysis", "Modules/Pearson"),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "tests.farrington_manning",
            (
                _constructor(
                    "farrington_manning",
                    (
                        ("design", PlanIR),
                        ("null", HypothesisIR),
                        ("squared_cutoff", "number"),
                        ("alpha", "level"),
                    ),
                    "FarringtonManningAnalysis",
                    _farrington_manning,
                    hypothesis_contract=FarringtonManningAnalysisIR.contract,
                    documentation=FarringtonManningAnalysisIR.contract.guidance,
                    lean=in_lean("analysis", "Modules/FarringtonManning"),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "tests.randomisation",
            (
                _constructor(
                    "randomisation_test",
                    (
                        ("design", PlanIR),
                        ("null", NullIR),
                        ("alpha", "level"),
                        ("draws", "integer", True),
                    ),
                    "RandomisationAnalysis",
                    _randomisation_test,
                    hypothesis_contract=RANDOMISATION_CONTRACT,
                    documentation="Randomisation test of the sharp null. Its level follows "
                    "from the randomisation declared on the assignment, and Lean proves it "
                    "for every test statistic fixed in advance; no distribution is assumed. "
                    "With cluster_assignment the clusters are randomised, so the test "
                    "permutes clusters. Without draws the p-value counts every possible "
                    "assignment; with draws=B it compares the observed assignment with B "
                    "drawn at random, which Lean also proves. " + RANDOMISATION_CONTRACT.guidance,
                    lean=in_lean("analysis", RANDOMISATION),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "models.observational",
            (
                _constructor(
                    "cross_sectional",
                    (
                        ("n", "integer"),
                        *STUDY_NAMES,
                        *STUDY_SCALES,
                        ("survey", "string", True),
                        ("clusters", "integer", True),
                    ),
                    "CrossSectionalStudy",
                    _cross_sectional,
                    documentation="A cross-sectional study: n participants sampled from one "
                    "population, with exposure and outcome measured at the same time. Only n "
                    "is fixed, not how many are exposed. It measures prevalence, not "
                    "incidence. " + STUDY_NAMES_DOCUMENTATION,
                    lean=in_lean("model", ASSOCIATION, OUTCOME_LAWS),
                ),
                _constructor(
                    "cohort",
                    (
                        ("exposed", "integer", True),
                        ("unexposed", "integer", True),
                        ("n", "integer", True),
                        *STUDY_NAMES,
                        *STUDY_SCALES,
                    ),
                    "CohortStudy",
                    _cohort,
                    documentation="A cohort study: participants followed from exposure to "
                    "outcome. Give exposed and unexposed when the groups were sampled in fixed "
                    "numbers, or n when one population was sampled and exposure measured. "
                    + STUDY_NAMES_DOCUMENTATION,
                    lean=in_lean("model", ASSOCIATION, OUTCOME_LAWS),
                ),
                _constructor(
                    "case_control",
                    (
                        ("cases", "integer"),
                        ("controls", "integer"),
                        *STUDY_NAMES,
                        ("exposure_scale", "string", True),
                    ),
                    "CaseControlStudy",
                    _case_control,
                    documentation="A case-control study: cases with the outcome and controls "
                    "without it, sampled in fixed numbers and asked about past exposure. It "
                    "estimates odds ratios only, never risk or prevalence, because the design "
                    "fixed how many have the outcome. " + STUDY_NAMES_DOCUMENTATION,
                    lean=in_lean("model", ASSOCIATION, OUTCOME_LAWS),
                ),
                _constructor(
                    "person_time_cohort",
                    (*STUDY_NAMES, ("exposure_scale", "string", True)),
                    "PersonTimeStudy",
                    _person_time_cohort,
                    documentation="A cohort followed over person-time, counting events in the "
                    "exposed and unexposed. It measures incidence rates; no group size is "
                    "fixed. " + STUDY_NAMES_DOCUMENTATION,
                    lean=in_lean("model", INCIDENCE, OUTCOME_LAWS),
                ),
                _constructor(
                    "observed_events",
                    (
                        ("model", PersonTimeStudyIR),
                        ("exposed_events", "integer"),
                        ("exposed_time", "number"),
                        ("unexposed_events", "integer"),
                        ("unexposed_time", "number"),
                    ),
                    "ObservedEvents",
                    _observed_events,
                    documentation="Events and person-time, such as person-years, in the exposed "
                    "and unexposed groups of a person-time cohort.",
                    lean=in_lean("data", INCIDENCE),
                ),
                _constructor(
                    "matched_case_control",
                    (("pairs", "integer"), *STUDY_NAMES, ("exposure_scale", "string", True)),
                    "MatchedStudy",
                    _matched_case_control,
                    documentation="A 1:1 matched case-control study: each case matched to one "
                    "control on chosen characteristics. Its tests and intervals use the "
                    "pairs where exactly one was exposed; unmatched analyses refuse it. "
                    + STUDY_NAMES_DOCUMENTATION,
                    lean=in_lean("model", MATCHED, OUTCOME_LAWS),
                ),
                _constructor(
                    "observed_pairs",
                    (("model", MatchedStudyIR), *((cell, "integer") for cell in PAIR_CELLS)),
                    "MatchedPairs",
                    _observed_pairs,
                    documentation="The observed pairs of a matched study: both exposed, only "
                    "the case, only the control, or neither. They must add up to the pairs.",
                    lean=in_lean("data", MATCHED),
                ),
                _constructor(
                    "observed_table",
                    (("model", ObservationalStudyIR), *((cell, "integer") for cell in CELLS)),
                    "AssociationTable",
                    _observed_table,
                    documentation="The observed 2x2 table: exposed and unexposed cases, who "
                    "have the outcome, and noncases. It must fit what the design fixed: a "
                    "cohort's group sizes, a case-control study's numbers of cases and "
                    "controls, or the total.",
                    lean=in_lean("data", ASSOCIATION),
                ),
                _constructor(
                    "no_association",
                    (("model", ObservationalStudyIR),),
                    "AssociationNull",
                    _no_association,
                    documentation="Null: no association between the study's exposure and "
                    "outcome, an odds ratio of 1. For a cohort, equal risk with and without "
                    "exposure; for a case-control study, exposure as common among cases as "
                    "among controls; for a cross-sectional study, equal prevalence.",
                    lean=in_lean("null", ASSOCIATION, OUTCOME_LAWS),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "tests.association",
            (
                _constructor(
                    "fisher_exact",
                    (("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")),
                    "AssociationAnalysis",
                    _fisher_exact,
                    documentation="Fisher's exact test of no association in an observational "
                    "2x2 study. Lean proves its level for every design: with group sizes "
                    "fixed by a cohort or case-control study, and with only the total fixed, "
                    "by averaging over the number exposed. The bound concerns association, "
                    "not an effect of the exposure.",
                    lean=in_lean("analysis", ASSOCIATION),
                ),
                _constructor(
                    "rate_test",
                    (("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")),
                    "RateAnalysis",
                    _rate_test,
                    documentation="The exact test of equal incidence rates: given the total "
                    "events, a two-sided binomial test of the exposed share at the exposed "
                    "share of person-time. Lean proves its level for every rate and any "
                    "person-time, given the total and on average over it.",
                    lean=in_lean("analysis", INCIDENCE),
                ),
                _constructor(
                    "rate_result",
                    (("analysis", RateAnalysisIR), ("events", ObservedEventsIR)),
                    "ResultClaim",
                    _rate_result,
                    documentation="Claim about the exact p-value and decision of the rate test "
                    "for the observed events, with the test's Type I bound.",
                    lean=in_lean("claim", RESULTS, INCIDENCE),
                ),
                _constructor(
                    "mcnemar",
                    (("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")),
                    "MatchedAnalysis",
                    _mcnemar,
                    documentation="McNemar's exact test of no association within matched "
                    "pairs: given the discordant pairs, a two-sided binomial test at one half. "
                    "Lean proves its level given the number of discordant pairs and on "
                    "average over it.",
                    lean=in_lean("analysis", MATCHED),
                ),
                _constructor(
                    "mcnemar_asymptotic",
                    (
                        ("design", PlanIR),
                        ("null", AssociationNullIR),
                        ("squared_cutoff", "number"),
                        ("alpha", "level"),
                    ),
                    "AsymptoticMcNemarAnalysis",
                    _mcnemar_asymptotic,
                    documentation="McNemar's two-sided chi-square test without continuity "
                    "correction. Its finite-sample Type I error is checked over all "
                    "discordance probabilities in the fixed matched-pairs design.",
                    lean=in_lean("analysis", "Modules/McNemarAsymptotic"),
                ),
                _constructor(
                    "matched_result",
                    (("analysis", MatchedAnalysisIR), ("pairs", MatchedPairsIR)),
                    "ResultClaim",
                    _matched_result,
                    documentation="Claim about the exact p-value and decision of McNemar's "
                    "test for the observed pairs, with the test's Type I bound.",
                    lean=in_lean("claim", RESULTS, MATCHED),
                ),
                _constructor(
                    "association_result",
                    (("analysis", AssociationAnalysisIR), ("table", AssociationTableIR)),
                    "ResultClaim",
                    _association_result,
                    documentation="Claim about the exact p-value and decision of Fisher's "
                    "test for the observed table, with the test's Type I bound. For a design "
                    "that fixed only the total, the p-value is given the number exposed.",
                    lean=in_lean("claim", RESULTS, ASSOCIATION),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "estimation.observational",
            (
                _constructor(
                    "rate_ratio",
                    (("events", ObservedEventsIR), ("level", "level")),
                    "IntervalClaim",
                    _rate_ratio,
                    documentation="Interval for the incidence rate ratio of a person-time "
                    "cohort, from the exact interval for the exposed share of events.",
                    lean=in_lean("claim", INTERVALS, INCIDENCE),
                ),
                *(
                    _constructor(
                        measure,
                        (
                            ("model", ObservationalStudyIR),
                            ("cases", "integer"),
                            ("level", "level"),
                            ("group", "string", True),
                        ),
                        "IntervalClaim",
                        _proportion(measure),
                        lean=in_lean("claim", INTERVALS, INTERVAL),
                        documentation=f"The {words} with its exact interval. Only a "
                        f"{designs[0].replace('_', '-')} study estimates it. For a cohort that "
                        'sampled groups separately, group="exposed" or "unexposed" says which.',
                    )
                    for measure, (words, designs) in PROPORTIONS.items()
                ),
                _constructor(
                    "conditional_odds_ratio",
                    (("pairs", MatchedPairsIR), ("level", "level")),
                    "IntervalClaim",
                    _conditional_odds_ratio,
                    documentation="Interval for the conditional odds ratio of a matched "
                    "study, the odds that the case is the exposed one in a discordant pair, "
                    "from the exact interval for that probability.",
                    lean=in_lean("claim", INTERVALS, MATCHED),
                ),
            )
            + tuple(
                _constructor(
                    measure,
                    (("table", AssociationTableIR), ("level", "level")),
                    "IntervalClaim",
                    _effect_interval(measure),
                    lean=in_lean("claim", INTERVALS, INTERVAL, ASSOCIATION),
                    documentation=f"Interval for the {words} at the given confidence level, "
                    "from exact intervals for each group's probability; valid for every pair "
                    "of probabilities, and conservative. "
                    + {
                        "odds": "Any design: for a case-control study it is the odds ratio "
                        "of exposure, which equals that of the outcome.",
                        "ratio": f"Only a {designs[0].replace('_', '-')} study estimates it.",
                        "difference": f"Only a {designs[0].replace('_', '-')} study estimates it.",
                    }[kind],
                )
                for measure, (words, kind, designs) in MEASURES.items()
            ),
        ),
        *(
            Module(
                name,
                (*(_cited_association_constructor(m) for m in group), TYPE_I),
            )
            for name, group in (
                ("tests.regression", REGRESSION),
                ("tests.correlation", CORRELATION),
                ("tests.survey", SURVEY),
            )
        ),
        Module(
            "tests.difference",
            (
                _constructor(
                    "difference_test",
                    (("design", PlanIR), ("null", HypothesisIR), ("alpha", "level")),
                    "Analysis",
                    _difference_test,
                    hypothesis_contract=MARGIN_CONTRACT,
                    documentation=MARGIN_CONTRACT.guidance,
                    lean=in_lean("analysis", "Modules/DifferenceTest"),
                ),
            ),
        ),
        Module(
            "multiplicity.bonferroni",
            (
                _constructor(
                    "bonferroni",
                    (("analyses", "list"), ("alpha", "level"), ("joint_law", "string", True)),
                    "Family",
                    _family,
                    documentation="Bonferroni: the members' levels may sum to at most alpha. "
                    "Members may be exact tests, cited tests, designs with interim looks, "
                    "sequences, graphs or other families; dependence between them is "
                    "unrestricted. "
                    "A family of two-sided Fisher analyses is proved "
                    "outright. Any other family is conditional: Lean checks the combination "
                    "and each member's own bound is assumed.",
                    lean=in_lean(
                        "composition",
                        COMPOSITION,
                        "Modules/Bonferroni",
                        "Modules/FisherFamily",
                        "Modules/FisherFamilyN",
                    ),
                ),
                FAMILYWISE,
            ),
        ),
        Module(
            "multiplicity.graphical",
            (
                _constructor(
                    "graphical",
                    (
                        ("analyses", "list"),
                        ("weights", "list"),
                        ("transitions", "list"),
                        ("alpha", "level"),
                    ),
                    "ComposedFamily",
                    _graphical,
                    documentation="A graphical procedure with recycling. weights gives each "
                    "test's starting share of alpha. Row i of transitions says how test i's "
                    "level is shared among the others when it is rejected. Declare every test "
                    "at the overall alpha. The procedure's guarantee is cited, not checked by "
                    "Lean; the contract checks that the weights and transitions are valid.",
                    lean=in_lean("composition", PROGRAM, METHODS),
                ),
                FAMILYWISE,
            ),
        ),
        Module(
            "multiplicity.fixed_sequence",
            (
                _constructor(
                    "fixed_sequence",
                    (("analyses", "list"), ("alpha", "level")),
                    "ComposedFamily",
                    _fixed_sequence,
                    documentation="Hierarchical testing: the analyses are tested in the listed "
                    "order, each at the full level alpha, and a test is carried out only if "
                    "every earlier one rejected. An entry may be a test, a design with interim "
                    "looks, or a family, sequence or graph; such an entry must be rejected in "
                    "full before the next is tested. Lean checks the combination; each "
                    "entry's own bound is assumed.",
                    lean=in_lean("composition", COMPOSITION),
                ),
                FAMILYWISE,
            ),
        ),
        Module(
            "planning",
            (
                _constructor(
                    "binomial_rates",
                    (
                        ("p_control", "number"),
                        ("p_treatment", "number"),
                        ("icc", "number", True),
                        ("cluster_size_cv", "number", True),
                    ),
                    "Rates",
                    _rates,
                    documentation="A planning point: one success probability per arm. "
                    "It is an input for power, not the null and not an established fact. "
                    "A test of cluster proportions also needs icc, the intracluster "
                    "correlation, and simulate(...) takes cluster_size_cv, how much cluster "
                    "sizes vary.",
                    lean=in_lean("planning", "Modules/FisherPower"),
                ),
                _constructor(
                    "mean_difference",
                    (
                        ("value", "number"),
                        ("sd", "number"),
                        ("icc", "number", True),
                        ("cluster_size_cv", "number", True),
                        ("sd_treatment", "number", True),
                        ("skewness", "number", True),
                    ),
                    "MeanDifference",
                    _mean_difference,
                    documentation="A planning point for a continuous outcome: the true mean "
                    "difference, treatment minus control, and the standard deviation of one "
                    "participant's outcome on the analysed scale. For a mixed model, sd is the "
                    "effective standard deviation of the contrast. A test of cluster means "
                    "also needs icc, the intracluster correlation: the share of the variance "
                    "that lies between clusters; simulate(...) also takes cluster_size_cv, the "
                    "coefficient of variation of cluster sizes. To simulate a two-sample "
                    "t-test in another scenario, give sd_treatment, the treatment arm's SD "
                    "(sd is then the control arm's), or skewness, for a gamma-shaped outcome. "
                    "All are planning inputs.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "hazard_ratio",
                    (("value", "number"), ("events", "integer")),
                    "HazardRatio",
                    _hazard_ratio,
                    documentation="A planning point for a survival outcome: the true hazard "
                    "ratio, treatment over control, and the expected total number of events. "
                    "Power depends on the events, not on the arm sizes. Both are planning inputs.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "correlation",
                    (
                        ("value", "number"),
                        ("skewness", "number", True),
                        ("exposure_skewness", "number", True),
                    ),
                    "Correlation",
                    _correlation,
                    documentation="A planning point for two continuous variables: their "
                    "correlation, strictly between -1 and 1. For pearson_correlation. To "
                    "simulate skewed data, give skewness (of the outcome's error) or "
                    "exposure_skewness. Planning inputs, not established facts.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "outcome_means",
                    (
                        ("unexposed", "number"),
                        ("exposed", "number"),
                        ("sd", "number"),
                        ("exposed_share", "number", True),
                        ("design_effect", "number", True),
                    ),
                    "OutcomeMeans",
                    _outcome_means,
                    documentation="A planning point for a measured outcome by a yes-or-no "
                    "exposure, for linear_association or survey_linear: the outcome's mean "
                    "without and with the exposure, and its standard deviation about them. A "
                    "study that fixes only its total also needs exposed_share; a survey of a "
                    "complex sample, design_effect. Planning inputs, not established facts.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "odds_per_sd",
                    (
                        ("odds_ratio", "number"),
                        ("baseline", "number"),
                        ("exposure_r2", "number", True),
                        ("design_effect", "number", True),
                    ),
                    "OddsPerSd",
                    _odds_per_sd,
                    documentation="A planning point for logistic_association with a measured "
                    "exposure: the odds ratio per standard deviation of the exposure, the "
                    "outcome's probability at the exposure's mean, and optionally exposure_r2, "
                    "the share of the exposure's variance the covariates explain. A survey test "
                    "of a complex sample also takes design_effect. Planning inputs, not "
                    "established facts.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "slope",
                    (
                        ("value", "number"),
                        ("exposure_sd", "number"),
                        ("residual_sd", "number"),
                        ("exposure_r2", "number", True),
                        ("design_effect", "number", True),
                        ("skewness", "number", True),
                        ("exposure_skewness", "number", True),
                    ),
                    "Slope",
                    _slope,
                    documentation="A planning point for linear_association with a continuous "
                    "exposure: the change in the outcome's mean per unit of exposure, the "
                    "exposure's standard deviation, the outcome's standard deviation about the "
                    "regression, and optionally exposure_r2, the share of the exposure's "
                    "variance the covariates explain. A survey test of a complex sample also "
                    "takes design_effect. To simulate skewed data, give skewness (of the "
                    "residual) or exposure_skewness. All are planning inputs.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "exponential_survival",
                    (
                        ("hazard_ratio", "number"),
                        ("control_median", "number"),
                        ("accrual", "number"),
                        ("follow_up", "number"),
                        ("dropout", "number", True),
                        ("dropout_time", "number", True),
                        ("effect_delay", "number", True),
                    ),
                    "ExponentialSurvival",
                    _exponential_survival,
                    documentation="A planning point for a survival outcome given by its "
                    "times: the hazard ratio, treatment over control; the control arm's median "
                    "time to the event; participants entering steadily over accrual and "
                    "followed for follow_up after it; and optionally the probability of "
                    "dropping out by dropout_time. Times are exponential and in one unit, such "
                    "as months. The arm sizes then give the expected events, so arm sizes can "
                    "be searched. simulate(...) also takes effect_delay: the hazard ratio "
                    "applies only from that time after entry. All are planning inputs.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "risks",
                    (
                        ("unexposed", "number"),
                        ("exposed", "number", True),
                        ("risk_ratio", "number", True),
                        ("exposed_share", "number", True),
                    ),
                    "Risks",
                    _risks,
                    documentation="A planning point for a cohort: the risk of the outcome "
                    "without exposure, and with it, given as exposed or as risk_ratio, exposed "
                    "over unexposed. A cohort of one population, declared with n, also needs "
                    "exposed_share, the probability that a participant is exposed. A planning "
                    "input, not an established fact.",
                    lean=in_lean("planning", "Modules/AssociationPower"),
                ),
                _constructor(
                    "outcome_prevalence",
                    (
                        ("unexposed", "number"),
                        ("exposed", "number", True),
                        ("prevalence_ratio", "number", True),
                        ("exposed_share", "number"),
                        ("design_effect", "number", True),
                    ),
                    "OutcomePrevalence",
                    _outcome_prevalence,
                    documentation="A planning point for a cross-sectional study: the prevalence "
                    "of the outcome without exposure, and with it, given as exposed or as "
                    "prevalence_ratio, and exposed_share, the probability that a participant is "
                    "exposed. A survey test of a complex sample also takes design_effect. A "
                    "planning input, not an established fact.",
                    lean=in_lean("planning", "Modules/AssociationPower"),
                ),
                _constructor(
                    "exposure_prevalence",
                    (
                        ("controls", "number"),
                        ("cases", "number", True),
                        ("odds_ratio", "number", True),
                    ),
                    "ExposurePrevalence",
                    _exposure_prevalence,
                    documentation="A planning point for a case-control study: the share of "
                    "controls who were exposed, and of cases, given as cases or as odds_ratio, "
                    "the odds of exposure among cases over the odds among controls. A planning "
                    "input, not an established fact.",
                    lean=in_lean("planning", "Modules/AssociationPower"),
                ),
                _constructor(
                    "discordant_pairs",
                    (("share", "number"), ("odds_ratio", "number")),
                    "DiscordantPairs",
                    _discordant_pairs,
                    documentation="A planning point for a 1:1 matched study: the probability "
                    "that a pair is discordant, with exactly one of the two exposed, and the "
                    "conditional odds ratio. A planning input, not an established fact.",
                    lean=in_lean("planning", "Modules/BinomialPower"),
                ),
                _constructor(
                    "incidence_rates",
                    (
                        ("rate_ratio", "number"),
                        ("exposed_time", "number"),
                        ("unexposed_time", "number"),
                        ("events", "integer", True),
                    ),
                    "IncidenceRates",
                    _incidence_rates,
                    documentation="A planning point for a person-time cohort: the rate ratio, "
                    "exposed over unexposed, the expected person-time in each group, of which "
                    "only the exposed share matters, and the total number of events power is "
                    "calculated for. Leave events out to search them with event_counts.",
                    lean=in_lean("planning", "Modules/BinomialPower"),
                ),
                _constructor(
                    "proportion",
                    (
                        ("value", "number"),
                        ("design_effect", "number", True),
                        ("population_size", "integer", True),
                    ),
                    "SingleProportion",
                    _single_proportion,
                    documentation="A planning point for one proportion, such as a prevalence or "
                    "a cumulative incidence: its value, strictly between 0 and 1. For the normal "
                    "interval of a survey, design_effect and population_size, the number in the "
                    "population sampled, for a finite population correction. A planning input, "
                    "not an established fact.",
                    lean=PRECISION,
                ),
                _constructor(
                    "precision_target",
                    (
                        ("at", PlanningPointIR),
                        ("level", "level"),
                        ("margin_of_error", "number", True),
                        ("relative_margin_of_error", "number", True),
                        ("assurance", "number", True),
                    ),
                    "PrecisionTarget",
                    _precision_target,
                    documentation="Require an interval at the given level to be narrow enough at "
                    "the planning point: its margin of error, half its width, at most "
                    "margin_of_error, or its relative margin of error at most "
                    "relative_margin_of_error, a fraction of the planning value. For a ratio the "
                    "relative margin r asks that the lower limit be at least (1 - r) times the "
                    "estimate, on the log scale. Without assurance, the interval is taken at the "
                    "counts the point expects; with it, the chance that the interval is narrow "
                    "enough must be at least assurance.",
                    lean=PRECISION,
                ),
                _constructor(
                    "planned_interval",
                    (
                        ("model", EstimableModelIR),
                        ("measure", "string"),
                        ("method", "string", True),
                        ("group", "string", True),
                    ),
                    "PlannedInterval",
                    _planned_interval,
                    documentation="The interval a study plans to report, for a precision target: "
                    "response_rate for one arm, difference for a two-arm trial, prevalence, "
                    "cumulative_incidence, risk or prevalence ratios and differences and "
                    "odds_ratio for observational studies, conditional_odds_ratio for matched "
                    'pairs and rate_ratio for person-time. method="exact" (the default) is '
                    'StatClaim\'s own exact interval; method="normal" is the usual large-sample '
                    "interval, and allows a survey's design effect and a finite population. For "
                    "a cohort that sampled two groups, group says whose cumulative incidence.",
                    lean=PRECISION,
                ),
                _constructor(
                    "interval_sizes",
                    (
                        ("interval", PlannedIntervalIR),
                        ("min_size", "integer"),
                        ("max_size", "integer"),
                        ("ratio", "integer", True),
                    ),
                    "IntervalCandidates",
                    _interval_sizes,
                    documentation="Sizes for a planned interval, in the design's own units: the "
                    "participants of one group or population; for two fixed groups, the first "
                    "(exposed, cases, or the control arm of a trial) with ratio of the other for "
                    "each; or the pairs or events.",
                    lean=PRECISION,
                ),
                _constructor(
                    "power_target",
                    (
                        ("at", PlanningPointIR),
                        ("minimum", "number"),
                        ("maximum_typeI", "level"),
                        ("nulls", NullScenariosIR, True),
                        ("rejecting", "string", True),
                    ),
                    "PowerTarget",
                    _power_target,
                    documentation="Require power of at least minimum at one planning point, "
                    "and a Type I error bound of at most maximum_typeI under the null. "
                    "Power at this point is not a guarantee for other alternatives. For a "
                    "design whose level is not proved, nulls lists where simulate(...) judges "
                    "its Type I error. For a family, rejecting says whether power means "
                    'rejecting "any" endpoint or "all" of them.',
                    lean=in_lean("planning", POLICY),
                ),
                _constructor(
                    "endpoint_points",
                    (("at", "list"), ("correlation", "number")),
                    "EndpointPoints",
                    _endpoint_points,
                    documentation="A planning point for a family: one point per member, in "
                    "order (binomial_rates for Fisher's test, mean_difference for a t-test), "
                    "and the correlation between endpoints measured on the same participants, "
                    "from 0 for independent endpoints to below 1. Planning inputs.",
                    lean=NotInLean("The power of a family is simulated, not proved."),
                ),
                _constructor(
                    "null_scenarios",
                    (("at", "list"),),
                    "NullScenarios",
                    _null_scenarios,
                    documentation="Points at the null, such as mean_difference(value=0, "
                    "sd=10), at which simulate(...) judges the Type I error of a design whose "
                    "level is not proved. Planning inputs; the error at other points is not "
                    "claimed.",
                    lean=NotInLean(
                        "Points at which a simulation judges Type I error; a simulation is "
                        "never proof."
                    ),
                ),
                _constructor(
                    "meets",
                    (("analysis", PlannableIR), ("target", TargetIR)),
                    "PlanningClaim",
                    _meets,
                    documentation="Claim that this analysis meets every component of the "
                    "target. calculate computes the components; verify must establish all. "
                    "For a cited test, calculate gives approximate power and verify is refused.",
                    lean=in_lean(
                        "claim",
                        PLANS,
                        POLICY,
                        "Modules/FisherPower",
                        "Modules/BinomialPower",
                        "Modules/AssociationPower",
                        TWO_STAGE,
                    ),
                ),
                _constructor(
                    "equal_arm_sizes",
                    (
                        ("analysis", TwoArmTestIR),
                        ("min_per_arm", "integer"),
                        ("max_per_arm", "integer"),
                    ),
                    "Candidates",
                    _candidates,
                    documentation="A finite design space: equal arm sizes within inclusive "
                    "bounds, keeping the analysis's sampling, null form, test and alpha.",
                    lean=in_lean("planning", "Modules/FisherPower"),
                ),
                _constructor(
                    "allocated_arm_sizes",
                    (
                        ("analysis", TwoArmTestIR),
                        ("min_control", "integer"),
                        ("max_control", "integer"),
                        ("treatment_per_control", "integer"),
                    ),
                    "Candidates",
                    _allocated,
                    documentation="A finite design space with unequal allocation: each "
                    "candidate has n controls and treatment_per_control * n treated "
                    "participants, for n within the inclusive bounds.",
                    lean=in_lean("planning", "Modules/FisherPower"),
                ),
                _constructor(
                    "cluster_counts",
                    (
                        ("analysis", TwoArmTestIR),
                        ("cluster_size", "integer"),
                        ("min_per_arm", "integer"),
                        ("max_per_arm", "integer"),
                    ),
                    "ClusterCandidates",
                    _cluster_counts,
                    documentation="Cluster-randomised trials for a test of cluster summaries: "
                    "min_per_arm to max_per_arm clusters in each arm, each of cluster_size "
                    "participants. Each keeps the analysis's null, test and alpha.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "cluster_sizes",
                    (
                        ("analysis", TwoArmTestIR),
                        ("min_size", "integer"),
                        ("max_size", "integer"),
                    ),
                    "ClusterCandidates",
                    _cluster_sizes,
                    documentation="Cluster-randomised trials for a test of cluster summaries: "
                    "the declared clusters per arm, with min_size to max_size participants in "
                    "each cluster. Each keeps the analysis's null, test and alpha. With few "
                    "clusters, no number of participants may be enough.",
                    lean=APPROXIMATE,
                ),
                _constructor(
                    "cohort_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_exposed", "integer"),
                        ("max_exposed", "integer"),
                        ("unexposed_per_exposed", "integer", True),
                    ),
                    "GroupCandidates",
                    _group_sizes("cohort"),
                    documentation="Designs of a cohort that samples its exposed and unexposed "
                    "groups: n exposed and unexposed_per_exposed * n unexposed (1 unless "
                    "given), for n within the inclusive bounds. Each keeps the analysis's "
                    "study, null and alpha.",
                    lean=in_lean("planning", "Modules/AssociationPower"),
                ),
                _constructor(
                    "case_control_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_cases", "integer"),
                        ("max_cases", "integer"),
                        ("controls_per_case", "integer", True),
                    ),
                    "GroupCandidates",
                    _group_sizes("case_control"),
                    documentation="Designs of a case-control study: n cases and "
                    "controls_per_case * n controls (1 unless given), for n within the "
                    "inclusive bounds. Each keeps the analysis's study, null and alpha.",
                    lean=in_lean("planning", "Modules/AssociationPower"),
                ),
                _constructor(
                    "total_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_n", "integer"),
                        ("max_n", "integer"),
                    ),
                    "TotalCandidates",
                    _total_sizes,
                    documentation="Cross-sectional studies, or cohorts of one population, with "
                    "min_n to max_n participants, keeping the analysis's study, null and alpha. "
                    "For Fisher's test, sample_size certifies a sufficient total and "
                    "smallest_sample_size is not offered; for a cited test with a power "
                    "formula, both are calculated.",
                    lean=in_lean("planning", "Modules/AssociationPower"),
                ),
                _constructor(
                    "matched_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_pairs", "integer"),
                        ("max_pairs", "integer"),
                    ),
                    "CountCandidates",
                    _count_sizes("pairs", MAX_PLANNED_PAIRS),
                    documentation="Matched studies with min_pairs to max_pairs pairs, keeping "
                    "the analysis's null and alpha: McNemar's test, or a conditional logistic "
                    "regression.",
                    lean=in_lean("planning", "Modules/BinomialPower"),
                ),
                _constructor(
                    "event_counts",
                    (
                        ("analysis", PlannableIR),
                        ("min_events", "integer"),
                        ("max_events", "integer"),
                    ),
                    "CountCandidates",
                    _count_sizes("events", MAX_EVENTS),
                    documentation="Totals of min_events to max_events events for the rate "
                    "test or a Poisson rate regression, keeping its null and alpha. The planning "
                    "point gives no events.",
                    lean=in_lean("planning", "Modules/BinomialPower"),
                ),
                _constructor(
                    "sample_sizes",
                    (("analysis", OneSampleAnalysisIR), ("min_n", "integer"), ("max_n", "integer")),
                    "OneArmCandidates",
                    _one_arm_candidates,
                    documentation="A finite design space: sample sizes within inclusive "
                    "bounds for a one-sample test, keeping its null rate and alpha.",
                    lean=in_lean("planning", "Modules/BinomialPower", ONE_SAMPLE),
                ),
                _constructor(
                    "response_rate",
                    (("value", "number"),),
                    "Rate",
                    lambda args, span: RateIR(_probability(args["value"], "value")),
                    documentation="A planning point for a single-arm design.",
                    lean=in_lean("planning", "Modules/BinomialPower", TWO_STAGE),
                ),
                _constructor(
                    "sample_size",
                    (("candidates", CandidateSpaceIR), ("target", TargetIR)),
                    "PlanningClaim",
                    _sizing(False),
                    documentation="Claim that some candidate meets the target. The search is "
                    "ascending; a sufficient size is not claimed to be the smallest possible.",
                    lean=in_lean(
                        "claim",
                        PLANS,
                        "Modules/FisherPower",
                        "Modules/BinomialPower",
                        "Modules/AssociationPower",
                    ),
                ),
                _constructor(
                    "smallest_sample_size",
                    (("candidates", CandidateSpaceIR), ("target", TargetIR)),
                    "PlanningClaim",
                    _sizing(True),
                    documentation="Claim that a candidate meets the target and that no smaller "
                    "candidate in the declared range does. Nothing is claimed outside the range.",
                    lean=in_lean(
                        "claim",
                        PLANS,
                        "Modules/FisherPower",
                        "Modules/BinomialPower",
                        "Modules/AssociationPower",
                    ),
                ),
            ),
        ),
        Module(
            "designs.group_sequential",
            (
                _constructor(
                    "alpha_spending",
                    (("looks", "list"), ("alpha", "level")),
                    "Sequential",
                    _sequential,
                    documentation="One test repeated at several looks, stopping at the first "
                    "rejection. Give each look as an analysis whose model has the cumulative "
                    "arm sizes at that look, with the level spent there. The levels may sum "
                    "to at most alpha. Lean checks the combination; each look's own bound is "
                    "assumed. The split is conservative.",
                    lean=in_lean("composition", COMPOSITION),
                ),
                _constructor(
                    "group_sequential",
                    (("looks", "list"), ("alpha", "level"), ("spending", "string")),
                    "Sequential",
                    _group_sequential,
                    documentation="One test repeated at several looks, stopping at the first "
                    "rejection, with boundaries that use the correlation between looks. "
                    'spending is "obrien_fleming" or "pocock" (Lan and DeMets). Give each look '
                    "as an analysis whose model has the cumulative arm sizes at that look, "
                    "with its nominal level: at most the level the spending function gives it "
                    "at its share of the information. The error message lists those levels. "
                    "For Fisher's test and the t-tests. The rule is cited.",
                    lean=in_lean("composition", PROGRAM, METHODS),
                ),
                _constructor(
                    "look_sizes",
                    (
                        ("design", SequentialIR),
                        ("min_per_arm", "integer"),
                        ("max_per_arm", "integer"),
                        ("step", "integer"),
                        ("criterion", "string"),
                    ),
                    "LookCandidates",
                    _look_sizes,
                    documentation="Designs with the declared looks whose sizes per control "
                    "arm are free: every increasing choice from min_per_arm to max_per_arm in "
                    "steps of step, keeping the final look's allocation, test and null. Each "
                    "candidate keeps the declared levels, or takes its own spending boundaries. "
                    'criterion="minimax" ranks the smallest final size first; "optimal" the '
                    "smallest expected size at the planning point. Exact for Fisher's test, "
                    "simulated for t-tests; the ranking is a calculation.",
                    lean=NotInLean(
                        "The power of a design with looks is calculated or simulated, and the "
                        "ranking of look sizes is a calculation; Lean does not check them."
                    ),
                ),
                TYPE_I,
            ),
        ),
        Module(
            "designs.adaptive",
            (
                _constructor(
                    "blinded_reestimation",
                    (
                        ("analysis", CitedAnalysisIR),
                        ("interim_per_arm", "integer"),
                        ("difference", "number"),
                        ("power", "number"),
                        ("max_per_arm", "integer"),
                    ),
                    "Reestimation",
                    _reestimation,
                    documentation="Student's t-test whose size per arm is re-estimated after "
                    "interim_per_arm per arm, from the variance of all outcomes with the arms "
                    "pooled, so no one sees the groups. The new size gives power at the planned "
                    "difference; it is never below the analysis's size per arm nor above "
                    "max_per_arm. Its Type I error is not proved: simulate(...) judges it at "
                    "the target's null scenarios.",
                    lean=NotInLean(
                        "Its Type I error is estimated by simulation at declared null "
                        "scenarios, not proved."
                    ),
                ),
            ),
        ),
        Module(
            "designs.two_stage",
            (
                _constructor(
                    "two_stage_binomial",
                    (("n_stage1", "integer"), ("n_stage2", "integer")),
                    "TwoStageModel",
                    _two_stage_model,
                    documentation="One arm, two stages, one response rate. Stage two is "
                    "observed only if the interim rule continues.",
                    lean=in_lean("design", TWO_STAGE, POLICY),
                ),
                _constructor(
                    "threshold_rule",
                    (("continue_above", "integer"), ("reject_above", "integer")),
                    "Rule",
                    _threshold_rule,
                    documentation="Continue when stage-one responses exceed continue_above; "
                    "reject the null when total responses exceed reject_above.",
                    lean=in_lean("design", TWO_STAGE),
                ),
                _constructor(
                    "beta_prior",
                    (("a", "integer"), ("b", "integer")),
                    "Prior",
                    _prior,
                    documentation="Beta(a, b) prior on the response rate, positive integers.",
                    lean=in_lean("design", TWO_STAGE),
                ),
                _constructor(
                    "posterior_rule",
                    (
                        ("prior", PriorIR),
                        ("reference", "number"),
                        ("continue_at_least", "level"),
                        ("success_at_least", "level"),
                    ),
                    "Rule",
                    _posterior_rule,
                    documentation="Continue, and finally declare success, when the posterior "
                    "probability that the response rate exceeds reference reaches the given "
                    "level. A posterior threshold does not by itself bound Type I error.",
                    lean=in_lean("design", TWO_STAGE),
                ),
                _constructor(
                    "stopped_at_interim",
                    (("analysis", TwoStageAnalysisIR), ("stage1_responses", "integer")),
                    "TwoStageObservation",
                    _stage_data(False),
                    documentation="Observed data when the interim rule stopped the study. "
                    "Rejected if the declared rule would have continued.",
                    lean=in_lean("data", TWO_STAGE),
                ),
                _constructor(
                    "completed_stages",
                    (
                        ("analysis", TwoStageAnalysisIR),
                        ("stage1_responses", "integer"),
                        ("stage2_responses", "integer"),
                    ),
                    "TwoStageObservation",
                    _stage_data(True),
                    documentation="Observed data from both stages. Rejected if the declared "
                    "rule would have stopped after stage one.",
                    lean=in_lean("data", TWO_STAGE),
                ),
                _constructor(
                    "two_stage_result",
                    (("observation", TwoStageObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                    documentation="Claim about the decision the declared design reaches for "
                    "the observed counts, with the design's error bound.",
                    lean=in_lean("claim", RESULTS, TWO_STAGE),
                ),
                _constructor(
                    "two_stage_designs",
                    (("null_rate", "number"), ("max_total", "integer"), ("criterion", "string")),
                    "TwoStageCandidates",
                    _two_stage_candidates,
                    documentation="Count-threshold two-stage designs with total size up to "
                    'max_total. criterion="optimal" minimises the expected sample size at the '
                    'null rate; "minimax" minimises the maximum sample size. The selected '
                    "design is certified; the ranking is a calculation.",
                    lean=in_lean("planning", TWO_STAGE),
                ),
                _constructor(
                    "two_stage_test",
                    (("design", TwoStageModelIR), ("rule", RuleIR), ("null_rate", "number")),
                    "TwoStageAnalysis",
                    _two_stage_test,
                    documentation="The complete policy: stages, interim stop, final decision "
                    "and the null response rate it tests.",
                    lean=in_lean("analysis", TWO_STAGE),
                ),
            ),
        ),
        Module(
            "estimation",
            (
                _constructor(
                    "difference_interval",
                    (
                        ("model", ModelIR),
                        ("control_successes", "integer"),
                        ("treatment_successes", "integer"),
                        ("level", "number"),
                    ),
                    "IntervalClaim",
                    _difference_interval,
                    documentation="Confidence interval for p_treatment - p_control, built "
                    "from an exact interval for each arm. It is valid for every pair of true "
                    "rates and is wider than intervals built for the difference directly, so "
                    "it can include zero when a test rejects.",
                    lean=in_lean("claim", INTERVALS, INTERVAL),
                ),
            ),
        ),
        Module(
            "tests.binomial",
            (
                _constructor(
                    "one_arm_binomial",
                    (("n", "integer"),),
                    "OneArmModel",
                    _one_arm,
                    documentation="One arm with n independent binary responses.",
                    lean=in_lean("model", ONE_SAMPLE),
                ),
                _constructor(
                    "binomial_test",
                    (("model", OneArmModelIR), ("null_rate", "number"), ("alpha", "level")),
                    "OneSampleAnalysis",
                    _binomial_test,
                    documentation="One-sided exact binomial test. Null: response rate <= "
                    "null_rate. Rejects at the smallest response count whose upper tail "
                    "probability at null_rate is at most alpha.",
                    lean=in_lean("analysis", ONE_SAMPLE),
                ),
                _constructor(
                    "binomial_score_test",
                    (
                        ("model", OneArmModelIR),
                        ("null_rate", "number"),
                        ("squared_cutoff", "number"),
                        ("alpha", "level"),
                    ),
                    "OneSampleScoreAnalysis",
                    _binomial_score_test,
                    documentation="Two-sided one-sample score rule for a binomial response "
                    "rate equal to null_rate. Lean checks the exact rejection probability "
                    "at that rate against the requested finite-sample ceiling.",
                    lean=in_lean("analysis", "Modules/OneSampleScore"),
                ),
                TYPE_I,
                _constructor(
                    "confidence_interval",
                    (("model", OneArmModelIR), ("count", "integer"), ("level", "number")),
                    "IntervalClaim",
                    _interval,
                    documentation="Exact (Clopper-Pearson) confidence interval for the response "
                    "rate. Endpoints are rounded outward to four decimals, so coverage is at "
                    "least the stated level for every true rate.",
                    lean=in_lean("claim", INTERVALS, INTERVAL),
                ),
                _constructor(
                    "responses",
                    (("analysis", OneSampleAnalysisIR), ("count", "integer")),
                    "OneSampleObservation",
                    _responses,
                    documentation="The observed number of responses for this analysis.",
                    lean=in_lean("data", ONE_SAMPLE),
                ),
                _constructor(
                    "binomial_result",
                    (("observation", OneSampleObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                    documentation="Claim about the exact p-value and decision for the "
                    "observed count, with the test's Type I bound.",
                    lean=in_lean("claim", RESULTS, ONE_SAMPLE),
                ),
            ),
        ),
    )
}
