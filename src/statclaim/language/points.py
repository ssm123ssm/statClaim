"""Builders for planning points and targets, and predicates on them."""

from collections.abc import Callable
from fractions import Fraction

from statclaim.family import MAX_ENDPOINTS
from statclaim.incidence import (
    MAX_EVENTS,
)
from statclaim.language.core import (
    LocatedValue,
    fail,
)
from statclaim.language.ir import (
    AssociationAnalysisIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    CorrelationIR,
    CountCandidatesIR,
    DiscordantPairsIR,
    EndpointPointsIR,
    ExponentialSurvivalIR,
    ExposurePrevalenceIR,
    GroupCandidatesIR,
    HazardRatioIR,
    IncidenceRatesIR,
    MatchedAnalysisIR,
    MatchedStudyIR,
    MeanDifferenceIR,
    NullScenariosIR,
    OddsPerSdIR,
    OutcomeMeansIR,
    OutcomePrevalenceIR,
    PersonTimeStudyIR,
    PlanningPointIR,
    PowerTargetIR,
    RateAnalysisIR,
    RatesIR,
    ReestimationIR,
    RisksIR,
    SlopeIR,
    TotalCandidatesIR,
)
from statclaim.language_syntax import (
    Span,
)
from statclaim.observational_planning import (
    MAX_GROUP,
    MAX_TOTAL,
)
from statclaim.observational_planning import SEARCH_KEYS as GROUP_SEARCH_KEYS
from statclaim.planning import (
    MAX_CITED_ARM,
    MAX_CITED_TOTAL,
    MAX_RATIO,
)
from statclaim.simulation import (
    MAX_SKEWNESS,
)


def skewed(point) -> bool:
    """Whether a planning point describes skewed data, for simulation."""
    return any(getattr(point, name, None) for name in ("skewness", "exposure_skewness"))


def departs(point) -> bool:
    """Whether a planning point leaves normal data, with a common SD for two means."""
    sd_treatment = getattr(point, "sd_treatment", None)
    return skewed(point) or (sd_treatment is not None and sd_treatment != point.sd)


def participant_draws(point) -> bool:
    """Whether simulating at this point draws every participant, not summary statistics."""
    return isinstance(point, ExponentialSurvivalIR) or skewed(point)


SCENARIO_REFUSED = (
    "sd_treatment and skewness describe a scenario for simulating a two-sample t-test; "
    "leave them out here."
)


def _probability(argument: LocatedValue, name: str, *, positive: bool = False) -> Fraction:
    low_ok = argument.value > 0 if positive else argument.value >= 0
    if not (low_ok and argument.value <= 1):
        bounds = "(0, 1]" if positive else "[0, 1]"
        fail("domain", f"{name} must lie in {bounds}.", argument.span)
    return argument.value


def _icc(arguments: dict[str, LocatedValue]) -> Fraction | None:
    """The intracluster correlation, when given: from 0, independent participants, up to but
    not including 1, identical participants within a cluster."""
    icc = arguments.get("icc")
    if icc is None or icc.value is None:
        return None
    if not 0 <= icc.value < 1:
        fail("domain", "icc must lie in [0, 1).", icc.span)
    return icc.value


def _cluster_cv(arguments: dict[str, LocatedValue]) -> Fraction | None:
    """The coefficient of variation of cluster sizes, when given: 0 for equal clusters."""
    cv = arguments.get("cluster_size_cv")
    if cv is None or cv.value is None:
        return None
    if not 0 <= cv.value <= 3:
        fail("domain", "cluster_size_cv must lie between 0 and 3.", cv.span)
    return cv.value


def _rates(arguments: dict[str, LocatedValue], span: Span) -> RatesIR:
    return RatesIR(
        _probability(arguments["p_control"], "p_control"),
        _probability(arguments["p_treatment"], "p_treatment"),
        _icc(arguments),
        _cluster_cv(arguments),
    )


def _mean_difference(arguments: dict[str, LocatedValue], span: Span) -> MeanDifferenceIR:
    sd = arguments["sd"]
    if sd.value <= 0:
        fail("domain", "sd must be positive.", sd.span)
    sd_treatment, skewness = arguments.get("sd_treatment"), arguments.get("skewness")
    if sd_treatment is not None and sd_treatment.value is not None and sd_treatment.value <= 0:
        fail("domain", "sd_treatment must be positive.", sd_treatment.span)
    if skewness is not None and skewness.value is not None and abs(skewness.value) > MAX_SKEWNESS:
        fail(
            "domain",
            f"skewness must lie between -{MAX_SKEWNESS} and {MAX_SKEWNESS}.",
            skewness.span,
        )
    return MeanDifferenceIR(
        arguments["value"].value,
        sd.value,
        _icc(arguments),
        _cluster_cv(arguments),
        None if sd_treatment is None else sd_treatment.value,
        None if skewness is None else skewness.value,
    )


def _hazard_ratio(arguments: dict[str, LocatedValue], span: Span) -> HazardRatioIR:
    ratio, events = arguments["value"], arguments["events"]
    if ratio.value <= 0:
        fail("domain", "A hazard ratio must be positive.", ratio.span)
    if events.value < 1:
        fail("domain", "events must be a positive integer.", events.span)
    return HazardRatioIR(ratio.value, events.value)


def _exponential_survival(arguments: dict[str, LocatedValue], span: Span) -> ExponentialSurvivalIR:
    ratio, median = arguments["hazard_ratio"], arguments["control_median"]
    accrual, follow_up = arguments["accrual"], arguments["follow_up"]
    if ratio.value <= 0:
        fail("domain", "A hazard ratio must be positive.", ratio.span)
    if median.value <= 0:
        fail("domain", "control_median must be a positive time.", median.span)
    for argument, name in ((accrual, "accrual"), (follow_up, "follow_up")):
        if argument.value < 0:
            fail("domain", f"{name} must be a time of at least 0.", argument.span)
    if accrual.value + follow_up.value <= 0:
        fail("domain", "accrual and follow_up cannot both be 0: no one would be followed.", span)
    dropout, when = arguments.get("dropout"), arguments.get("dropout_time")
    given = [a for a in (dropout, when) if a is not None and a.value is not None]
    if len(given) == 1:
        fail(
            "domain",
            "Give dropout and dropout_time together: the probability of dropping out by that "
            "time, such as dropout=1/10, dropout_time=12.",
            given[0].span,
        )
    if given:
        if not 0 <= dropout.value < 1:
            fail("domain", "dropout must lie in [0, 1).", dropout.span)
        if when.value <= 0:
            fail("domain", "dropout_time must be a positive time.", when.span)
    delay = arguments.get("effect_delay")
    if delay is not None and delay.value is not None and delay.value < 0:
        fail("domain", "effect_delay must be a time of at least 0.", delay.span)
    return ExponentialSurvivalIR(
        ratio.value,
        median.value,
        accrual.value,
        follow_up.value,
        dropout.value if given else None,
        when.value if given else None,
        None if delay is None else delay.value,
    )


def _correlation(arguments: dict[str, LocatedValue], span: Span) -> CorrelationIR:
    rho = arguments["value"]
    if not -1 < rho.value < 1:
        fail("domain", "A correlation must lie strictly between -1 and 1.", rho.span)
    return CorrelationIR(rho.value, *_skews(arguments))


def _outcome_means(arguments: dict[str, LocatedValue], span: Span) -> OutcomeMeansIR:
    sd = arguments["sd"]
    if sd.value <= 0:
        fail("domain", "sd must be positive.", sd.span)
    share = arguments.get("exposed_share")
    exposed_share = None if share is None or share.value is None else share.value
    if exposed_share is not None and not 0 < exposed_share < 1:
        fail("domain", "exposed_share must lie strictly between 0 and 1.", share.span)
    return OutcomeMeansIR(
        arguments["unexposed"].value,
        arguments["exposed"].value,
        sd.value,
        exposed_share,
        _design_effect(arguments),
    )


def _odds_per_sd(arguments: dict[str, LocatedValue], span: Span) -> OddsPerSdIR:
    ratio = arguments["odds_ratio"]
    if ratio.value <= 0:
        fail("domain", "odds_ratio must be positive.", ratio.span)
    baseline = _probability(arguments["baseline"], "baseline")
    if baseline in (0, 1):
        fail("domain", "baseline must lie strictly between 0 and 1.", arguments["baseline"].span)
    explained = arguments.get("exposure_r2")
    share = None if explained is None or explained.value is None else explained.value
    if share is not None and not 0 <= share < 1:
        fail("domain", "exposure_r2 must lie in [0, 1).", explained.span)
    return OddsPerSdIR(ratio.value, baseline, share, _design_effect(arguments))


def _slope(arguments: dict[str, LocatedValue], span: Span) -> SlopeIR:
    for name in ("exposure_sd", "residual_sd"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be positive.", arguments[name].span)
    explained = arguments.get("exposure_r2")
    share = None if explained is None or explained.value is None else explained.value
    if share is not None and not 0 <= share < 1:
        fail("domain", "exposure_r2 must lie in [0, 1).", explained.span)
    return SlopeIR(
        arguments["value"].value,
        arguments["exposure_sd"].value,
        arguments["residual_sd"].value,
        share,
        _design_effect(arguments),
        *_skews(arguments),
    )


def _skews(arguments: dict[str, LocatedValue]) -> tuple:
    """The skewness of the outcome's error and of the exposure, for simulation."""
    found = []
    for name in ("skewness", "exposure_skewness"):
        given = arguments.get(name)
        if given is not None and given.value is not None and abs(given.value) > MAX_SKEWNESS:
            fail(
                "domain", f"{name} must lie between -{MAX_SKEWNESS} and {MAX_SKEWNESS}.", given.span
            )
        found.append(None if given is None else given.value)
    return tuple(found)


def _power_target(arguments: dict[str, LocatedValue], span: Span) -> PowerTargetIR:
    nulls, rejecting = arguments.get("nulls"), arguments.get("rejecting")
    if rejecting is not None and rejecting.value is not None and rejecting.value not in REJECTING:
        fail("domain", 'rejecting is "any" or "all".', rejecting.span)
    return PowerTargetIR(
        arguments["at"].value,
        _probability(arguments["minimum"], "minimum", positive=True),
        arguments["maximum_typeI"].value,
        None if nulls is None else nulls.value,
        None if rejecting is None else rejecting.value,
    )


REJECTING = ("any", "all")


def _endpoint_points(arguments: dict[str, LocatedValue], span: Span) -> EndpointPointsIR:
    items, correlation = arguments["at"].value, arguments["correlation"]
    if not 2 <= len(items) <= MAX_ENDPOINTS:
        fail("domain", f"Give between 2 and {MAX_ENDPOINTS} points.", arguments["at"].span)
    for item in items:
        if not isinstance(item.value, (RatesIR, MeanDifferenceIR)):
            fail(
                "type",
                "Each endpoint's point is binomial_rates(...) for a yes-or-no endpoint or "
                "mean_difference(...) for a measured one.",
                item.span,
            )
    if not 0 <= correlation.value < 1:
        fail("domain", "correlation must lie in [0, 1).", correlation.span)
    return EndpointPointsIR(tuple(item.value for item in items), correlation.value)


MAX_NULL_SCENARIOS = 20


def _null_scenarios(arguments: dict[str, LocatedValue], span: Span) -> NullScenariosIR:
    items = arguments["at"].value
    if not 1 <= len(items) <= MAX_NULL_SCENARIOS:
        fail(
            "domain",
            f"List between 1 and {MAX_NULL_SCENARIOS} null scenarios.",
            arguments["at"].span,
        )
    for item in items:
        if not isinstance(item.value, PlanningPointIR):
            fail(
                "type",
                "Each null scenario is a planning point at the null, such as "
                "mean_difference(value=0, sd=10).",
                item.span,
            )
        if type(item.value) is not type(items[0].value):
            fail("type", "Every null scenario must be the same kind of point.", item.span)
    return NullScenariosIR(tuple(item.value for item in items))


REESTIMATED_TESTS = ("t_test", "t_test_one_sided")


def _reestimation(arguments: dict[str, LocatedValue], span: Span) -> ReestimationIR:
    analysis = arguments["analysis"]
    test = analysis.value
    if not isinstance(test, CitedAnalysisIR) or test.method.key not in REESTIMATED_TESTS:
        fail(
            "unsupported_claim",
            "Blinded re-estimation is simulated for Student's t-test: t_test or t_test_one_sided.",
            analysis.span,
        )
    model = test.plan.model
    if model.n_control != model.n_treatment:
        fail(
            "domain",
            "Blinded re-estimation keeps the arms equal: give the analysis equal arm sizes.",
            analysis.span,
        )
    interim, largest = arguments["interim_per_arm"], arguments["max_per_arm"]
    if not 2 <= interim.value < model.n_control:
        fail(
            "domain",
            f"interim_per_arm must be at least 2 and below the planned {model.n_control} per arm.",
            interim.span,
        )
    if not model.n_control <= largest.value <= MAX_CITED_ARM:
        fail(
            "domain",
            f"max_per_arm must lie from the planned {model.n_control} to {MAX_CITED_ARM}.",
            largest.span,
        )
    difference = arguments["difference"]
    if difference.value == 0:
        fail(
            "domain",
            "The planned difference cannot be 0: no size would detect it.",
            difference.span,
        )
    power = arguments["power"]
    if not 0 < power.value < 1:
        fail("domain", "power must lie strictly between 0 and 1.", power.span)
    return ReestimationIR(test, interim.value, difference.value, power.value, largest.value)


def _reference_and_other(
    arguments: dict[str, LocatedValue],
    span: Span,
    reference: str,
    other: str,
    measure: str,
) -> tuple[Fraction, Fraction]:
    """A reference group's probability, and the other group's given directly or through the
    measure the design estimates."""
    base = _probability(arguments[reference], reference)
    given, ratio = arguments.get(other), arguments.get(measure)
    given = None if given is None or given.value is None else given
    ratio = None if ratio is None or ratio.value is None else ratio
    if (given is None) == (ratio is None):
        fail(
            "planning_point",
            f"Give {other}=... or {measure}=..., one of the two.",
            span,
        )
    if given is not None:
        return base, _probability(given, other)
    if ratio.value <= 0:
        fail("domain", f"{measure} must be positive.", ratio.span)
    if measure in ("risk_ratio", "prevalence_ratio"):
        noun = measure.removesuffix("_ratio")
        value = base * ratio.value
        if value > 1:
            fail(
                "domain",
                f"A {noun} ratio of {ratio.value} with a {noun} of {base} without exposure "
                f"gives a {noun} above 1.",
                ratio.span,
            )
        return base, value
    # The odds of exposure among cases are the odds among controls times the odds ratio.
    odds = ratio.value * base
    return base, odds / (1 - base + odds)


def _exposed_share(arguments: dict[str, LocatedValue]) -> Fraction | None:
    share = arguments.get("exposed_share")
    if share is None or share.value is None:
        return None
    if not 0 < share.value < 1:
        fail("domain", "exposed_share must lie strictly between 0 and 1.", share.span)
    return share.value


def _risks(arguments: dict[str, LocatedValue], span: Span) -> RisksIR:
    return RisksIR(
        *_reference_and_other(arguments, span, "unexposed", "exposed", "risk_ratio"),
        _exposed_share(arguments),
    )


def _design_effect(arguments: dict[str, LocatedValue]) -> Fraction | None:
    """A survey's design effect, when given: positive, and below 1 for a design, such as a
    stratified one, that is more precise than simple random sampling."""
    effect = arguments.get("design_effect")
    if effect is None or effect.value is None:
        return None
    if effect.value <= 0:
        fail("domain", "design_effect must be positive.", effect.span)
    return effect.value


def _outcome_prevalence(arguments: dict[str, LocatedValue], span: Span) -> OutcomePrevalenceIR:
    return OutcomePrevalenceIR(
        *_reference_and_other(arguments, span, "unexposed", "exposed", "prevalence_ratio"),
        _exposed_share(arguments),
        _design_effect(arguments),
    )


def _total_sizes(arguments: dict[str, LocatedValue], span: Span) -> TotalCandidatesIR:
    analysis, low, high = arguments["analysis"], arguments["min_n"], arguments["max_n"]
    if not isinstance(analysis.value, (AssociationAnalysisIR, CitedAssociationIR)):
        fail(
            "type",
            "total_sizes searches an observational study by its total: give it Fisher's test "
            "of association or a cited observational test.",
            analysis.span,
        )
    if analysis.value.plan.model.groups is not None:
        fail(
            "type",
            "total_sizes searches studies that fix only their total. This study fixes its "
            "groups: use cohort_sizes or case_control_sizes.",
            analysis.span,
        )
    if isinstance(analysis.value, CitedAssociationIR):
        fewest = len(analysis.value.covariates) + 3
        if low.value < fewest:
            fail(
                "domain",
                f"min_n must be at least {fewest}: the error needs a degree of freedom after "
                "the exposure, the intercept and the covariates.",
                low.span,
            )
        if high.value < low.value:
            fail("domain", "max_n must be at least min_n.", high.span)
        if high.value > MAX_CITED_TOTAL:
            fail("domain", f"max_n is currently limited to {MAX_CITED_TOTAL:,}.", high.span)
        return TotalCandidatesIR(analysis.value, low.value, high.value)
    if low.value < 1:
        fail("domain", "min_n must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_n must be at least min_n.", high.span)
    if high.value > MAX_TOTAL:
        fail("domain", f"Exact power is limited to {MAX_TOTAL} participants in all.", high.span)
    return TotalCandidatesIR(analysis.value, low.value, high.value)


def _exposure_prevalence(arguments: dict[str, LocatedValue], span: Span) -> ExposurePrevalenceIR:
    return ExposurePrevalenceIR(
        *_reference_and_other(arguments, span, "controls", "cases", "odds_ratio")
    )


def _discordant_pairs(arguments: dict[str, LocatedValue], span: Span) -> DiscordantPairsIR:
    share, ratio = arguments["share"], arguments["odds_ratio"]
    if not 0 < share.value <= 1:
        fail("domain", "share must lie in (0, 1]: some pairs must be discordant.", share.span)
    if ratio.value <= 0:
        fail("domain", "odds_ratio must be positive.", ratio.span)
    return DiscordantPairsIR(share.value, ratio.value)


def _incidence_rates(arguments: dict[str, LocatedValue], span: Span) -> IncidenceRatesIR:
    for name in ("rate_ratio", "exposed_time", "unexposed_time"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be positive.", arguments[name].span)
    events = arguments.get("events")
    count = None if events is None or events.value is None else events.value
    if count is not None and not 1 <= count <= MAX_EVENTS:
        fail("domain", f"events must be from 1 to {MAX_EVENTS}.", events.span)
    return IncidenceRatesIR(
        arguments["rate_ratio"].value,
        arguments["exposed_time"].value,
        arguments["unexposed_time"].value,
        count,
    )


def _count_sizes(unit: str, limit: int) -> Callable:
    exact = MatchedAnalysisIR if unit == "pairs" else RateAnalysisIR
    study = MatchedStudyIR if unit == "pairs" else PersonTimeStudyIR

    def build(arguments: dict[str, LocatedValue], span: Span) -> CountCandidatesIR:
        analysis = arguments["analysis"]
        cited = isinstance(analysis.value, CitedAssociationIR) and isinstance(
            analysis.value.plan.model, study
        )
        if not (isinstance(analysis.value, exact) or cited):
            fail(
                "type",
                f"This search counts {unit}: give it "
                + (
                    "McNemar's test or a conditional logistic regression of a matched study."
                    if unit == "pairs"
                    else "the rate test or a Poisson rate regression of a person-time cohort."
                ),
                analysis.span,
            )
        low, high = arguments[f"min_{unit}"], arguments[f"max_{unit}"]
        if low.value < 1:
            fail("domain", f"min_{unit} must be a positive integer.", low.span)
        if high.value < low.value:
            fail("domain", f"max_{unit} must be at least min_{unit}.", high.span)
        bound = MAX_CITED_TOTAL if cited else limit
        if high.value > bound:
            words = "is currently limited to" if cited else "Exact power is limited to"
            fail("domain", f"{words[0].upper()}{words[1:]} {bound:,} {unit}.", high.span)
        return CountCandidatesIR(analysis.value, low.value, high.value)

    return build


def _group_sizes(design: str) -> Callable:
    low_key, high_key, ratio_key = GROUP_SEARCH_KEYS[design]
    study = {
        "cohort": "a cohort that sampled its exposed and unexposed groups",
        "case_control": "a case-control study",
    }[design]

    def build(arguments: dict[str, LocatedValue], span: Span) -> GroupCandidatesIR:
        analysis, low, high = arguments["analysis"], arguments[low_key], arguments[high_key]
        if not isinstance(analysis.value, (AssociationAnalysisIR, CitedAssociationIR)):
            fail(
                "type",
                f"{design}_sizes searches Fisher's test of association or a cited "
                "observational test.",
                analysis.span,
            )
        model = analysis.value.plan.model
        if model.design != design:
            fail(
                "type",
                f"{design}_sizes searches the sizes of {study}; this analysis's study is "
                "another design.",
                analysis.span,
            )
        if model.groups is None:
            fail(
                "unsupported_claim",
                "This cohort fixes only its total, so how many are exposed is random; its "
                "power is not available yet. Declare exposed and unexposed when the groups "
                "are sampled separately.",
                analysis.span,
            )
        ratio = arguments.get(ratio_key)
        each = 1 if ratio is None or ratio.value is None else ratio.value
        if not 1 <= each <= MAX_RATIO:
            fail("domain", f"{ratio_key} must be from 1 to {MAX_RATIO}.", ratio.span)
        if low.value < 1:
            fail("domain", f"{low_key} must be a positive integer.", low.span)
        if high.value < low.value:
            fail("domain", f"{high_key} must be at least {low_key}.", high.span)
        cited = isinstance(analysis.value, CitedAssociationIR)
        if cited and high.value * (1 + each) > MAX_CITED_TOTAL:
            fail(
                "domain",
                f"The total is currently limited to {MAX_CITED_TOTAL:,} participants.",
                high.span,
            )
        if not cited and high.value * each > MAX_GROUP:
            fail(
                "domain",
                f"Exact power is limited to {MAX_GROUP} participants in each group.",
                high.span,
            )
        return GroupCandidatesIR(analysis.value, low.value, high.value, each)

    return build


# The planning point each observational design is planned at.
GROUP_POINTS = {
    "cohort": (RisksIR, "risks(unexposed=..., exposed=...)"),
    "case_control": (ExposurePrevalenceIR, "exposure_prevalence(controls=..., cases=...)"),
    "cross_sectional": (
        OutcomePrevalenceIR,
        "outcome_prevalence(unexposed=..., exposed=..., exposed_share=...)",
    ),
}
