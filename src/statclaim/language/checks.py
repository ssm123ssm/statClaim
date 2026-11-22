"""Checks that a planning point and target fit an analysis, and meets(...)."""

from statclaim.association import (
    MEASURES,
    not_estimable,
)
from statclaim.incidence import (
    proportion_not_estimable,
)
from statclaim.language.analyses import (
    _test_key,
)
from statclaim.language.core import (
    LocatedValue,
    fail,
)
from statclaim.language.designs import (
    BINOMIAL_ASSUMPTIONS,
    check_design,
)
from statclaim.language.ir import (
    AnalysisIR,
    AssociationAnalysisIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    ClaimIR,
    CorrelationIR,
    DiscordantPairsIR,
    EndpointPointsIR,
    ExponentialSurvivalIR,
    ExposurePrevalenceIR,
    FamilyIR,
    FamilyLikeIR,
    FeasibilityIR,
    HazardRatioIR,
    IncidenceRatesIR,
    IntervalCandidatesIR,
    MatchedAnalysisIR,
    MeanDifferenceIR,
    ModelIR,
    ObservationalStudyIR,
    OddsPerSdIR,
    OneArmModelIR,
    OneSampleAnalysisIR,
    OutcomeMeansIR,
    OutcomePrevalenceIR,
    PlannableIR,
    PlannedIntervalIR,
    PlanningPointIR,
    PrecisionTargetIR,
    RateAnalysisIR,
    RateIR,
    RatesIR,
    ReestimationIR,
    RisksIR,
    SequentialIR,
    SingleProportionIR,
    SlopeIR,
    TwoStageAnalysisIR,
    group_probabilities,
)
from statclaim.language.normalize import (
    _check_skewed_point,
)
from statclaim.language.points import (
    GROUP_POINTS,
    SCENARIO_REFUSED,
    _design_effect,
)
from statclaim.language_syntax import (
    Span,
)
from statclaim.methods import NULL_FORMS, methods_for
from statclaim.methods.observational import (
    METHODS as OBSERVATIONAL_METHODS,
)
from statclaim.observational_planning import (
    MAX_GROUP,
    MAX_PLANNED_PAIRS,
    MAX_TOTAL,
)
from statclaim.planning import (
    MAX_RATIO,
)
from statclaim.precision import MAX_EXACT_PAIRS
from statclaim.precision import MAX_SIZE as MAX_PRECISION_SIZE
from statclaim.precision import MEASURES as PLANNED_MEASURES
from statclaim.precision import METHODS as PRECISION_METHODS


def _check_count_point(analysis, target: LocatedValue, where: Span) -> None:
    """McNemar's test is planned at discordant_pairs, the rate test at incidence_rates."""
    point = target.value.at
    if isinstance(analysis, MatchedAnalysisIR):
        if not isinstance(point, DiscordantPairsIR):
            fail(
                "planning_point",
                "Plan a matched study at discordant_pairs(share=..., odds_ratio=...).",
                target.span,
            )
        ratio = point.odds_ratio
    else:
        if not isinstance(point, IncidenceRatesIR):
            fail(
                "planning_point",
                "Plan a person-time cohort at incidence_rates(rate_ratio=..., exposed_time=..., "
                "unexposed_time=..., events=...).",
                target.span,
            )
        ratio = point.rate_ratio
    if ratio == 1:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({analysis.hypothesis.statement}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _check_association_point(
    analysis: AssociationAnalysisIR, target: LocatedValue, where: Span
) -> None:
    """Fisher's test of association is planned when its design fixes both groups."""
    model, point = analysis.plan.model, target.value.at
    kind, signature = GROUP_POINTS[model.design]
    if model.design == "cohort" and model.groups is None:
        signature = "risks(unexposed=..., exposed=..., exposed_share=...)"
    if not isinstance(point, kind):
        fail(
            "planning_point",
            f"Plan a {model.design.replace('_', '-')} study at {signature}.",
            target.span,
        )
    share = getattr(point, "exposed_share", None)
    if model.groups is None:
        if share is None:
            fail(
                "planning_point",
                "This study fixes only its total, so how many are exposed is random. Give "
                "exposed_share, the probability that a participant is exposed.",
                target.span,
            )
    elif share is not None:
        fail(
            "planning_point",
            "This cohort sampled its exposed and unexposed groups in fixed numbers, so the "
            "share exposed is not random. Leave exposed_share out.",
            target.span,
        )
    first, second = group_probabilities(point)
    if first == second:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null "
            f"({analysis.hypothesis.statement}). Power is assessed at an alternative; choose "
            "a point outside the null.",
            target.span,
        )


# How to write the planning point each kind of power formula takes.
POINT_SIGNATURES = {
    "mean_difference": (MeanDifferenceIR, "mean_difference(value=..., sd=...)"),
    "binomial_rates": (RatesIR, "binomial_rates(p_control=..., p_treatment=...)"),
    "hazard_ratio": (HazardRatioIR, "hazard_ratio(value=..., events=...)"),
    "exponential_survival": (
        ExponentialSurvivalIR,
        "exponential_survival(hazard_ratio=..., control_median=..., accrual=..., follow_up=...)",
    ),
    "correlation": (CorrelationIR, "correlation(value=...)"),
    "slope": (SlopeIR, "slope(value=..., exposure_sd=..., residual_sd=...)"),
}


# A test of cluster summaries also takes the intracluster correlation.
CLUSTER_POINT_SIGNATURES = {
    "mean_difference": "mean_difference(value=..., sd=..., icc=...)",
    "binomial_rates": "binomial_rates(p_control=..., p_treatment=..., icc=...)",
}


ICC_REFUSED = (
    "icc is for a test of cluster summaries, such as cluster_t_test, in a cluster-randomised "
    "trial. This analysis takes participants one by one; leave icc out."
)


def clustered_test(analysis: object) -> bool:
    """Whether the analysis is a cited test of one summary per cluster."""
    return isinstance(analysis, CitedAnalysisIR) and analysis.method.unit == "cluster"


def cited_formula(analysis: CitedAnalysisIR, point: PlanningPointIR):
    """The cited test's power formula at this kind of planning point, or None."""
    return next(
        (f for f in analysis.method.formulas if isinstance(point, POINT_SIGNATURES[f.point][0])),
        None,
    )


def _check_cited_point(analysis: CitedAnalysisIR, target: LocatedValue, where: Span) -> None:
    """A cited test can be planned only with a power formula, at that formula's kind of point."""
    method, point = analysis.method, target.value.at
    if method.power is None:
        others = ", ".join(m.key for m in methods_for(method.outcome) if m.power) or "none"
        fail(
            "no_power_formula",
            f"{method.key} has no power formula, so its power cannot be calculated. Tests "
            f"for this outcome with one: {others}.",
            where,
        )
    formula = cited_formula(analysis, point)
    signature = POINT_SIGNATURES[(formula or method.power).point][1]
    if clustered_test(analysis):
        signature = CLUSTER_POINT_SIGNATURES[method.power.point]
    if formula is None:
        signatures = " or ".join(POINT_SIGNATURES[f.point][1] for f in method.formulas)
        if clustered_test(analysis):
            signatures = signature
        fail("planning_point", f"Plan {method.key} at {signatures}.", target.span)
    if clustered_test(analysis) and point.icc is None:
        fail(
            "planning_point",
            f"Plan {method.key} at {signature}: the intracluster correlation sets how much "
            "each cluster's summary varies, and so the power.",
            target.span,
        )
    if not clustered_test(analysis) and getattr(point, "icc", None) is not None:
        fail("planning_point", ICC_REFUSED, target.span)
    if not clustered_test(analysis) and getattr(point, "cluster_size_cv", None) is not None:
        fail(
            "planning_point",
            "cluster_size_cv describes the clusters of a cluster-randomised trial; leave it out.",
            target.span,
        )
    scenario = any(getattr(point, name, None) is not None for name in ("sd_treatment", "skewness"))
    if scenario and analysis.method.module != "tests.t":
        fail("planning_point", SCENARIO_REFUSED, target.span)
    model = analysis.plan.model
    if isinstance(point, HazardRatioIR) and point.events > model.n_control + model.n_treatment:
        fail(
            "planning_point",
            f"events cannot exceed the {model.n_control + model.n_treatment} participants "
            "in the design.",
            target.span,
        )
    null = analysis.hypothesis
    if isinstance(point, MeanDifferenceIR):
        effect = point.value
    elif isinstance(point, RatesIR):
        effect = point.p_treatment - point.p_control
    elif isinstance(point, ExponentialSurvivalIR):
        effect = point.hazard_ratio - 1
    else:
        effect = point.value - 1  # a hazard ratio of 1 is no effect
    favours = NULL_FORMS[null.predicate][1].favours
    outside = {
        "higher": effect > null.value,
        "lower": effect < null.value,
        None: effect != 0,
    }[favours]
    if not outside:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({null.statement}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


# The kinds of planning point a cited observational test's formula takes: the points of that
# kind, the exposure scale it needs, and how to write one.
OBSERVATIONAL_POINTS = {
    "association_groups": (
        (RisksIR, OutcomePrevalenceIR, ExposurePrevalenceIR),
        "binary",
        "the design's own point: risks(...), outcome_prevalence(...) or exposure_prevalence(...)",
    ),
    "odds_per_sd": ((OddsPerSdIR,), "continuous", "odds_per_sd(odds_ratio=..., baseline=...)"),
    "outcome_means": (
        (OutcomeMeansIR,),
        "binary",
        "outcome_means(unexposed=..., exposed=..., sd=...)",
    ),
    "correlation": ((CorrelationIR,), "continuous", "correlation(value=...)"),
    "slope": ((SlopeIR,), "continuous", "slope(value=..., exposure_sd=..., residual_sd=...)"),
    "discordant_pairs": (
        (DiscordantPairsIR,),
        "binary",
        "discordant_pairs(share=..., odds_ratio=...)",
    ),
    "incidence_rates": (
        (IncidenceRatesIR,),
        "binary",
        "incidence_rates(rate_ratio=..., exposed_time=..., unexposed_time=..., events=...)",
    ),
}


DESIGN_EFFECT_REFUSED = (
    "design_effect is for a survey test of a complex sample, such as survey_logistic. This "
    "analysis assumes a simple random sample; leave design_effect out."
)


def observational_formula(analysis: CitedAssociationIR, point: PlanningPointIR):
    """The cited observational test's power formula at this point and exposure scale."""
    scale = analysis.plan.model.exposure_scale
    for formula in analysis.method.formulas:
        kinds, needs, _ = OBSERVATIONAL_POINTS[formula.point]
        if isinstance(point, kinds) and needs == scale:
            return formula
    return None


def _check_cited_association_point(
    analysis: CitedAssociationIR, target: LocatedValue, where: Span
) -> None:
    """A cited observational test is planned at a point its formulas take, for the study's
    exposure scale, outside the null."""
    method, point = analysis.method, target.value.at
    if not method.formulas:
        others = ", ".join(m.key for m in OBSERVATIONAL_METHODS.values() if m.formulas)
        fail(
            "no_power_formula",
            f"{method.key} has no power formula yet, so its power cannot be calculated. Cited "
            f"observational tests with one: {others}.",
            where,
        )
    scale = analysis.plan.model.exposure_scale
    fitting = [f for f in method.formulas if OBSERVATIONAL_POINTS[f.point][1] == scale]
    if not fitting:
        scales = " or ".join(sorted({OBSERVATIONAL_POINTS[f.point][1] for f in method.formulas}))
        fail(
            "planning_point",
            f"{method.key}'s power formulas are for a {scales} exposure; this study declares a "
            f"{scale} exposure.",
            target.span,
        )
    formula = observational_formula(analysis, point)
    if formula is None:
        signatures = " or ".join(OBSERVATIONAL_POINTS[f.point][2] for f in fitting)
        fail("planning_point", f"Plan {method.key} at {signatures}.", target.span)
    model = analysis.plan.model
    if (
        method.module == "tests.survey"
        and model.survey != "simple_random"
        and getattr(point, "design_effect", None) is None
    ):
        fail(
            "planning_point",
            f"This survey samples by {model.survey} design, so its power depends on the design "
            "effect: give design_effect=..., the variance of the exposure's estimate over that "
            "of a simple random sample of the same size.",
            target.span,
        )
    if formula.point == "association_groups":
        _check_association_point(analysis, target, where)
        if method.key == "modified_poisson" and 0 in group_probabilities(point):
            fail(
                "domain",
                "A risk or prevalence ratio needs the outcome in both groups: give "
                "probabilities above 0.",
                target.span,
            )
        return
    if formula.point == "outcome_means":
        share = point.exposed_share
        if model.groups is None and share is None:
            fail(
                "planning_point",
                "This study fixes only its total, so how many are exposed is random. Give "
                "exposed_share, the probability that a participant is exposed.",
                target.span,
            )
        if model.groups is not None and share is not None:
            fail(
                "planning_point",
                "This cohort sampled its exposed and unexposed groups in fixed numbers, so the "
                "share exposed is not random. Leave exposed_share out.",
                target.span,
            )
    effect = {
        "outcome_means": lambda: point.exposed - point.unexposed,
        "odds_per_sd": lambda: point.odds_ratio - 1,
        "correlation": lambda: point.value,
        "slope": lambda: point.value,
        "discordant_pairs": lambda: point.odds_ratio - 1,
        "incidence_rates": lambda: point.rate_ratio - 1,
    }[formula.point]()
    if effect == 0:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({analysis.hypothesis.statement}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _check_point(analysis: PlannableIR, target: LocatedValue, where: Span) -> None:
    """The planning point must belong to the analysis's parameter space, outside its null."""
    point = target.value.at
    if isinstance(analysis, ReestimationIR):
        _check_reestimation_point(analysis, target)
        _check_cited_point(analysis.analysis, target, where)
        return
    if getattr(target.value, "nulls", None) is not None:
        fail(
            "planning_point",
            "null_scenarios are for a design whose Type I error is judged by simulation, such "
            "as blinded_reestimation(...). This analysis's level is proved or cited; leave "
            "nulls out.",
            target.span,
        )
    family = isinstance(analysis, FamilyLikeIR) and not isinstance(analysis, SequentialIR)
    if family:
        _check_family_point(analysis, target)
        return
    if getattr(target.value, "rejecting", None) is not None:
        fail(
            "planning_point",
            "rejecting is for a family of tests: whether its power means rejecting any "
            "endpoint or all of them. Leave it out here.",
            target.span,
        )
    if isinstance(point, EndpointPointsIR):
        fail(
            "planning_point",
            "endpoint_points(...) is for a family of tests; give this analysis one point.",
            target.span,
        )
    if isinstance(analysis, SequentialIR):
        _check_sequential(analysis, where)
        if exact_looks(analysis):
            _check_point(analysis.final, target, where)
        else:
            _check_cited_point(analysis.final, target, where)
        return
    if isinstance(analysis, CitedAnalysisIR):
        _check_cited_point(analysis, target, where)
        return
    if any(getattr(point, name, None) is not None for name in ("icc", "cluster_size_cv")):
        fail("planning_point", ICC_REFUSED, target.span)
    if getattr(point, "sd_treatment", None) is not None or (
        isinstance(point, MeanDifferenceIR) and point.skewness is not None
    ):
        fail("planning_point", SCENARIO_REFUSED, target.span)
    if any(getattr(point, name, None) is not None for name in ("skewness", "exposure_skewness")):
        _check_skewed_point(analysis, target)
    survey = isinstance(analysis, CitedAssociationIR) and analysis.method.module == "tests.survey"
    if getattr(point, "design_effect", None) is not None and not survey:
        fail("planning_point", DESIGN_EFFECT_REFUSED, target.span)
    if isinstance(analysis, CitedAssociationIR):
        _check_cited_association_point(analysis, target, where)
        return
    if isinstance(analysis, AssociationAnalysisIR):
        _check_association_point(analysis, target, where)
        return
    if isinstance(analysis, (MatchedAnalysisIR, RateAnalysisIR)):
        _check_count_point(analysis, target, where)
        return
    if isinstance(analysis, (TwoStageAnalysisIR, OneSampleAnalysisIR)):
        if not isinstance(point, RateIR):
            fail(
                "planning_point",
                "A single-arm analysis has one response rate. "
                "Declare the target at response_rate(value=...).",
                target.span,
            )
        null = f"response rate <= {analysis.null_rate}"
        outside = point.value > analysis.null_rate
    else:
        if not isinstance(point, RatesIR):
            fail(
                "planning_point",
                "A two-arm analysis needs both rates. "
                "Declare the target at binomial_rates(p_control=..., p_treatment=...).",
                target.span,
            )
        if analysis.alternative == "margin":
            margin = analysis.hypothesis.value
            null = f"p_treatment - p_control <= {margin}"
            outside = point.p_treatment - point.p_control > margin
        elif analysis.alternative == "greater":
            null, outside = "p_treatment <= p_control", point.p_treatment > point.p_control
        else:
            null, outside = "p_treatment = p_control", point.p_control != point.p_treatment
    if not outside:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({null}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _residual_df(analysis: CitedAssociationIR, n: int) -> int:
    """Degrees of freedom left for a regression's error: n less the slope, the intercept and
    the covariates."""
    return n - len(analysis.covariates) - 2


SIMULATION_SCENARIO = ("icc", "cluster_size_cv", "sd_treatment", "skewness")


def _check_reestimation_point(design: ReestimationIR, target: LocatedValue) -> None:
    """Normal outcomes with a common SD, and the nulls at which Type I error is judged."""
    point, nulls = target.value.at, target.value.nulls
    plain = (
        "Blinded re-estimation is simulated for normal outcomes with a common SD: give "
        "mean_difference(value=..., sd=...)"
    )
    if not isinstance(point, MeanDifferenceIR) or any(
        getattr(point, name, None) is not None for name in SIMULATION_SCENARIO
    ):
        fail("planning_point", plain + ".", target.span)
    if nulls is None:
        fail(
            "planning_point",
            "The Type I error of a re-estimated design is not proved. List the nulls at which "
            "to judge it: power_target(..., nulls=null_scenarios(at=[mean_difference(value="
            f"{design.analysis.hypothesis.value}, sd=...), ...])).",
            target.span,
        )
    for null in nulls.points:
        if not isinstance(null, MeanDifferenceIR) or any(
            getattr(null, name, None) is not None for name in SIMULATION_SCENARIO
        ):
            fail("planning_point", plain + " for each null scenario.", target.span)
        if null.value != design.analysis.hypothesis.value:
            fail(
                "planning_point",
                f"A null scenario lies on the null: its difference must be "
                f"{design.analysis.hypothesis.value}, not {null.value}.",
                target.span,
            )


FAMILY_MODES = {
    "family": "bonferroni",
    "fixed_sequence": "fixed_sequence",
    "graphical": "graphical",
}


def family_procedure(family: FamilyLikeIR) -> str:
    """How a family rejects: each member at its own level, in order, or along a graph."""
    return "bonferroni" if isinstance(family, FamilyIR) else FAMILY_MODES[family.mode]


def endpoint_kind(analysis) -> str | None:
    """A member simulated in a family: "binary" for Fisher's test, "measured" for a t-test."""
    if isinstance(analysis, AnalysisIR) and analysis.alternative in ("two_sided", "greater"):
        return "binary"
    if isinstance(analysis, CitedAnalysisIR) and analysis.method.module == "tests.t":
        return "measured"
    return None


def _outside_null(analysis, point) -> bool:
    if isinstance(point, RatesIR):
        if analysis.alternative == "greater":
            return point.p_treatment > point.p_control
        return point.p_treatment != point.p_control
    null = analysis.hypothesis
    favours = NULL_FORMS[null.predicate][1].favours
    if favours == "higher":
        return point.value > null.value
    if favours == "lower":
        return point.value < null.value
    return point.value != null.value


def _check_family_point(family: FamilyLikeIR, target: LocatedValue) -> None:
    """One point per member, of its kind; any or all; shared participants when correlated."""
    point, members = target.value.at, family.analyses
    if not isinstance(family, FamilyIR) and family.mode not in FAMILY_MODES:
        fail("unsupported_claim", "This kind of family is not simulated yet.", target.span)
    if not isinstance(point, EndpointPointsIR):
        fail(
            "planning_point",
            "A family's power is planned at endpoint_points(at=[one point per member, in "
            "order], correlation=...).",
            target.span,
        )
    if len(point.points) != len(members):
        fail(
            "planning_point",
            f"The family has {len(members)} members, so give {len(members)} points, in order.",
            target.span,
        )
    if target.value.rejecting is None:
        fail(
            "planning_point",
            "Say whether the family's power means rejecting any endpoint or all of them: "
            'power_target(..., rejecting="any") or rejecting="all".',
            target.span,
        )
    for (name, analysis), member_point in zip(members, point.points, strict=True):
        kind = endpoint_kind(analysis)
        if kind is None:
            fail(
                "unsupported_claim",
                f"{name}: a family's power is simulated for members that are Fisher's test or "
                "the t-tests; this member is not simulated yet.",
                target.span,
            )
        wanted = RatesIR if kind == "binary" else MeanDifferenceIR
        scenario = any(
            getattr(member_point, field, None) is not None for field in SIMULATION_SCENARIO
        )
        if not isinstance(member_point, wanted) or scenario:
            words = "binomial_rates(...)" if kind == "binary" else "mean_difference(value, sd)"
            fail("planning_point", f"{name} is planned at {words}.", target.span)
    if point.correlation > 0:
        sizes = {(a.plan.model.n_control, a.plan.model.n_treatment) for _, a in members}
        if len(sizes) > 1:
            fail(
                "planning_point",
                "Correlated endpoints are measured on the same participants: give every "
                "member the same arm sizes, or correlation=0.",
                target.span,
            )
    if not any(_outside_null(a, p) for (_, a), p in zip(members, point.points, strict=True)):
        fail(
            "planning_point",
            "At least one endpoint's point must lie outside its null; otherwise there is no "
            "power to plan.",
            target.span,
        )


def exact_looks(analysis: SequentialIR) -> bool:
    """Whether a design's looks are Fisher's test, whose power is summed exactly."""
    look = analysis.final
    return isinstance(look, AnalysisIR) and look.alternative in ("two_sided", "greater")


MAX_LOOK_ARM = 500  # participants per arm at the last look, for the exact sum


def _check_sequential(analysis: SequentialIR, where: Span) -> None:
    """A design with looks is planned exactly for Fisher's test, and by simulation for tests
    with a simulation model for looks."""
    look = analysis.final
    if exact_looks(analysis):
        model = look.plan.model
        if max(model.n_control, model.n_treatment) > MAX_LOOK_ARM:
            fail(
                "domain",
                f"The exact power of Fisher's test at looks is summed up to {MAX_LOOK_ARM} per "
                "arm at the last look.",
                where,
            )
        return
    model = getattr(getattr(look, "method", None), "simulation", None)
    if not isinstance(look, CitedAnalysisIR) or model is None or model.looks is None:
        key = getattr(getattr(look, "method", None), "key", None) or _test_key(look)
        fail(
            "unsupported_claim",
            f"The power of a design with looks is exact for Fisher's test and simulated for "
            f"the t-tests; {key} looks are not supported yet.",
            where,
        )


def _check_planned_size(analysis: PlannableIR, where: Span, point=None) -> None:
    """The declared study's size, for exact power at it; a search checks its own bounds."""
    if (
        isinstance(analysis, CitedAssociationIR)
        and analysis.method.module != "tests.survey"
        and observational_formula(analysis, point).point
        in ("correlation", "slope", "outcome_means")
        and _residual_df(analysis, analysis.plan.model.total) < 1
    ):
        fail(
            "domain",
            f"{analysis.plan.model.total} participants leave no degrees of freedom for the "
            f"error after the exposure, the intercept and {len(analysis.covariates)} covariates.",
            where,
        )
    if isinstance(analysis, MatchedAnalysisIR) and analysis.plan.model.pairs > MAX_PLANNED_PAIRS:
        fail("domain", f"Exact power is limited to {MAX_PLANNED_PAIRS} pairs.", where)
    if not isinstance(analysis, AssociationAnalysisIR):
        return
    model = analysis.plan.model
    if model.groups is None and model.n > MAX_TOTAL:
        fail(
            "domain",
            f"Exact power is limited to {MAX_TOTAL} participants in all when only the total "
            "is fixed.",
            where,
        )
    if model.groups is not None and max(model.groups) > MAX_GROUP:
        fail("domain", f"Exact power is limited to {MAX_GROUP} participants in each group.", where)


def _design_name(model: object) -> str | None:
    if isinstance(model, OneArmModelIR):
        return "one_arm"
    if isinstance(model, ModelIR):
        return "two_arm"
    if isinstance(model, ObservationalStudyIR):
        return model.design
    return None


def _planned_interval(arguments: dict[str, LocatedValue], span: Span) -> PlannedIntervalIR:
    model, measure = arguments["model"], arguments["measure"]
    method_arg, group_arg = arguments.get("method"), arguments.get("group")
    method = "exact" if method_arg is None or method_arg.value is None else method_arg.value
    group = None if group_arg is None or group_arg.value is None else group_arg.value
    design = _design_name(model.value)
    if design is None:
        fail(
            "type",
            "planned_interval takes a one-arm or two-arm binomial model, or an observational "
            "study.",
            model.span,
        )
    fitting = [key for key, (_, designs) in PLANNED_MEASURES.items() if design in designs]
    if measure.value not in PLANNED_MEASURES:
        fail(
            "domain",
            f"measure must be one of {', '.join(fitting)} for this design.",
            measure.span,
        )
    kind, designs = PLANNED_MEASURES[measure.value]
    if design not in designs:
        reason = (
            proportion_not_estimable(measure.value, design)
            if kind == "proportion" and design != "one_arm"
            else not_estimable(measure.value, design)
            if measure.value in MEASURES
            else None
        )
        fail(
            "not_estimable",
            f"{measure.value}: "
            + (reason or f"a {design.replace('_', '-')} design does not estimate it.")
            + f" This design estimates {', '.join(fitting) or 'none of them'}.",
            measure.span,
        )
    if method not in PRECISION_METHODS:
        fail("domain", 'method must be "exact" or "normal".', method_arg.span)
    if design == "two_arm":
        check_design(model.value, BINOMIAL_ASSUMPTIONS, "planned_interval", model.span)
    observed = model.value if isinstance(model.value, ObservationalStudyIR) else None
    if observed is not None:
        for which, scale in (
            ("outcome", observed.outcome_scale),
            ("exposure", observed.exposure_scale),
        ):
            if scale != "binary" and (which == "outcome" or kind != "proportion"):
                fail(
                    "type",
                    f"planned_interval({measure.value}) needs a yes-or-no {which}; this study "
                    f"declares a continuous {which}.",
                    model.span,
                )
        if method == "exact" and observed.survey != "simple_random":
            fail(
                "complex_sample",
                f"Exact intervals assume a simple random sample; this survey declares "
                f'{observed.survey} sampling. Use method="normal", with design_effect on the '
                "planning point.",
                model.span,
            )
    needs_group = kind == "proportion" and observed is not None and observed.groups is not None
    if needs_group and group not in ("exposed", "unexposed"):
        fail(
            "domain",
            "This cohort sampled exposed and unexposed groups separately, so say which: "
            'group="exposed" or group="unexposed".',
            span,
        )
    if not needs_group and group is not None:
        fail("domain", "This interval has no group to choose; leave group out.", group_arg.span)
    return PlannedIntervalIR(model.value, measure.value, method, group)


def _single_proportion(arguments: dict[str, LocatedValue], span: Span) -> SingleProportionIR:
    value = arguments["value"]
    if not 0 < value.value < 1:
        fail("domain", "value must lie strictly between 0 and 1.", value.span)
    population = arguments.get("population_size")
    size = None if population is None or population.value is None else population.value
    if size is not None and size < 2:
        fail("domain", "population_size must be at least 2.", population.span)
    return SingleProportionIR(value.value, _design_effect(arguments), size)


def _precision_target(arguments: dict[str, LocatedValue], span: Span) -> PrecisionTargetIR:
    level, assurance = arguments["level"], arguments.get("assurance")
    absolute, relative = arguments.get("margin_of_error"), arguments.get("relative_margin_of_error")
    given = [a for a in (absolute, relative) if a is not None and a.value is not None]
    if len(given) != 1:
        fail(
            "domain",
            "Give one of margin_of_error, half the interval's width, or "
            "relative_margin_of_error, a fraction of the planning value.",
            span,
        )
    if given[0].value <= 0:
        fail("domain", "The margin of error must be positive.", given[0].span)
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    chance = None if assurance is None or assurance.value is None else assurance.value
    if chance is not None and not 0 < chance < 1:
        fail("domain", "assurance must lie strictly between 0 and 1.", assurance.span)
    is_absolute = absolute is not None and absolute.value is not None
    return PrecisionTargetIR(
        arguments["at"].value,
        level.value,
        given[0].value if is_absolute else None,
        None if is_absolute else given[0].value,
        chance,
    )


def _two_group_sizes(interval: PlannedIntervalIR) -> bool:
    """Whether a search of this interval varies two fixed groups, the first with ratio of
    the second for each."""
    model = interval.model
    if isinstance(model, ModelIR):
        return True
    kind = PLANNED_MEASURES[interval.measure][0]
    return (
        isinstance(model, ObservationalStudyIR)
        and model.groups is not None
        and kind in ("difference", "ratio", "odds")
    )


def _interval_sizes(arguments: dict[str, LocatedValue], span: Span) -> IntervalCandidatesIR:
    interval, low, high = arguments["interval"], arguments["min_size"], arguments["max_size"]
    if not isinstance(interval.value, PlannedIntervalIR):
        fail("type", "interval_sizes searches a planned_interval(...).", interval.span)
    ratio = arguments.get("ratio")
    each = 1 if ratio is None or ratio.value is None else ratio.value
    if ratio is not None and ratio.value is not None and not _two_group_sizes(interval.value):
        fail(
            "domain",
            "ratio is for a design that samples two groups in fixed numbers; this search "
            "varies one size.",
            ratio.span,
        )
    if not 1 <= each <= MAX_RATIO:
        fail("domain", f"ratio must be from 1 to {MAX_RATIO}.", ratio.span)
    if low.value < 1:
        fail("domain", "min_size must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_size must be at least min_size.", high.span)
    exact_pairs = (
        interval.value.method == "exact" and interval.value.measure == "conditional_odds_ratio"
    )
    limit = MAX_EXACT_PAIRS if exact_pairs else MAX_PRECISION_SIZE
    if high.value * (1 + each if _two_group_sizes(interval.value) else 1) > limit:
        fail("domain", f"The search is currently limited to {limit:,} in all.", high.span)
    return IntervalCandidatesIR(interval.value, low.value, high.value, each)


def _check_precision(
    interval: PlannedIntervalIR, target: LocatedValue, where: Span, search: bool
) -> None:
    """A planned interval is planned at the point its measure takes, with a precision target
    its method can reach."""
    goal = target.value
    if not isinstance(goal, PrecisionTargetIR):
        fail(
            "planning_point",
            "A planned interval takes precision_target(at=..., level=..., margin_of_error=...), "
            "not a power target.",
            target.span,
        )
    point, model, measure = goal.at, interval.model, interval.measure
    kind = PLANNED_MEASURES[measure][0]
    exact = interval.method == "exact"
    if kind == "proportion":
        wanted = (
            (SingleProportionIR, RateIR)
            if isinstance(model, OneArmModelIR)
            else (SingleProportionIR,)
        )
        if not isinstance(point, wanted):
            fail("planning_point", f"Plan {measure} at proportion(value=...).", target.span)
        value = point.value
    elif kind == "difference" and isinstance(model, ModelIR):
        if not isinstance(point, RatesIR) or point.icc is not None:
            fail(
                "planning_point",
                "Plan the difference at binomial_rates(p_control=..., p_treatment=...).",
                target.span,
            )
        value = point.p_treatment - point.p_control
    elif kind in ("difference", "ratio", "odds"):
        wanted, signature = GROUP_POINTS[model.design]
        if model.design == "cohort" and model.groups is None:
            signature = "risks(unexposed=..., exposed=..., exposed_share=...)"
        if not isinstance(point, wanted):
            fail(
                "planning_point",
                f"Plan a {model.design.replace('_', '-')} study's {measure} at {signature}.",
                target.span,
            )
        share = getattr(point, "exposed_share", None)
        if model.groups is None and share is None:
            fail(
                "planning_point",
                "This study fixes only its total, so how many are exposed is random. Give "
                "exposed_share, the probability that a participant is exposed.",
                target.span,
            )
        if model.groups is not None and share is not None:
            fail(
                "planning_point",
                "This cohort sampled its exposed and unexposed groups in fixed numbers; leave "
                "exposed_share out.",
                target.span,
            )
        first, second = group_probabilities(point)
        if kind == "ratio" and 0 in (first, second):
            fail("domain", f"A {measure} needs both probabilities above 0.", target.span)
        if kind == "odds" and not (0 < first < 1 and 0 < second < 1):
            fail(
                "domain",
                "An odds ratio needs both probabilities strictly between 0 and 1.",
                target.span,
            )
        value = (
            second - first
            if kind == "difference"
            else (
                second / first
                if kind == "ratio"
                else (second / (1 - second)) / (first / (1 - first))
            )
        )
    elif kind == "matched":
        if not isinstance(point, DiscordantPairsIR):
            fail(
                "planning_point",
                "Plan the conditional odds ratio at discordant_pairs(share=..., odds_ratio=...).",
                target.span,
            )
        value = point.odds_ratio
    else:
        if not isinstance(point, IncidenceRatesIR):
            fail(
                "planning_point",
                "Plan the rate ratio at incidence_rates(rate_ratio=..., exposed_time=..., "
                "unexposed_time=..., events=...).",
                target.span,
            )
        if search and point.events is not None:
            fail(
                "planning_point",
                "interval_sizes searches the events; leave events out of incidence_rates.",
                target.span,
            )
        if not search and point.events is None:
            fail(
                "planning_point",
                "The rate ratio's interval is given the total events: give events=..., or "
                "search them with interval_sizes.",
                target.span,
            )
        value = point.rate_ratio
    if goal.relative is not None:
        if kind in ("proportion", "difference") and value == 0:
            fail(
                "planning_point",
                "A relative margin of error is a fraction of the planning value, which is 0 "
                "here; give margin_of_error instead.",
                target.span,
            )
        if kind not in ("proportion", "difference") and goal.relative >= 1:
            fail(
                "domain",
                "For a ratio, the relative margin of error r asks that the lower limit be at "
                "least (1 - r) times the estimate, so r must be below 1.",
                target.span,
            )
    effect = getattr(point, "design_effect", None)
    population = getattr(point, "population_size", None)
    survey = isinstance(model, ObservationalStudyIR) and model.survey != "simple_random"
    if exact and (effect is not None or population is not None):
        fail(
            "planning_point",
            "design_effect and population_size describe a survey's normal interval; the exact "
            'interval assumes a simple random sample. Use method="normal" for them.',
            target.span,
        )
    if survey and effect is None:
        fail(
            "planning_point",
            f"This survey samples by {model.survey} design: give design_effect=... on the "
            "planning point.",
            target.span,
        )
    if population is not None and not search and isinstance(model, ObservationalStudyIR):
        if population <= model.total:
            fail(
                "domain",
                f"population_size must exceed the {model.total} sampled.",
                target.span,
            )


def _meets(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis = arguments["analysis"]
    if isinstance(analysis.value, PlannedIntervalIR) or isinstance(
        arguments["target"].value, PrecisionTargetIR
    ):
        if not isinstance(analysis.value, PlannedIntervalIR):
            fail(
                "type",
                "precision_target is for planned_interval(...): a test is planned with "
                "power_target.",
                analysis.span,
            )
        _check_precision(analysis.value, arguments["target"], analysis.span, search=False)
        return ClaimIR(
            "meets",
            FeasibilityIR(analysis.value, arguments["target"].value),
            analysis.name or "<expression>",
        )
    _check_point(analysis.value, arguments["target"], analysis.span)
    _check_planned_size(analysis.value, analysis.span, arguments["target"].value.at)
    point = arguments["target"].value.at
    if isinstance(point, IncidenceRatesIR) and point.events is None:
        fail(
            "planning_point",
            "The rate test's power is given the total number of events. Give events=... in "
            "incidence_rates, or search the events with event_counts.",
            arguments["target"].span,
        )
    return ClaimIR(
        "meets",
        FeasibilityIR(analysis.value, arguments["target"].value),
        analysis.name or "<expression>",
    )
