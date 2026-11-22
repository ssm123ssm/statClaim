"""Builders for sample-size searches and single-arm and two-stage designs."""

from collections.abc import Callable

from statclaim.language.checks import (
    _check_point,
    _check_precision,
    clustered_test,
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
    CandidatesIR,
    CitedAnalysisIR,
    ClaimIR,
    ClusterCandidatesIR,
    DifferenceIntervalIR,
    HazardRatioIR,
    IncidenceRatesIR,
    IntervalCandidatesIR,
    IntervalIR,
    OneArmCandidatesIR,
    OneArmModelIR,
    OneSampleAnalysisIR,
    OneSampleObservationIR,
    PrecisionTargetIR,
    PriorIR,
    RuleIR,
    SizingIR,
    TotalCandidatesIR,
    TwoArmTestIR,
    TwoStageAnalysisIR,
    TwoStageCandidatesIR,
    TwoStageModelIR,
    TwoStageObservationIR,
)
from statclaim.language.points import (
    _probability,
)
from statclaim.language_syntax import (
    Span,
)
from statclaim.planning import (
    CRITERIA,
    MAX_CITED_ARM,
    MAX_CLUSTER_SIZE,
    MAX_CLUSTERS,
    MAX_MARGIN_ARM,
    MAX_ONE_ARM,
    MAX_PER_ARM,
    MAX_RATIO,
    MAX_SEARCH_TOTAL,
    MAX_STAGE,
    TwoStageRule,
)


def _arm_limit(analysis: TwoArmTestIR) -> int:
    """The largest arm a search may reach: exact tests are slower to evaluate."""
    if isinstance(analysis, CitedAnalysisIR):
        return MAX_CITED_ARM
    return MAX_MARGIN_ARM if getattr(analysis, "alternative", None) == "margin" else MAX_PER_ARM


def _not_clustered(analysis: LocatedValue) -> None:
    """A test of cluster summaries is sized in clusters, not participants."""
    if clustered_test(analysis.value):
        fail(
            "unsupported_claim",
            f"{analysis.value.method.key} takes one summary per cluster, so it is sized in "
            "clusters: search cluster_counts(...) for the number of clusters per arm, or "
            "cluster_sizes(...) for the participants in each cluster.",
            analysis.span,
        )


def _cluster_analysis(analysis: LocatedValue, search: str) -> CitedAnalysisIR:
    if not clustered_test(analysis.value):
        fail(
            "unsupported_claim",
            f"{search} searches a test of cluster summaries, such as cluster_t_test, in a "
            "cluster-randomised trial. Use equal_arm_sizes(...) for an analysis of "
            "participants.",
            analysis.span,
        )
    return analysis.value


def _cluster_counts(arguments: dict[str, LocatedValue], span: Span) -> ClusterCandidatesIR:
    analysis = _cluster_analysis(arguments["analysis"], "cluster_counts")
    size, low, high = (arguments[k] for k in ("cluster_size", "min_per_arm", "max_per_arm"))
    if not 1 <= size.value <= MAX_CLUSTER_SIZE:
        fail("domain", f"cluster_size must be between 1 and {MAX_CLUSTER_SIZE:,}.", size.span)
    fewest = analysis.method.min_per_arm
    if low.value < fewest:
        fail(
            "domain",
            f"{analysis.method.key} needs at least {fewest} clusters per arm, so min_per_arm "
            f"must be at least {fewest}.",
            low.span,
        )
    if high.value < low.value:
        fail("domain", "max_per_arm must be at least min_per_arm.", high.span)
    if high.value > MAX_CLUSTERS:
        fail("domain", f"max_per_arm is currently limited to {MAX_CLUSTERS:,} clusters.", high.span)
    return ClusterCandidatesIR(analysis, low.value, high.value, size.value)


def _cluster_sizes(arguments: dict[str, LocatedValue], span: Span) -> ClusterCandidatesIR:
    analysis = _cluster_analysis(arguments["analysis"], "cluster_sizes")
    low, high = arguments["min_size"], arguments["max_size"]
    if low.value < 1:
        fail("domain", "min_size must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_size must be at least min_size.", high.span)
    if high.value > MAX_CLUSTER_SIZE:
        fail(
            "domain",
            f"max_size is currently limited to {MAX_CLUSTER_SIZE:,} participants per cluster.",
            high.span,
        )
    return ClusterCandidatesIR(analysis, low.value, high.value)


def _candidates(arguments: dict[str, LocatedValue], span: Span) -> CandidatesIR:
    _not_clustered(arguments["analysis"])
    low, high = arguments["min_per_arm"], arguments["max_per_arm"]
    if low.value < 1:
        fail("domain", "min_per_arm must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_per_arm must be at least min_per_arm.", high.span)
    limit = _arm_limit(arguments["analysis"].value)
    if high.value > limit:
        fail("domain", f"max_per_arm is currently limited to {limit} for this analysis.", high.span)
    return CandidatesIR(arguments["analysis"].value, low.value, high.value)


def _one_arm(arguments: dict[str, LocatedValue], span: Span) -> OneArmModelIR:
    n = arguments["n"]
    if not 1 <= n.value <= MAX_ONE_ARM:
        fail("domain", f"n must be between 1 and {MAX_ONE_ARM}.", n.span)
    return OneArmModelIR(n.value)


def _binomial_test(arguments: dict[str, LocatedValue], span: Span) -> OneSampleAnalysisIR:
    rate = arguments["null_rate"]
    if not 0 < rate.value < 1:
        fail("domain", "null_rate must lie strictly between 0 and 1.", rate.span)
    return OneSampleAnalysisIR(arguments["model"].value, rate.value, arguments["alpha"].value)


def _responses(arguments: dict[str, LocatedValue], span: Span) -> OneSampleObservationIR:
    analysis, count = arguments["analysis"].value, arguments["count"]
    if not 0 <= count.value <= analysis.model.n:
        fail("domain", f"count must be between 0 and {analysis.model.n}.", count.span)
    return OneSampleObservationIR(analysis, count.value)


def _interval(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    model, count, level = arguments["model"], arguments["count"], arguments["level"]
    if not 0 <= count.value <= model.value.n:
        fail("domain", f"count must be between 0 and {model.value.n}.", count.span)
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    return ClaimIR(
        "interval",
        IntervalIR(model.value, count.value, level.value),
        model.name or "<expression>",
    )


def _difference_interval(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    model, level = arguments["model"], arguments["level"]
    check_design(model.value, BINOMIAL_ASSUMPTIONS, "difference_interval", model.span)
    for name, size in (
        ("control_successes", model.value.n_control),
        ("treatment_successes", model.value.n_treatment),
    ):
        if not 0 <= arguments[name].value <= size:
            fail("domain", f"{name} must be between 0 and {size}.", arguments[name].span)
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    interval = DifferenceIntervalIR(
        model.value,
        arguments["control_successes"].value,
        arguments["treatment_successes"].value,
        level.value,
    )
    try:
        interval.lower()
    except ValueError as error:
        fail("domain", str(error), level.span)
    return ClaimIR("interval", interval, model.name or "<expression>")


def _one_arm_candidates(arguments: dict[str, LocatedValue], span: Span) -> OneArmCandidatesIR:
    low, high = arguments["min_n"], arguments["max_n"]
    if low.value < 1:
        fail("domain", "min_n must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_n must be at least min_n.", high.span)
    if high.value > MAX_ONE_ARM:
        fail("domain", f"max_n is currently limited to {MAX_ONE_ARM}.", high.span)
    return OneArmCandidatesIR(arguments["analysis"].value, low.value, high.value)


def _allocated(arguments: dict[str, LocatedValue], span: Span) -> CandidatesIR:
    _not_clustered(arguments["analysis"])
    low, high = arguments["min_control"], arguments["max_control"]
    ratio = arguments["treatment_per_control"]
    if not 1 <= ratio.value <= MAX_RATIO:
        fail("domain", f"treatment_per_control must be between 1 and {MAX_RATIO}.", ratio.span)
    if low.value < 1:
        fail("domain", "min_control must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_control must be at least min_control.", high.span)
    limit = _arm_limit(arguments["analysis"].value)
    if high.value * ratio.value > limit:
        fail(
            "domain",
            f"The larger arm is currently limited to {limit} participants for this analysis.",
            high.span,
        )
    return CandidatesIR(arguments["analysis"].value, low.value, high.value, ratio.value)


def _sizing(minimal: bool) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        candidates = arguments["candidates"]
        goal = arguments["target"].value
        if isinstance(candidates.value, IntervalCandidatesIR) or isinstance(
            goal, PrecisionTargetIR
        ):
            if not isinstance(candidates.value, IntervalCandidatesIR):
                fail(
                    "type",
                    "precision_target is searched with interval_sizes(interval=...).",
                    candidates.span,
                )
            if minimal and getattr(goal, "assurance", None) is not None:
                fail(
                    "unsupported_claim",
                    "With an assurance, the chance of reaching the margin rises with the size "
                    "only roughly, since counts are whole numbers, so a smallest-size claim is "
                    "not offered. Use sample_size(...) for a sufficient size.",
                    candidates.span,
                )
            _check_precision(
                candidates.value.interval, arguments["target"], candidates.span, search=True
            )
            return ClaimIR(
                "sample_size",
                SizingIR(candidates.value, goal, minimal),
                candidates.name or "<expression>",
            )
        if (
            minimal
            and isinstance(candidates.value, CandidatesIR)
            and isinstance(candidates.value.analysis, AnalysisIR)
            and candidates.value.analysis.alternative == "margin"
        ):
            fail(
                "unsupported_claim",
                "Each sample size has its own critical value for this test, so a "
                "smallest-size claim is not supported. Use sample_size(...) to certify a "
                "sufficient design.",
                candidates.span,
            )
        if (
            minimal
            and isinstance(candidates.value, TotalCandidatesIR)
            and isinstance(candidates.value.analysis, AssociationAnalysisIR)
        ):
            fail(
                "unsupported_claim",
                "With only the total fixed, each candidate's check covers every number "
                "exposed, so a smallest-size claim is not supported. Use sample_size(...) to "
                "certify a sufficient total.",
                candidates.span,
            )
        if minimal and isinstance(candidates.value, TwoStageCandidatesIR):
            fail(
                "unsupported_claim",
                "A two-stage search ranks designs by its criterion; that ranking is a "
                "calculation and is not certified. Use sample_size(...) to certify the "
                "selected design's error and power.",
                candidates.span,
            )
        _check_point(candidates.value.analysis, arguments["target"], candidates.span)
        point = arguments["target"].value.at
        if isinstance(point, IncidenceRatesIR) and point.events is not None:
            fail(
                "planning_point",
                "event_counts searches the total number of events; leave events out of "
                "incidence_rates.",
                arguments["target"].span,
            )
        if isinstance(arguments["target"].value.at, HazardRatioIR):
            fail(
                "unsupported_claim",
                "At hazard_ratio(...), log-rank power depends on the number of events, not on "
                "the arm sizes, so a search over arm sizes does not apply. Plan at "
                "exponential_survival(...), whose times give the events each size expects, or "
                "calculate meets(...) for a number of events.",
                arguments["target"].span,
            )
        return ClaimIR(
            "sample_size",
            SizingIR(candidates.value, arguments["target"].value, minimal),
            candidates.name or "<expression>",
        )

    return build


def _two_stage_model(arguments: dict[str, LocatedValue], span: Span) -> TwoStageModelIR:
    for name, argument in arguments.items():
        if not 1 <= argument.value <= MAX_STAGE:
            fail("domain", f"{name} must be between 1 and {MAX_STAGE}.", argument.span)
    return TwoStageModelIR(arguments["n_stage1"].value, arguments["n_stage2"].value)


def _threshold_rule(arguments: dict[str, LocatedValue], span: Span) -> RuleIR:
    for name, argument in arguments.items():
        if argument.value < 0:
            fail("domain", f"{name} must be a nonnegative integer.", argument.span)
    return RuleIR(
        TwoStageRule(
            "threshold", arguments["continue_above"].value, arguments["reject_above"].value
        )
    )


def _prior(arguments: dict[str, LocatedValue], span: Span) -> PriorIR:
    for name, argument in arguments.items():
        if argument.value < 1:
            fail(
                "domain",
                f"{name} must be a positive integer; "
                "the exact posterior rule currently supports integer Beta parameters.",
                argument.span,
            )
    return PriorIR(arguments["a"].value, arguments["b"].value)


def _posterior_rule(arguments: dict[str, LocatedValue], span: Span) -> RuleIR:
    reference = arguments["reference"]
    if not 0 < reference.value < 1:
        fail("domain", "reference must lie strictly between 0 and 1.", reference.span)
    prior = arguments["prior"].value
    return RuleIR(
        TwoStageRule(
            "posterior",
            prior_a=prior.a,
            prior_b=prior.b,
            reference=reference.value,
            continue_at_least=arguments["continue_at_least"].value,
            success_at_least=arguments["success_at_least"].value,
        )
    )


def _two_stage_candidates(arguments: dict[str, LocatedValue], span: Span) -> TwoStageCandidatesIR:
    rate, total, criterion = arguments["null_rate"], arguments["max_total"], arguments["criterion"]
    if not 0 < rate.value < 1:
        fail("domain", "null_rate must lie strictly between 0 and 1.", rate.span)
    if not 2 <= total.value <= MAX_SEARCH_TOTAL:
        fail("domain", f"max_total must be between 2 and {MAX_SEARCH_TOTAL}.", total.span)
    if criterion.value not in CRITERIA:
        fail("domain", 'criterion must be "optimal" or "minimax".', criterion.span)
    return TwoStageCandidatesIR(rate.value, total.value, criterion.value)


def _stage_data(completed: bool) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> TwoStageObservationIR:
        analysis, first = arguments["analysis"].value, arguments["stage1_responses"]
        second = arguments["stage2_responses"] if completed else None
        for argument, size in (
            (first, analysis.design.n_stage1),
            (second, analysis.design.n_stage2),
        ):
            if argument is not None and not 0 <= argument.value <= size:
                fail("domain", f"Responses must be between 0 and {size}.", argument.span)
        observation = TwoStageObservationIR(
            analysis, first.value, second.value if second is not None else None
        )
        try:
            observation.lower()
        except ValueError as error:
            # The data must be what the declared rule would have produced.
            fail("rule_mismatch", str(error), first.span)
        return observation

    return build


def _two_stage_test(arguments: dict[str, LocatedValue], span: Span) -> TwoStageAnalysisIR:
    return TwoStageAnalysisIR(
        arguments["design"].value,
        arguments["rule"].value,
        _probability(arguments["null_rate"], "null_rate"),
    )
