"""Power for cited tests of observational studies: a calculation, never evidence.

The formula comes from the method's registry entry (methods/association_power.py) and is
chosen by the planning point and the study's exposure scale. Power is in the study's own
units: participants, the two groups a cohort or case-control study fixes, matched pairs, or
events. A search is by bisection, since power rises with the size.
"""

from fractions import Fraction

from statclaim.fisher import fraction_record
from statclaim.language import (
    CitedAssociationIR,
    CorrelationIR,
    CountCandidatesIR,
    DiscordantPairsIR,
    FeasibilityIR,
    GroupCandidatesIR,
    IncidenceRatesIR,
    MatchedStudyIR,
    OddsPerSdIR,
    PersonTimeStudyIR,
    PowerTargetIR,
    SlopeIR,
    group_probabilities,
    observational_formula,
    planned_analysis,
)
from statclaim.methods.identify import identify, mark
from statclaim.observational_planning import SEARCH_KEYS
from statclaim.report import planning_report

PLANNING_POINT = "The planning point is an input for planning, not an established fact."


def _r2(point) -> dict:
    share = getattr(point, "exposure_r2", None)
    return {} if share is None else {"exposure_r2": float(share)}


def inputs(analysis: CitedAssociationIR, point, size) -> tuple[dict, float]:
    """The formula's arguments and size for one design. `size` is the total, or for a study
    that fixes two groups, (reference group, other group): (unexposed, exposed) or
    (controls, cases), or the pairs or events."""
    if isinstance(point, CorrelationIR):
        return {"value": float(point.value)}, size
    if isinstance(point, SlopeIR):
        values = {
            "value": float(point.value),
            "exposure_sd": float(point.exposure_sd),
            "residual_sd": float(point.residual_sd),
        }
        return {**values, **_r2(point)}, size
    if isinstance(point, OddsPerSdIR):
        return {
            "value": float(point.odds_ratio),
            "baseline": float(point.baseline),
            **_r2(point),
        }, size
    if isinstance(point, DiscordantPairsIR):
        return {"share": float(point.share), "odds_ratio": float(point.odds_ratio)}, size
    if isinstance(point, IncidenceRatesIR):
        share = point.exposed_time / (point.exposed_time + point.unexposed_time)
        return {"rate_ratio": float(point.rate_ratio), "exposed_share": float(share)}, size
    first, second = group_probabilities(point)
    values = {"p_reference": float(first), "p_other": float(second)}
    if isinstance(size, tuple):
        reference, other = size
        return {**values, "share_other": other / (reference + other)}, reference + other
    return {**values, "share_other": float(point.exposed_share)}, size


def power_at(analysis: CitedAssociationIR, point, size):
    values, n = inputs(analysis, point, size)
    formula = observational_formula(analysis, point)
    return formula.function(values, n, len(analysis.covariates), float(analysis.alpha))


def describe_point(point) -> str:
    if isinstance(point, CorrelationIR):
        return f"a correlation of {point.value}"
    if isinstance(point, OddsPerSdIR):
        return (
            f"an odds ratio of {point.odds_ratio} per standard deviation of the exposure, with "
            f"the outcome's probability {point.baseline} at its mean"
        )
    if isinstance(point, SlopeIR):
        explained = (
            f", the covariates explaining {point.exposure_r2} of the exposure's variance"
            if point.exposure_r2 is not None
            else ""
        )
        return (
            f"a slope of {point.value} per unit of exposure, with exposure SD "
            f"{point.exposure_sd} and residual SD {point.residual_sd}{explained}"
        )
    if isinstance(point, DiscordantPairsIR):
        return (
            f"{point.share} of pairs discordant and a conditional odds ratio of {point.odds_ratio}"
        )
    if isinstance(point, IncidenceRatesIR):
        return f"a rate ratio of {point.rate_ratio}"
    first, second = group_probabilities(point)
    return f"probabilities {first} and {second} in the two groups"


def _record(value: float) -> dict:
    """A rounded decimal: exact as written, but only an approximation of the formula's value."""
    rounded = Fraction(f"{value:.6f}")
    return {"fraction": str(rounded), "decimal_approximation": f"{value:.6f}"}


def _sizes(analysis: CitedAssociationIR, point, size) -> dict:
    """The design's sizes, in its own units."""
    model = analysis.plan.model
    if isinstance(model, MatchedStudyIR):
        return {"pairs": size}
    if isinstance(model, PersonTimeStudyIR):
        return {"events": size}
    if isinstance(size, tuple):
        reference, other = size
        names = (
            ("controls", "cases") if model.design == "case_control" else ("unexposed", "exposed")
        )
        return {names[0]: reference, names[1]: other, "total_sample_size": reference + other}
    record = {"total_sample_size": size, "covariates": len(analysis.covariates)}
    if isinstance(point, (CorrelationIR, SlopeIR)):
        record["degrees_of_freedom"] = size - len(analysis.covariates) - 2
    return record


def evaluate(analysis: CitedAssociationIR, target: PowerTargetIR, size) -> dict:
    result = power_at(analysis, target.at, size)
    formula = observational_formula(analysis, target.at)
    return {
        **_sizes(analysis, target.at, size),
        "power": _record(result.power),
        "minimum_power": fraction_record(target.minimum),
        "power_target_met": result.power >= target.minimum,
        "critical_estimate": _record(result.critical),
        "reject_when": result.direction,
        "standard_error": _record(result.standard_error),
        "alpha": fraction_record(analysis.alpha),
        "maximum_typeI": fraction_record(target.maximum_typeI),
        "typeI_target_met": analysis.alpha <= target.maximum_typeI,
        "formula": formula.key,
        "formula_version": formula.version,
        "approximation": formula.approximation,
    }


def assumptions(analysis: CitedAssociationIR, point) -> list[dict]:
    """The test's own assumptions, then the formula's, then the planning point's."""
    formula = observational_formula(analysis, point)
    items = [mark(item) for item in (*analysis.assumptions, *formula.assumptions)]
    return [*items, identify(PLANNING_POINT)]


def declared_size(analysis: CitedAssociationIR, point):
    """The declared study's size in the formula's units."""
    model = analysis.plan.model
    if isinstance(model, MatchedStudyIR):
        return model.pairs
    if isinstance(model, PersonTimeStudyIR):
        return point.events
    return model.groups if model.groups is not None else model.total


def candidates(space):
    """The search's sizes as a function of an index, and the index's bounds."""
    if isinstance(space, GroupCandidatesIR):
        return (lambda m: (space.ratio * m, m)), space.min_size, space.max_size
    if isinstance(space, CountCandidatesIR):
        return (lambda m: m), space.min_size, space.max_size
    return (lambda m: m), space.min_n, space.max_n


def _search_words(space) -> str:
    if isinstance(space, GroupCandidatesIR):
        noun = "cases" if space.analysis.plan.model.design == "case_control" else "exposed"
        each = f", {space.ratio} for each" if space.ratio != 1 else ""
        return f"from {space.min_size} to {space.max_size} {noun}{each}"
    if isinstance(space, CountCandidatesIR):
        return f"from {space.min_size} to {space.max_size} {space.unit}"
    return f"a total from {space.min_n} to {space.max_n} participants"


def describe(subject) -> dict:
    """The planning claim before calculation: what will be computed and what it rests on."""
    analysis, target = planned_analysis(subject), subject.target
    method = analysis.method
    formula = observational_formula(analysis, target.at)
    goal = (
        f"power at least {target.minimum} at {describe_point(target.at)}, and the test's level "
        f"{analysis.alpha} at most {target.maximum_typeI}"
    )
    adjusted = (
        f", adjusted for {len(analysis.covariates)} covariates" if analysis.covariates else ""
    )
    if isinstance(subject, FeasibilityIR):
        text = f"{method.title}{adjusted}, as declared: {goal}."
    else:
        words = _search_words(subject.candidates)
        text = f"{method.title}{adjusted}: the first size {words} with {goal}."
    text += f" Power is a {formula.approximation}."
    listed = assumptions(analysis, target.at)
    report = planning_report("cited_planning", text, [item["text"] for item in listed])
    report["method"] = method.to_dict()
    report["formula"] = formula.to_dict()
    report["assumptions"] = listed
    report["references"] = [*method.references, *formula.references]
    return report


def run(report: dict, subject) -> dict:
    """Calculate power, or find the first size in the range that reaches the target."""
    analysis, target = planned_analysis(subject), subject.target
    if isinstance(subject, FeasibilityIR):
        calculation = evaluate(analysis, target, declared_size(analysis, target.at))
        report["calculation"] = calculation
        met = calculation["power_target_met"] and calculation["typeI_target_met"]
        report["decision"] = "target_met" if met else "target_not_met"
        return report
    space = subject.candidates
    size_of, low, high = candidates(space)
    search = _bounds(space)
    evaluated = 0

    def enough(index: int) -> bool:
        nonlocal evaluated
        evaluated += 1
        return power_at(analysis, target.at, size_of(index)).power >= target.minimum

    if not enough(high):
        report["calculation"] = {
            **search,
            "candidates_evaluated": evaluated,
            "power_target_met": False,
            "approximation": observational_formula(analysis, target.at).approximation,
        }
        report["decision"] = "no_feasible_candidate"
        return report
    # Power rises with the size, so the first that is enough lies in (low - 1, high].
    below = low - 1
    while high - below > 1:
        middle = (below + high) // 2
        if enough(middle):
            high = middle
        else:
            below = middle
    calculation = evaluate(analysis, target, size_of(high))
    report["calculation"] = {**calculation, **search, "candidates_evaluated": evaluated}
    report["decision"] = "target_met" if calculation["typeI_target_met"] else "target_not_met"
    return report


def _bounds(space) -> dict:
    if isinstance(space, GroupCandidatesIR):
        low, high, ratio = SEARCH_KEYS[space.analysis.plan.model.design]
        return {low: space.min_size, high: space.max_size, ratio: space.ratio}
    if isinstance(space, CountCandidatesIR):
        return {f"min_{space.unit}": space.min_size, f"max_{space.unit}": space.max_size}
    return {"min_n": space.min_n, "max_n": space.max_n}
