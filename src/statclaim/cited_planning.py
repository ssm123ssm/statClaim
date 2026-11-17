"""Approximate power for cited tests: a calculation, never evidence and never a bound.

The formula comes from the method's registry entry (methods/power.py). This module
only reads the declaration, calls the formula and reports what it rests on.
"""

from fractions import Fraction

from statclaim.fisher import fraction_record
from statclaim.language import (
    CitedAnalysisIR,
    FeasibilityIR,
    HazardRatioIR,
    MeanDifferenceIR,
    PowerTargetIR,
    RatesIR,
    planned_analysis,
)
from statclaim.methods import NULL_FORMS
from statclaim.methods.core import PowerResult
from statclaim.methods.identify import identify, mark
from statclaim.report import planning_report

APPROXIMATE = "normal approximation, not a bound"
PLANNING_POINT = "The planning point is an input for planning, not an established fact."


def _values(point) -> dict[str, float]:
    if isinstance(point, MeanDifferenceIR):
        return {"value": float(point.value), "sd": float(point.sd)}
    if isinstance(point, RatesIR):
        return {"p_control": float(point.p_control), "p_treatment": float(point.p_treatment)}
    return {"value": float(point.value), "events": float(point.events)}


def describe_point(point) -> str:
    if isinstance(point, MeanDifferenceIR):
        return f"a mean difference of {point.value} with standard deviation {point.sd}"
    if isinstance(point, HazardRatioIR):
        return f"a hazard ratio of {point.value} with {point.events} events"
    return f"p_control = {point.p_control}, p_treatment = {point.p_treatment}"


def approximate_power(analysis: CitedAnalysisIR, point, n_control: int, n_treatment: int):
    null = analysis.hypothesis
    return analysis.method.power.function(
        _values(point),
        n_control,
        n_treatment,
        float(null.value),
        float(analysis.alpha),
        NULL_FORMS[null.predicate][1].one_sided,
    )


def _record(value: float) -> dict:
    """A rounded decimal: exact as written, but only an approximation of the formula's value."""
    rounded = Fraction(f"{value:.6f}")
    return {"fraction": str(rounded), "decimal_approximation": f"{value:.6f}"}


def evaluate(analysis: CitedAnalysisIR, target: PowerTargetIR, sizes: tuple[int, int]) -> dict:
    n_control, n_treatment = sizes
    result: PowerResult = approximate_power(analysis, target.at, n_control, n_treatment)
    formula = analysis.method.power
    return {
        "n_control": n_control,
        "n_treatment": n_treatment,
        "total_sample_size": n_control + n_treatment,
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
        "approximation": APPROXIMATE,
    }


def assumptions(analysis: CitedAnalysisIR) -> list[dict]:
    """The test's own assumptions, then the formula's, then the planning point's."""
    method = analysis.method
    items = [mark(item) for item in (*method.assumptions, *method.power.assumptions)]
    return [*items, identify(PLANNING_POINT)]


def describe(subject) -> dict:
    """The planning claim before calculation: what will be computed and what it rests on."""
    analysis, target = planned_analysis(subject), subject.target
    method = analysis.method
    point = describe_point(target.at)
    goal = (
        f"power at least {target.minimum} at {point}, and the test's level {analysis.alpha} "
        f"at most {target.maximum_typeI}"
    )
    if isinstance(subject, FeasibilityIR):
        model = analysis.plan.model
        text = f"{method.title} with arm sizes ({model.n_control}, {model.n_treatment}): {goal}."
    else:
        candidates = subject.candidates
        allocation = "equal-arm" if candidates.ratio == 1 else f"1:{candidates.ratio} allocation"
        text = (
            f"{method.title}: the first {allocation} size from {candidates.min_per_arm} to "
            f"{candidates.max_per_arm} controls with {goal}."
        )
    text += f" Power is a {APPROXIMATE}."
    listed = assumptions(analysis)
    report = planning_report("cited_planning", text, [item["text"] for item in listed])
    report["method"] = method.to_dict()
    report["formula"] = method.power.to_dict()
    report["assumptions"] = listed
    report["references"] = [*method.references, *method.power.references]
    return report


def run(report: dict, subject) -> dict:
    """Calculate approximate power, or search ascending for the first size that reaches it."""
    analysis, target = planned_analysis(subject), subject.target
    if isinstance(subject, FeasibilityIR):
        model = analysis.plan.model
        calculation = evaluate(analysis, target, (model.n_control, model.n_treatment))
        met = calculation["power_target_met"] and calculation["typeI_target_met"]
        report["calculation"] = calculation
        report["decision"] = "target_met" if met else "target_not_met"
        return report
    candidates = subject.candidates
    search = {"min_per_arm": candidates.min_per_arm, "max_per_arm": candidates.max_per_arm}
    for evaluated, size in enumerate(range(candidates.min_per_arm, candidates.max_per_arm + 1), 1):
        sizes = (size, candidates.ratio * size)
        if approximate_power(analysis, target.at, *sizes).power >= target.minimum:
            calculation = evaluate(analysis, target, sizes)
            met = calculation["typeI_target_met"]
            report["calculation"] = {**calculation, **search, "candidates_evaluated": evaluated}
            report["decision"] = "target_met" if met else "target_not_met"
            return report
    report["calculation"] = {
        **search,
        "candidates_evaluated": candidates.max_per_arm - candidates.min_per_arm + 1,
        "power_target_met": False,
        "approximation": APPROXIMATE,
    }
    report["decision"] = "no_feasible_candidate"
    return report
