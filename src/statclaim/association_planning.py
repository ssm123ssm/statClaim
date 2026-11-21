"""Power for cited tests of observational studies: a calculation, never evidence.

The formula comes from the method's registry entry (methods/association_power.py). Power
is in the number of participants n, with the covariates the analysis adjusts for. A
search of totals is by bisection, since power rises with n.
"""

from fractions import Fraction

from statclaim.fisher import fraction_record
from statclaim.language import (
    CitedAssociationIR,
    CorrelationIR,
    FeasibilityIR,
    PowerTargetIR,
    planned_analysis,
)
from statclaim.methods.core import PowerResult
from statclaim.methods.identify import identify, mark
from statclaim.report import planning_report

PLANNING_POINT = "The planning point is an input for planning, not an established fact."


def _values(point) -> dict[str, float]:
    if isinstance(point, CorrelationIR):
        return {"value": float(point.value)}
    values = {
        "value": float(point.value),
        "exposure_sd": float(point.exposure_sd),
        "residual_sd": float(point.residual_sd),
    }
    if point.exposure_r2 is not None:
        values["exposure_r2"] = float(point.exposure_r2)
    return values


def describe_point(point) -> str:
    if isinstance(point, CorrelationIR):
        return f"a correlation of {point.value}"
    explained = (
        f", the covariates explaining {point.exposure_r2} of the exposure's variance"
        if point.exposure_r2 is not None
        else ""
    )
    return (
        f"a slope of {point.value} per unit of exposure, with exposure SD {point.exposure_sd} "
        f"and residual SD {point.residual_sd}{explained}"
    )


def power_at(analysis: CitedAssociationIR, point, n: int) -> PowerResult:
    return analysis.method.power.function(
        _values(point), n, len(analysis.covariates), float(analysis.alpha)
    )


def _record(value: float) -> dict:
    """A rounded decimal: exact as written, but only an approximation of the formula's value."""
    rounded = Fraction(f"{value:.6f}")
    return {"fraction": str(rounded), "decimal_approximation": f"{value:.6f}"}


def evaluate(analysis: CitedAssociationIR, target: PowerTargetIR, n: int) -> dict:
    result = power_at(analysis, target.at, n)
    formula = analysis.method.power
    k = len(analysis.covariates)
    return {
        "total_sample_size": n,
        "covariates": k,
        "degrees_of_freedom": n - k - 2,
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


def assumptions(analysis: CitedAssociationIR) -> list[dict]:
    """The test's own assumptions, then the formula's, then the planning point's."""
    items = [mark(item) for item in (*analysis.assumptions, *analysis.method.power.assumptions)]
    return [*items, identify(PLANNING_POINT)]


def describe(subject) -> dict:
    """The planning claim before calculation: what will be computed and what it rests on."""
    analysis, target = planned_analysis(subject), subject.target
    method, formula = analysis.method, analysis.method.power
    goal = (
        f"power at least {target.minimum} at {describe_point(target.at)}, and the test's level "
        f"{analysis.alpha} at most {target.maximum_typeI}"
    )
    adjusted = (
        f", adjusted for {len(analysis.covariates)} covariates" if analysis.covariates else ""
    )
    if isinstance(subject, FeasibilityIR):
        n = analysis.plan.model.total
        text = f"{method.title}{adjusted}, with {n} participants: {goal}."
    else:
        candidates = subject.candidates
        text = (
            f"{method.title}{adjusted}: the first total from {candidates.min_n} to "
            f"{candidates.max_n} participants with {goal}."
        )
    text += f" Power is a {formula.approximation}."
    listed = assumptions(analysis)
    report = planning_report("cited_planning", text, [item["text"] for item in listed])
    report["method"] = method.to_dict()
    report["formula"] = formula.to_dict()
    report["assumptions"] = listed
    report["references"] = [*method.references, *formula.references]
    return report


def run(report: dict, subject) -> dict:
    """Calculate power, or find the first total in the range that reaches the target."""
    analysis, target = planned_analysis(subject), subject.target
    if isinstance(subject, FeasibilityIR):
        calculation = evaluate(analysis, target, analysis.plan.model.total)
        report["calculation"] = calculation
        met = calculation["power_target_met"] and calculation["typeI_target_met"]
        report["decision"] = "target_met" if met else "target_not_met"
        return report
    candidates = subject.candidates
    search = {"min_n": candidates.min_n, "max_n": candidates.max_n}
    low, high = candidates.min_n, candidates.max_n
    evaluated = 0

    def enough(n: int) -> bool:
        nonlocal evaluated
        evaluated += 1
        return power_at(analysis, target.at, n).power >= target.minimum

    if not enough(high):
        report["calculation"] = {
            **search,
            "candidates_evaluated": evaluated,
            "power_target_met": False,
            "approximation": analysis.method.power.approximation,
        }
        report["decision"] = "no_feasible_candidate"
        return report
    # Power rises with n, so the first total that is enough lies in (low - 1, high].
    below = low - 1
    while high - below > 1:
        middle = (below + high) // 2
        if enough(middle):
            high = middle
        else:
            below = middle
    calculation = evaluate(analysis, target, high)
    report["calculation"] = {**calculation, **search, "candidates_evaluated": evaluated}
    report["decision"] = "target_met" if calculation["typeI_target_met"] else "target_not_met"
    return report
