"""Precision targets for planned intervals: from the declaration to the calculation.

precision.py holds the numbers; this module reads the planned interval, its design and the
target, and reports the margin of error, the assurance and a search for a size. Without
an assurance the margin falls steadily as the size grows, so a search finds the smallest
size by bisection; with one, the chance rises only roughly, and the search finds a
sufficient size.
"""

from fractions import Fraction

from statclaim.fisher import fraction_record
from statclaim.language import (
    DiscordantPairsIR,
    FeasibilityIR,
    IncidenceRatesIR,
    ModelIR,
    ObservationalStudyIR,
    OneArmModelIR,
    PlannedIntervalIR,
    PrecisionTargetIR,
    RatesIR,
    group_probabilities,
    planned_analysis,
)
from statclaim.precision import INFINITE, MEASURES, Plan, assumptions
from statclaim.report import planning_report

LARGEST_EXACT_REPORT = 1000  # StatClaim reports exact intervals for up to this many per group


def kind_of(interval: PlannedIntervalIR) -> str:
    return MEASURES[interval.measure][0]


def _value_and_rates(interval: PlannedIntervalIR, point) -> tuple[float, tuple]:
    kind = kind_of(interval)
    if kind == "proportion":
        return float(point.value), (float(point.value),)
    if kind == "matched":
        share = point.odds_ratio / (1 + point.odds_ratio)
        return float(point.odds_ratio), (float(share),)
    if kind == "rate":
        exposed = point.exposed_time * point.rate_ratio
        share = exposed / (exposed + point.unexposed_time)
        return float(point.rate_ratio), (float(share),)
    if isinstance(point, RatesIR):
        first, second = point.p_control, point.p_treatment
    else:
        first, second = group_probabilities(point)
    if kind == "difference":
        value = second - first
    elif kind == "ratio":
        value = second / first
    else:
        value = (second / (1 - second)) / (first / (1 - first))
    return float(value), (float(first), float(second))


def plan(interval: PlannedIntervalIR, target: PrecisionTargetIR) -> Plan:
    point = target.at
    value, rates = _value_and_rates(interval, point)
    effect = getattr(point, "design_effect", None)
    population = getattr(point, "population_size", None)
    scale = 1.0
    if isinstance(point, IncidenceRatesIR):
        scale = float(point.unexposed_time / point.exposed_time)
    return Plan(
        kind_of(interval),
        interval.method,
        target.level,
        rates,
        value,
        scale=scale,
        share=float(point.share) if isinstance(point, DiscordantPairsIR) else None,
        effect=float(effect) if effect is not None else 1.0,
        population=population,
    )


def _two_fixed_groups(interval: PlannedIntervalIR) -> bool:
    model = interval.model
    return isinstance(model, ModelIR) or (
        isinstance(model, ObservationalStudyIR)
        and model.groups is not None
        and kind_of(interval) in ("difference", "ratio", "odds")
    )


def declared_size(interval: PlannedIntervalIR, target: PrecisionTargetIR):
    """The declared study's size in this interval's terms."""
    model, kind = interval.model, kind_of(interval)
    if isinstance(model, OneArmModelIR):
        return model.n
    if isinstance(model, ModelIR):
        return (model.n_control, model.n_treatment)
    if kind == "matched":
        return model.pairs
    if kind == "rate":
        return target.at.events
    if kind == "proportion":
        if model.groups is not None:
            unexposed, exposed = model.groups
            return exposed if interval.group == "exposed" else unexposed
        return model.total
    return model.groups if model.groups is not None else model.total


def size_of(interval: PlannedIntervalIR, ratio: int):
    """A search's size for index m: one group, or the first group with ratio of the other."""
    model = interval.model
    if isinstance(model, ModelIR):
        return lambda m: (m, ratio * m)  # m controls, ratio treated for each
    if _two_fixed_groups(interval):
        return lambda m: (ratio * m, m)  # m exposed or cases, ratio of the others for each
    return lambda m: m


def group_sizes(interval: PlannedIntervalIR, target: PrecisionTargetIR, size) -> tuple:
    """The sizes the plan takes: one group, or (reference, other); for a design that fixes
    only its total, the expected numbers unexposed and exposed."""
    if isinstance(size, tuple):
        return size
    if kind_of(interval) in ("difference", "ratio", "odds"):
        share = float(target.at.exposed_share)
        return (size * (1 - share), size * share)
    return (size,)


def _record(value: float) -> dict | None:
    if value == INFINITE:
        return None
    rounded = Fraction(f"{value:.6f}")
    return {"fraction": str(rounded), "decimal_approximation": f"{value:.6f}"}


def _sizes_record(interval: PlannedIntervalIR, size) -> dict:
    model, kind = interval.model, kind_of(interval)
    if kind == "matched":
        return {"pairs": size}
    if kind == "rate":
        return {"events": size}
    if isinstance(size, tuple):
        first, second = size
        if isinstance(model, ModelIR):
            names = ("n_control", "n_treatment")
        elif model.design == "case_control":
            names = ("controls", "cases")
        else:
            names = ("unexposed", "exposed")
        return {names[0]: first, names[1]: second, "total_sample_size": first + second}
    return {"total_sample_size": size}


def evaluate(interval: PlannedIntervalIR, target: PrecisionTargetIR, size) -> dict:
    """The margin at the expected counts, and when asked, the assurance; met or not."""
    planned = plan(interval, target)
    sizes = group_sizes(interval, target, size)
    relative = target.relative is not None
    bound = float(target.bound)
    bounds, _ = planned.expected(sizes)
    achieved = planned.margin(bounds, relative)
    record = {
        **_sizes_record(interval, size),
        "measure": interval.measure,
        "method": interval.method,
        "level": fraction_record(target.level),
        "estimate": _record(planned.value),
        "lower": _record(bounds[0]),
        "upper": _record(bounds[1]),
        "relative": relative,
        "margin_achieved": _record(achieved),
        "target_margin": fraction_record(target.bound),
    }
    met = achieved <= bound + 1e-12
    if target.assurance is not None:
        chance = planned.assurance(sizes, relative, bound)
        record["assurance"] = _record(chance)
        record["minimum_assurance"] = fraction_record(target.assurance)
        met = chance >= float(target.assurance)
    record["precision_target_met"] = met
    return record


def _largest_group(size) -> int:
    return int(max(size)) if isinstance(size, tuple) else int(size)


def describe(subject) -> dict:
    """The precision claim before calculation: what will be computed and what it rests on."""
    interval, target = planned_analysis(subject), subject.target
    words = interval.measure.replace("_", " ")
    goal = (
        f"a margin of error at most {target.margin}"
        if target.margin is not None
        else f"a relative margin of error at most {target.relative}"
    )
    chance = (
        f", with probability at least {target.assurance}"
        if target.assurance is not None
        else ", at the counts the planning point expects"
    )
    method = "StatClaim's exact" if interval.method == "exact" else "the normal"
    if isinstance(subject, FeasibilityIR):
        text = (
            f"Does {method} {target.level} interval for the {words}, as declared, have "
            f"{goal}{chance}?"
        )
    else:
        candidates = subject.candidates
        smallest = "smallest" if target.assurance is None else "a sufficient"
        text = (
            f"The {smallest} size from {candidates.min_size} to {candidates.max_size} for which "
            f"{method} {target.level} interval for the {words} has {goal}{chance}."
        )
    total_only = (
        target.assurance is not None
        and isinstance(interval.model, ObservationalStudyIR)
        and interval.model.groups is None
        and kind_of(interval) in ("difference", "ratio", "odds")
    )
    listed = list(assumptions(interval.method, total_only))
    report = planning_report("precision", text + " A calculation, not checked by Lean.", listed)
    # The planning point's is a condition; the others are the calculation's assumptions.
    report["assumptions"] = [
        {
            "id": f"precision_{index + 1}",
            "kind": "scope" if text_ == listed[-1] else "approximation",
            "text": text_,
            "status": "condition" if text_ == listed[-1] else "assumed",
        }
        for index, text_ in enumerate(listed)
    ]
    return report


def run(report: dict, subject) -> dict:
    """Calculate the precision of the declared study, or search for a size."""
    interval, target = planned_analysis(subject), subject.target
    if isinstance(subject, FeasibilityIR):
        size = declared_size(interval, target)
        calculation = evaluate(interval, target, size)
        report["calculation"] = calculation
        report["decision"] = (
            "target_met" if calculation["precision_target_met"] else "target_not_met"
        )
        _note_reporting(report, interval, size)
        return report
    candidates = subject.candidates
    size_for = size_of(interval, candidates.ratio)
    low, high = candidates.min_size, candidates.max_size
    search = {"min_size": low, "max_size": high, "ratio": candidates.ratio}
    evaluated = 0

    def enough(m: int) -> bool:
        nonlocal evaluated
        evaluated += 1
        return evaluate(interval, target, size_for(m))["precision_target_met"]

    if not enough(high):
        report["calculation"] = {
            **search,
            "candidates_evaluated": evaluated,
            "precision_target_met": False,
        }
        report["decision"] = "no_feasible_candidate"
        return report
    below = low - 1
    while high - below > 1:
        middle = (below + high) // 2
        if enough(middle):
            high = middle
        else:
            below = middle
    calculation = evaluate(interval, target, size_for(high))
    report["calculation"] = {**calculation, **search, "candidates_evaluated": evaluated}
    report["decision"] = "target_met"
    _note_reporting(report, interval, size_for(high))
    return report


def _note_reporting(report: dict, interval: PlannedIntervalIR, size) -> None:
    """Say so when StatClaim could not compute the planned exact interval for the results."""
    if interval.method == "exact" and _largest_group(size) > LARGEST_EXACT_REPORT:
        report["calculation"]["note"] = (
            f"StatClaim computes exact intervals for results of up to {LARGEST_EXACT_REPORT} per "
            "group; the plan holds for the Clopper-Pearson interval, which can be computed "
            "elsewhere for larger groups."
        )
