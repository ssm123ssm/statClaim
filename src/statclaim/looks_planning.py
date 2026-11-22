"""Exact power of a design whose interim looks are Fisher's test: a calculation.

Each look's rejection region is the exact one StatClaim proves for a single Fisher test.
The chance of reaching each look with each pair of counts, not rejected before, is carried
from look to look by adding each stage's binomial increments, so every path of counts
through the looks is summed once. Nothing is simulated: the power, the chance of stopping at
each look and the expected size are exact sums, in floating point. The design's Type I bound
is proved by Lean; the exact rejection rate with both arms at the control rate is reported
beside it.
"""

import math
from fractions import Fraction

from statclaim.fisher import fraction_record
from statclaim.language import FeasibilityIR, SequentialIR, planned_analysis
from statclaim.planning import fisher_rejection_region
from statclaim.report import planning_report

MAX_LOOK_ARM = 300  # participants per arm at the last look: the sum stays within seconds
EXACT_LOOKS = (
    "Power, the chance of stopping at each look and the expected size are summed exactly over "
    "every path of counts through the looks, each look with the exact rejection region of "
    "Fisher's test at its own level. The sum is in floating point. The planning rates are "
    "inputs, not facts."
)


def _binomial(n: int, rate: float) -> list[float]:
    """P(K = k) for K binomial(n, rate), k from 0 to n."""
    if rate <= 0.0 or rate >= 1.0:
        return [1.0 if k == (0 if rate <= 0.0 else n) else 0.0 for k in range(n + 1)]
    log_rate, log_rest, base = math.log(rate), math.log1p(-rate), math.lgamma(n + 1)
    return [
        math.exp(
            base - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * log_rate + (n - k) * log_rest
        )
        for k in range(n + 1)
    ]


def _grow(mass: list[list[float]], steps_c: list[float], steps_t: list[float]):
    """Add one stage's responders to each arm: convolve the counts along each arm in turn."""
    rows, cols = len(mass), len(mass[0])
    wide = [[0.0] * cols for _ in range(rows + len(steps_c) - 1)]
    for x, row in enumerate(mass):
        for a, weight in enumerate(steps_c):
            if weight == 0.0:
                continue
            target = wide[x + a]
            for y, value in enumerate(row):
                if value:
                    target[y] += value * weight
    grown = []
    for row in wide:
        new = [0.0] * (cols + len(steps_t) - 1)
        for y, value in enumerate(row):
            if value:
                for b, weight in enumerate(steps_t):
                    new[y + b] += value * weight
        grown.append(new)
    return grown


def fisher_looks(looks: list[tuple[int, int, Fraction, str]], p_control: float, p_treatment: float):
    """The chance of stopping at each look. `looks` lists each look's cumulative arm sizes,
    its level and its alternative ("two_sided" or "greater")."""
    sizes = (0, 0)
    mass = [[1.0]]
    stopped = []
    for n_c, n_t, level, alternative in looks:
        mass = _grow(
            mass, _binomial(n_c - sizes[0], p_control), _binomial(n_t - sizes[1], p_treatment)
        )
        region = fisher_rejection_region(n_c, n_t, level, alternative)
        rejected = 0.0
        for x, row in enumerate(mass):
            for y, value in enumerate(row):
                if value and region[x][y]:
                    rejected += value
                    row[y] = 0.0
        stopped.append(rejected)
        sizes = (n_c, n_t)
    return stopped


def _looks(design: SequentialIR) -> list[tuple[int, int, Fraction, str]]:
    return [
        (look.plan.model.n_control, look.plan.model.n_treatment, look.alpha, look.alternative)
        for _, look in design.analyses
    ]


def _record(value: float) -> dict:
    rounded = Fraction(f"{value:.6f}")
    return {"fraction": str(rounded), "decimal_approximation": f"{value:.6f}"}


def _expected(looks, stopped: list[float]) -> float:
    totals = [n_c + n_t for n_c, n_t, _, _ in looks]
    return (
        sum(p * total for p, total in zip(stopped, totals, strict=True))
        + (1.0 - sum(stopped)) * totals[-1]
    )


def evaluate(design: SequentialIR, target) -> dict:
    looks, point = _looks(design), target.at
    control, treatment = float(point.p_control), float(point.p_treatment)
    stopped = fisher_looks(looks, control, treatment)
    null = fisher_looks(looks, control, control)
    power = min(sum(stopped), 1.0)
    n_c, n_t = looks[-1][:2]
    return {
        "n_control": n_c,
        "n_treatment": n_t,
        "total_sample_size": n_c + n_t,
        "looks": [
            {
                "n_control": c,
                "n_treatment": t,
                "alpha": fraction_record(level),
                "stop": _record(stop),
                "stop_null": _record(stop_null),
            }
            for (c, t, level, _), stop, stop_null in zip(looks, stopped, null, strict=True)
        ],
        "expected_sample_size": _record(_expected(looks, stopped)),
        "expected_sample_size_null": _record(_expected(looks, null)),
        "power": _record(power),
        "minimum_power": fraction_record(target.minimum),
        "power_target_met": power >= target.minimum,
        "typeI_at_control_rate": _record(sum(null)),
        "alpha": fraction_record(design.alpha),
        "maximum_typeI": fraction_record(target.maximum_typeI),
        "typeI_target_met": design.alpha <= target.maximum_typeI,
        "approximation": "sum over every path of counts through the looks",
    }


def describe(subject) -> dict:
    design, target = planned_analysis(subject), subject.target
    looks = ", ".join(
        f"({look.plan.model.n_control}, {look.plan.model.n_treatment}) at {look.alpha}"
        for _, look in design.analyses
    )
    text = (
        f"Fisher's test at {len(design.analyses)} looks, with cumulative arm sizes and levels "
        f"{looks}, stopping at the first rejection: power at least {target.minimum} at "
        f"response rates {target.at.p_control} and {target.at.p_treatment}, and the design's "
        f"level {design.alpha} at most {target.maximum_typeI}. Power is summed exactly over "
        "every path of counts through the looks; it is calculated, not checked by Lean."
    )
    return planning_report("looks_planning", text, [EXACT_LOOKS])


def run(report: dict, subject) -> dict:
    if not isinstance(subject, FeasibilityIR):
        raise ValueError("a design with looks is calculated as declared")
    design, target = planned_analysis(subject), subject.target
    calculation = evaluate(design, target)
    report["calculation"] = calculation
    met = calculation["power_target_met"] and calculation["typeI_target_met"]
    report["decision"] = "target_met" if met else "target_not_met"
    return report
