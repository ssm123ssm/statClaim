"""Precision of planned intervals: the margin of error, and the chance of reaching it.

A precision target asks that an interval be narrow enough: its margin of error, half its
width, at most a value, or its relative margin of error at most a fraction of the planning
value. Without an assurance, the interval is taken at the counts the planning point
expects. With one, the chance that the interval turns out narrow enough must reach the
assurance; that chance is summed exactly over the possible counts.

The exact intervals are StatClaim's own: Clopper-Pearson, rounded outward to a grid of
1/10,000, combined for two groups as `DifferenceInterval` and `EffectInterval` combine
them. They are computed here in floating point, for every size. The normal intervals are
the usual large-sample ones, with a survey's design effect and a finite population
correction. Everything here is a calculation: Lean does not check precision.
"""

import math
from bisect import bisect_right
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from statistics import NormalDist

from statclaim.methods.t_distribution import beta_quantile

GRID = 10_000
_NORMAL = NormalDist()
_SLACK = 1e-12  # floating-point room when comparing a margin with its target
INFINITE = math.inf


def arm_level(level: Fraction) -> Fraction:
    """The level of each group's exact interval: the smallest four-decimal level whose
    square is at least the requested level, as `DifferenceInterval` uses."""
    target = level * GRID**2
    root = isqrt(target.numerator // target.denominator)
    while Fraction(root * root) < target:
        root += 1
    return Fraction(root, GRID)


@lru_cache(maxsize=200_000)
def exact_bounds(x: float, n: float, level: float) -> tuple[float, float]:
    """The Clopper-Pearson interval for x of n, rounded outward to the grid. x and n may be
    expected counts, which need not be whole numbers."""
    tail = (1 - level) / 2
    lower = 0.0 if x <= 0 else beta_quantile(tail, x, n - x + 1)
    upper = 1.0 if x >= n else beta_quantile(1 - tail, x + 1, n - x)
    return math.floor(lower * GRID) / GRID, math.ceil(upper * GRID) / GRID


def _odds(p: float) -> float:
    return p / (1 - p)


def _binomial(n: int, p: float):
    """(k, P(K = k)) for K binomial(n, p), over the counts that are not negligible."""
    if p <= 0:
        yield 0, 1.0
        return
    if p >= 1:
        yield n, 1.0
        return
    spread = math.sqrt(n * p * (1 - p))
    low, high = (
        max(0, math.floor(n * p - 10 * spread) - 1),
        min(n, math.ceil(n * p + 10 * spread) + 1),
    )
    log_p, log_q = math.log(p), math.log1p(-p)
    head = math.lgamma(n + 1)
    for k in range(low, high + 1):
        weight = math.exp(
            head - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * log_p + (n - k) * log_q
        )
        if weight > 0:
            yield k, weight


# Kinds of measure: how the interval is built from one or two groups' probabilities.
KINDS = ("proportion", "difference", "ratio", "odds", "matched", "rate")
# Each interval a study can plan: its kind, and the designs that estimate it.
MEASURES = {
    "response_rate": ("proportion", ("one_arm",)),
    "prevalence": ("proportion", ("cross_sectional",)),
    "cumulative_incidence": ("proportion", ("cohort",)),
    "difference": ("difference", ("two_arm",)),
    "risk_difference": ("difference", ("cohort",)),
    "prevalence_difference": ("difference", ("cross_sectional",)),
    "risk_ratio": ("ratio", ("cohort",)),
    "prevalence_ratio": ("ratio", ("cross_sectional",)),
    "odds_ratio": ("odds", ("cross_sectional", "cohort", "case_control")),
    "conditional_odds_ratio": ("matched", ("matched_case_control",)),
    "rate_ratio": ("rate", ("person_time_cohort",)),
}
METHODS = ("exact", "normal")
# What a precision calculation rests on, by method.
EXACT_ASSUMPTIONS = (
    "Counts are binomial: participants, pairs or events arise independently, with one "
    "probability in each group, as the planning point gives.",
    "The interval is StatClaim's exact interval: Clopper-Pearson, rounded outward to a grid of "
    "1/10,000; for two groups, each group's interval at a level whose square is at least the "
    "requested level.",
    "Precision is computed in floating point and is not checked by Lean; a margin within "
    "1e-12 of its target counts as reaching it.",
)
NORMAL_ASSUMPTIONS = (
    "The interval is the usual large-sample one: the estimate plus or minus z standard errors, "
    "on the log scale for a ratio, at the planning values. A normal approximation, not a bound.",
    "A survey's design effect and the size of the population sampled are planning inputs, "
    "not established facts.",
)
EXPECTED_GROUPS = (
    "When only the total is fixed, the assurance is computed at the expected numbers exposed "
    "and unexposed."
)
PLANNING_POINT = "The planning point is an input for planning, not an established fact."


def assumptions(method: str, total_only_assurance: bool) -> tuple[str, ...]:
    listed = EXACT_ASSUMPTIONS if method == "exact" else NORMAL_ASSUMPTIONS
    return (*listed, *((EXPECTED_GROUPS,) if total_only_assurance else ()), PLANNING_POINT)


# The largest size a search may reach: exact sums over matched pairs are the slowest.
MAX_SIZE = 100_000
MAX_EXACT_PAIRS = 10_000


def margin(kind: str, bounds: tuple[float, float], relative: bool, value: float) -> float:
    """The interval's margin in the target's terms. Absolute: half the width. Relative, for a
    proportion or a difference: half the width over the planning value. Relative, for a ratio:
    1 - e^(-h), with h half the width on the log scale, so that the lower limit is at least
    (1 - r) times the estimate."""
    lower, upper = bounds
    if math.isinf(upper):
        return INFINITE
    if not relative:
        return (upper - lower) / 2
    if kind in ("proportion", "difference"):
        return (upper - lower) / (2 * abs(value))
    if lower <= 0:
        return INFINITE
    return 1 - math.exp(-(math.log(upper) - math.log(lower)) / 2)


def _two_groups(kind: str, reference: tuple[float, float], other: tuple[float, float]):
    """An effect's interval from the two groups' intervals, as `EffectInterval` builds it."""
    (c_low, c_up), (t_low, t_up) = reference, other
    if kind == "difference":
        return t_low - c_up, t_up - c_low
    if kind == "ratio":
        return t_low / c_up, (t_up / c_low if c_low > 0 else INFINITE)
    lower = 0.0 if c_up >= 1 else _odds(t_low) / _odds(c_up)
    upper = _odds(t_up) / _odds(c_low) if c_low > 0 and t_up < 1 else INFINITE
    return lower, upper


def _normal_half(kind: str, rates, sizes, z: float, effect: float, population: float | None):
    """The normal interval's half width on its own scale: of the proportion or difference,
    or of the log ratio."""
    if kind == "proportion":
        (p,), (n,) = rates, sizes
        correction = (population - n) / (population - 1) if population else 1.0
        return z * math.sqrt(effect * p * (1 - p) / n * max(correction, 0.0))
    if kind == "difference":
        (p0, p1), (n0, n1) = rates, sizes
        return z * math.sqrt(effect * (p0 * (1 - p0) / n0 + p1 * (1 - p1) / n1))
    if kind == "ratio":
        (p0, p1), (n0, n1) = rates, sizes
        if p0 <= 0 or p1 <= 0:
            return INFINITE
        return z * math.sqrt(effect * ((1 - p1) / (n1 * p1) + (1 - p0) / (n0 * p0)))
    # Odds: 1 / a + 1 / b + 1 / c + 1 / d over the expected cells.
    (p0, p1), (n0, n1) = rates, sizes
    cells = (n1 * p1, n1 * (1 - p1), n0 * p0, n0 * (1 - p0))
    if min(cells) <= 0:
        return INFINITE
    return z * math.sqrt(effect * sum(1 / cell for cell in cells))


def normal_bounds(kind, rates, sizes, level, effect=1.0, population=None, estimate=None):
    """The normal interval: estimate +- half for a proportion or a difference, or
    estimate * e^(+-h) for a ratio."""
    z = _NORMAL.inv_cdf(1 - (1 - level) / 2)
    half = _normal_half(kind, rates, sizes, z, effect, population)
    if kind in ("proportion", "difference"):
        return estimate - half, estimate + half
    if math.isinf(half) or estimate <= 0:
        return 0.0, INFINITE
    return estimate * math.exp(-half), estimate * math.exp(half)


class Plan:
    """One planned interval in plain numbers.

    kind: a key of KINDS. method: "exact" or "normal". level: the interval's level.
    rates: the planning point's probabilities, (p,) for one group, (reference, other) for
    two, (P,) for a matched pair's chance that the case is the exposed one, or for a rate
    ratio the exposed share of events. value: the measure at the planning point, for a
    relative margin. scale: a rate ratio's unexposed over exposed person-time. share: a
    matched study's share of discordant pairs. effect, population: a survey's design effect
    and population size, for the normal method.
    """

    def __init__(
        self,
        kind,
        method,
        level,
        rates,
        value,
        *,
        scale=1.0,
        share=None,
        effect=1.0,
        population=None,
    ):
        self.kind, self.method, self.level = kind, method, level
        self.rates, self.value, self.scale, self.share = rates, value, scale, share
        self.effect, self.population = effect, population

    # Intervals at given counts -------------------------------------------------------------
    def interval(self, counts, sizes) -> tuple[float, float]:
        """The interval the study would report with these counts, which may be expected
        counts. counts and sizes are per group, in the order of rates."""
        level = float(self.level)
        if self.method == "normal":
            rates = tuple(x / n for x, n in zip(counts, sizes, strict=True))
            estimate = self._estimate(rates)
            if self.kind in ("matched", "rate"):
                # One binomial share: the log odds has variance 1 / x + 1 / (n - x).
                (x,), (n,) = counts, sizes
                if x <= 0 or x >= n:
                    return 0.0, INFINITE
                z = _NORMAL.inv_cdf(1 - (1 - level) / 2)
                h = z * math.sqrt(self.effect * (1 / x + 1 / (n - x)))
                return estimate * math.exp(-h), estimate * math.exp(h)
            return normal_bounds(
                self.kind, rates, sizes, level, self.effect, self.population, estimate
            )
        if self.kind == "proportion":
            return exact_bounds(counts[0], sizes[0], level)
        if self.kind in ("matched", "rate"):
            if sizes[0] <= 0:
                return 0.0, INFINITE
            low, up = exact_bounds(counts[0], sizes[0], level)
            factor = self.scale if self.kind == "rate" else 1.0
            lower = _odds(low) * factor if low < 1 else INFINITE
            upper = _odds(up) * factor if up < 1 else INFINITE
            return lower, upper
        each = float(arm_level(self.level))
        groups = [exact_bounds(x, n, each) for x, n in zip(counts, sizes, strict=True)]
        return _two_groups(self.kind, groups[0], groups[1])

    def _estimate(self, rates) -> float:
        if self.kind == "proportion":
            return rates[0]
        if self.kind == "difference":
            return rates[1] - rates[0]
        if self.kind == "ratio":
            return rates[1] / rates[0] if rates[0] > 0 else INFINITE
        if self.kind == "odds":
            p0, p1 = rates
            return _odds(p1) / _odds(p0) if 0 < p0 < 1 and p1 < 1 else INFINITE
        p = rates[0]
        return _odds(p) * (self.scale if self.kind == "rate" else 1.0) if p < 1 else INFINITE

    def margin(self, bounds, relative: bool) -> float:
        kind = "ratio" if self.kind in ("odds", "matched", "rate") else self.kind
        return margin(kind, bounds, relative, self.value)

    # The two criteria ----------------------------------------------------------------------
    def expected(self, sizes) -> tuple[tuple[float, float], tuple]:
        """The interval at the counts the planning point expects, and those sizes."""
        if self.kind == "matched":
            discordant = sizes[0] * self.share
            sizes = (discordant,)
        counts = tuple(n * p for n, p in zip(sizes, self.rates, strict=True))
        return self.interval(counts, sizes), sizes

    def assurance(self, sizes, relative: bool, target: float) -> float:
        """The chance that the margin is at most the target, summed over the counts."""
        bound = target + _SLACK

        def fits(counts, group_sizes):
            return self.margin(self.interval(counts, group_sizes), relative) <= bound

        if self.kind == "matched":
            total = 0.0
            for discordant, weight in _binomial(int(sizes[0]), self.share):
                inner = sum(
                    w for x, w in _binomial(discordant, self.rates[0]) if fits((x,), (discordant,))
                )
                total += weight * inner
            return total
        if len(sizes) == 1:
            n = int(sizes[0])
            return sum(w for x, w in _binomial(n, self.rates[0]) if fits((x,), (n,)))
        n0, n1 = (int(round(n)) for n in sizes)
        first = list(_binomial(n0, self.rates[0]))
        second = list(_binomial(n1, self.rates[1]))
        additive = self._additive(relative)
        if additive is None:
            return sum(w0 * w1 for x0, w0 in first for x1, w1 in second if fits((x0, x1), (n0, n1)))
        # The margin is a sum over the groups: sort one group's parts and add the other's.
        score, threshold = additive
        parts = sorted((score(0, x0, n0), w0) for x0, w0 in first)
        values = [part for part, _ in parts]
        cumulative, running = [], 0.0
        for _, weight in parts:
            running += weight
            cumulative.append(running)
        total = 0.0
        for x1, w1 in second:
            room = threshold(bound) - score(1, x1, n1)
            index = bisect_right(values, room + _SLACK)
            if index:
                total += w1 * cumulative[index - 1]
        return total

    def _additive(self, relative: bool):
        """When the margin is a sum of one part per group: (part(group, x, n), threshold
        on the sum for a target). None when it is not, as for a ratio's absolute margin."""
        level = float(self.level)
        if self.method == "exact":
            each = float(arm_level(self.level))
            if self.kind == "difference":
                scale = abs(self.value) if relative else 1.0

                def part(group, x, n):
                    low, up = exact_bounds(x, n, each)
                    return up - low

                return part, lambda bound: 2 * bound * scale
            if not relative:
                return None
            transform = math.log if self.kind == "ratio" else (lambda p: math.log(_odds(p)))

            def log_part(group, x, n):
                low, up = exact_bounds(x, n, each)
                if low <= 0 or up >= 1 and self.kind == "odds":
                    return INFINITE
                return transform(up) - transform(low)

            return log_part, lambda bound: -2 * math.log1p(-bound) if bound < 1 else INFINITE
        z = _NORMAL.inv_cdf(1 - (1 - level) / 2)
        if self.kind == "difference":
            scale = abs(self.value) if relative else 1.0

            def variance(group, x, n):
                p = x / n
                return self.effect * p * (1 - p) / n

            return variance, lambda bound: (bound * scale / z) ** 2
        if not relative:
            return None

        def log_variance(group, x, n):
            if self.kind == "ratio":
                return INFINITE if x <= 0 else self.effect * (1 / x - 1 / n)
            return INFINITE if x <= 0 or x >= n else self.effect * (1 / x + 1 / (n - x))

        return log_variance, lambda bound: (-math.log1p(-bound) / z) ** 2 if bound < 1 else INFINITE
