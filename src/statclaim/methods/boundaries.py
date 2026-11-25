"""Group-sequential boundaries from an error-spending function, under the canonical joint
distribution.

At each look the test statistic is approximately normal, and the statistics at the looks have
the canonical joint distribution of Jennison and Turnbull (2000, chapter 3): the score has
independent increments, so the correlation of the statistics at looks j <= k is the square root
of the ratio of their information. A spending function says how much of the error level is
spent by each information fraction (Lan and DeMets, 1983); each look's critical value spends
exactly the increment. A two-sided design spends half the level on each side, as gsDesign and
rpact do. The crossing probabilities are integrals over the continuation region of the earlier
looks, computed by the recursive numerical integration of Jennison and Turnbull (2000, chapter
19) on their grid, with Simpson's rule. Plain floating point; boundaries agree with rpact to
about six decimals.

For two arms, the information at a look is proportional to n_c n_t / (n_c + n_t), the inverse of
the variance factor of a difference of means or proportions.
"""

import math
from fractions import Fraction
from statistics import NormalDist

# Bump whenever this file changes: every boundary and power that uses it may change.
VERSION = 1

_NORMAL = NormalDist()
GRID = 18  # Jennison and Turnbull's r: 6r - 1 grid points per look before trimming
SPENDING = ("obrien_fleming", "pocock")

LAN_DEMETS = (
    "Lan, K. K. G. and DeMets, D. L. (1983). Discrete sequential boundaries for clinical "
    "trials. Biometrika 70(3), 659-663."
)
JENNISON_TURNBULL = (
    "Jennison, C. and Turnbull, B. W. (2000). Group Sequential Methods with Applications to "
    "Clinical Trials. Chapman and Hall/CRC."
)


def spent(spending: str, alpha: float, fraction: float, sides: int = 1) -> float:
    """The error spent by information fraction `fraction` (Lan and DeMets's functions). A
    two-sided design spends half on each side, as gsDesign and rpact do."""
    if sides == 2:
        return 2.0 * spent(spending, alpha / 2.0, fraction)
    if fraction >= 1.0:
        return alpha
    if fraction <= 0.0:
        return 0.0
    if spending == "obrien_fleming":
        return 2.0 * (1.0 - _NORMAL.cdf(_NORMAL.inv_cdf(1.0 - alpha / 2.0) / math.sqrt(fraction)))
    if spending == "pocock":
        return alpha * math.log(1.0 + (math.e - 1.0) * fraction)
    raise ValueError(f"Unknown spending function {spending!r}.")


def _grid(mean: float, low: float, high: float) -> tuple[list[float], list[float]]:
    """Points and Simpson weights on (low, high) for a density centred at `mean`."""
    r = GRID
    raw = []
    for i in range(1, 6 * r):
        if i < r:
            raw.append(mean - 3.0 - 4.0 * math.log(r / i))
        elif i <= 5 * r:
            raw.append(mean - 3.0 + 3.0 * (i - r) / (2.0 * r))
        else:
            raw.append(mean + 3.0 + 4.0 * math.log(r / (6 * r - i)))
    inside = [x for x in raw if low < x < high]
    points = [low] + inside + [high] if low < high else []
    if len(points) < 2:
        return [], []
    nodes, weights = [], []
    for index, (left, right) in enumerate(zip(points, points[1:], strict=False)):
        width = right - left
        if index == 0:
            nodes.append(left)
            weights.append(width / 6.0)
        else:
            weights[-1] += width / 6.0
        nodes.append((left + right) / 2.0)
        weights.append(4.0 * width / 6.0)
        nodes.append(right)
        weights.append(width / 6.0)
    return nodes, weights


def _tail(critical: float, sides: int, shift: float, scale: float) -> float:
    """P(statistic beyond the critical value) for N(shift, scale^2)."""
    upper = 1.0 - _NORMAL.cdf((critical - shift) / scale)
    if sides == 1:
        return upper
    return upper + _NORMAL.cdf((-critical - shift) / scale)


class _Path:
    """The sub-density of the statistic at the last look, on the paths that have not crossed."""

    def __init__(self, drift: float, sides: int):
        self.drift, self.sides = drift, sides
        self.info = 0.0
        self.nodes: list[float] = []
        self.weights: list[float] = []
        self.density: list[float] = []

    def _moves(self, info: float):
        step = info - self.info
        root_prev, root = math.sqrt(self.info), math.sqrt(info)
        scale = math.sqrt(step / info)
        shifts = [(z * root_prev + self.drift * step) / root for z in self.nodes]
        return shifts, scale

    def crossing(self, info: float, critical: float) -> float:
        """The chance of crossing first at a look with this information and critical value."""
        if not self.nodes and self.info == 0.0:
            return _tail(critical, self.sides, self.drift * math.sqrt(info), 1.0)
        shifts, scale = self._moves(info)
        return sum(
            w * f * _tail(critical, self.sides, shift, scale)
            for shift, f, w in zip(shifts, self.density, self.weights, strict=True)
        )

    def advance(self, info: float, critical: float) -> None:
        """Move to the next look, keeping only paths that do not cross it."""
        mean = self.drift * math.sqrt(info)
        low = -critical if self.sides == 2 else -math.inf
        nodes, weights = _grid(mean, max(low, mean - 12.0), min(critical, mean + 12.0))
        if self.info == 0.0:
            density = [_NORMAL.pdf(x - mean) for x in nodes]
        else:
            shifts, scale = self._moves(info)
            mass = [w * f for f, w in zip(self.density, self.weights, strict=True)]
            density = [
                sum(
                    m * _NORMAL.pdf((x - shift) / scale)
                    for m, shift in zip(mass, shifts, strict=True)
                )
                / scale
                for x in nodes
            ]
        self.info, self.nodes, self.weights, self.density = info, nodes, weights, density


def crossings(
    information: list[float], criticals: list[float], sides: int, drift: float = 0.0
) -> list[float]:
    """The chance of first crossing at each look, with mean drift * sqrt(information) at
    each look (0 under the null)."""
    path = _Path(drift, sides)
    found = []
    for info, critical in zip(information, criticals, strict=True):
        found.append(path.crossing(info, critical))
        path.advance(info, critical)
    return found


def boundaries(information: list[float], alpha: float, sides: int, spending: str) -> list[float]:
    """Critical values that spend the error by the spending function at each look."""
    final = information[-1]
    path = _Path(0.0, sides)
    criticals: list[float] = []
    before = 0.0
    for info in information:
        now = spent(spending, alpha, info / final, sides)
        target, before = now - before, now
        if target <= 1e-15:
            critical = math.inf
        else:
            low, high = 0.0, 40.0
            while high - low > 1e-10:
                middle = (low + high) / 2.0
                if path.crossing(info, middle) > target:
                    low = middle
                else:
                    high = middle
            critical = high
        criticals.append(critical)
        path.advance(info, critical)
    return criticals


def information(sizes: list[tuple[int, int]]) -> list[float]:
    """Each look's information, up to a constant, from its cumulative arm sizes."""
    return [n_c * n_t / (n_c + n_t) for n_c, n_t in sizes]


def nominal(critical: float, sides: int) -> float:
    """The nominal level of a critical value: the p-value threshold at that look."""
    return sides * (1.0 - _NORMAL.cdf(critical))


def critical(level: float, sides: int) -> float:
    return _NORMAL.inv_cdf(1.0 - level / sides) if level > 0 else math.inf


def levels(information: list[float], alpha: float, sides: int, spending: str) -> list[float]:
    return [nominal(c, sides) for c in boundaries(information, alpha, sides, spending)]


def floor_level(level: float, places: int) -> Fraction:
    """A level rounded down to `places` decimals, so a declared level at most this is within
    the boundary."""
    scale = 10**places
    return Fraction(math.floor(level * scale), scale)


def limits(
    sizes: list[tuple[int, int]], alpha: Fraction, sides: int, spending: str
) -> tuple[Fraction, ...]:
    """The largest nominal level each look may use: the boundary's, rounded down to 1e-9."""
    found = levels(information(sizes), float(alpha), sides, spending)
    return tuple(floor_level(level, 9) for level in found)


def overall(sizes: list[tuple[int, int]], declared: list[Fraction], sides: int) -> float:
    """The chance of rejecting at some look under the null, with the declared nominal levels,
    under the canonical joint distribution."""
    info = information(sizes)
    return sum(crossings(info, [critical(float(level), sides) for level in declared], sides))


def stopping(
    sizes: list[tuple[int, int]], declared: list[Fraction], sides: int, drift: float
) -> list[float]:
    """The chance of stopping at each look when the standardised effect is `drift` per unit of
    information: a normal approximation of a design's power."""
    info = information(sizes)
    return crossings(info, [critical(float(level), sides) for level in declared], sides, drift)
