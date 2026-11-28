"""Exact certificate proposals for asymptotic tests on finite binary samples."""

from collections.abc import Callable
from fractions import Fraction
from functools import lru_cache
from math import comb

from statclaim.planning import margin_grid, margin_rejection_probability
from statclaim.wald import COUNTEREXAMPLE_GRID, GRID


def _cover(start: int, stop: int, accepts: Callable[[int, int], bool]) -> tuple[int, ...] | None:
    cells = []
    pending = [(start, stop)]
    while pending:
        low, high = pending.pop()
        if accepts(low, high):
            cells.append(high)
        elif high - low == 1:
            return None
        else:
            middle = (low + high) // 2
            pending.extend(((middle, high), (low, middle)))
    return tuple(cells)


def _witness(
    start: Fraction,
    alpha: Fraction,
    probability: Callable[[Fraction], Fraction],
) -> tuple[Fraction, Fraction] | None:
    width = 1 - start
    for p in (start, Fraction(1)):
        value = probability(p)
        if value > alpha:
            return p, value
    for depth in range(1, COUNTEREXAMPLE_GRID.bit_length()):
        denominator = 2**depth
        for k in range(1, denominator, 2):
            p = start + width * Fraction(k, denominator)
            value = probability(p)
            if value > alpha:
                return p, value
    return None


@lru_cache(maxsize=64)
def mcnemar_weights(n: int, cutoff: Fraction) -> tuple[tuple[int, int], ...]:
    a, b = cutoff.as_integer_ratio()
    weights = []
    for d in range(1, n + 1):
        rejected = sum(comb(d, k) for k in range(d + 1) if a * d < b * (2 * k - d) ** 2)
        if rejected:
            weights.append((d, comb(n, d) * rejected * 2 ** (n - d)))
    return tuple(weights)


def _mcnemar_numerator(n: int, cutoff: Fraction, high: int, complement: int) -> int:
    return sum(weight * high**d * complement ** (n - d) for d, weight in mcnemar_weights(n, cutoff))


def mcnemar_probability(n: int, cutoff: Fraction, q: Fraction) -> Fraction:
    a, b = q.as_integer_ratio()
    return Fraction(_mcnemar_numerator(n, cutoff, a, b - a), (2 * b) ** n)


@lru_cache(maxsize=64)
def mcnemar_certificate(n: int, cutoff: Fraction, alpha: Fraction) -> tuple[int, ...] | None:
    limit = alpha * (2 * GRID) ** n
    return _cover(
        0, GRID, lambda low, high: _mcnemar_numerator(n, cutoff, high, GRID - low) <= limit
    )


@lru_cache(maxsize=64)
def mcnemar_witness(n: int, cutoff: Fraction, alpha: Fraction) -> tuple[Fraction, Fraction] | None:
    return _witness(Fraction(0), alpha, lambda q: mcnemar_probability(n, cutoff, q))


type Bracket = tuple[Fraction, Fraction]
type Region = tuple[tuple[int, ...], tuple[Bracket, ...]]


def _fm_table(nc: int, nt: int, x: int, y: int, delta: Fraction, cutoff: Fraction):
    gap = Fraction(y, nt) - Fraction(x, nc) + delta
    lo, hi = delta, Fraction(1)
    if gap <= 0:
        return False, (lo, hi)

    def variance_bound(left: Fraction, right: Fraction) -> Fraction:
        return left * (1 - right) / nc + (left - delta) * (1 - right + delta) / nt

    square = gap**2
    for _ in range(24):
        if square <= cutoff * variance_bound(lo, hi):
            return False, (lo, hi)
        if cutoff * variance_bound(hi, lo) < square:
            return True, (lo, hi)
        middle = (lo + hi) / 2
        score = x / middle - (nc - x) / (1 - middle) + y / (middle - delta)
        score -= (nt - y) / (1 - middle + delta)
        if score == 0:
            return cutoff * variance_bound(middle, middle) < square, (middle, middle)
        if score > 0:
            lo = middle
        else:
            hi = middle
    return None, (lo, hi)


@lru_cache(maxsize=32)
def fm_regions(nc: int, nt: int, margin: Fraction, cutoff: Fraction) -> tuple[Region, Region]:
    """Propose an upper monotone region and a lower region with proven rejections."""
    outer = []
    inner = []
    brackets = []
    for x in range(nc + 1):
        first_possible = nt + 1
        last_unproved = -1
        for y in range(nt + 1):
            reject, bracket = _fm_table(nc, nt, x, y, -margin, cutoff)
            if reject is not False:
                first_possible = min(first_possible, y)
            if reject is not True:
                last_unproved = y
            brackets.append(bracket)
        outer.append(first_possible)
        inner.append(last_unproved + 1)
    for x in range(nc - 1, -1, -1):
        outer[x] = min(outer[x], outer[x + 1])
    data = tuple(brackets)
    return (tuple(outer), data), (tuple(inner), data)


@lru_cache(maxsize=32)
def fm_certificate(
    nc: int, nt: int, margin: Fraction, cutoff: Fraction, alpha: Fraction
) -> tuple[Region, int, int, tuple[int, ...]] | None:
    outer, _ = fm_regions(nc, nt, margin, cutoff)
    grid, shift = margin_grid(margin)
    cells = _cover(
        -shift,
        grid,
        lambda low, high: (
            margin_rejection_probability(
                nc, nt, outer[0], Fraction(low, grid), Fraction(high + shift, grid)
            )
            <= alpha
        ),
    )
    return (outer, grid, -shift, cells) if cells else None


@lru_cache(maxsize=32)
def fm_witness(
    nc: int, nt: int, margin: Fraction, cutoff: Fraction, alpha: Fraction
) -> tuple[Fraction, Fraction] | None:
    _, inner = fm_regions(nc, nt, margin, cutoff)
    return _witness(
        -margin,
        alpha,
        lambda p: margin_rejection_probability(nc, nt, inner[0], p, p + margin),
    )


def one_sample_score_probability(n: int, reference: Fraction, cutoff: Fraction) -> Fraction:
    """Exact size of the two-sided score test at its point null."""
    a, d = reference.as_integer_ratio()
    critical = cutoff.numerator * a * (d - a) * n
    weight = sum(
        comb(n, k) * a**k * (d - a) ** (n - k)
        for k in range(n + 1)
        if cutoff.denominator * (k * d - n * a) ** 2 > critical
    )
    return Fraction(weight, d**n)


@lru_cache(maxsize=32)
def pearson_weights(nc: int, nt: int, cutoff: Fraction, corrected: bool) -> tuple[int, ...]:
    total_n = nc + nt
    a, b = cutoff.as_integer_ratio()
    control_weights = [comb(nc, x) for x in range(nc + 1)]
    treatment_weights = [comb(nt, y) for y in range(nt + 1)]
    correction = total_n if corrected else 0
    coefficients = [0] * (total_n + 1)
    for x, weight_x in enumerate(control_weights):
        for y, weight_y in enumerate(treatment_weights):
            total = x + y
            gap = max(0, 2 * abs(y * nc - x * nt) - correction)
            if 4 * a * nc * nt * total * (total_n - total) < b * total_n * gap**2:
                coefficients[total] += weight_x * weight_y
    return tuple(coefficients)


def _integer_polynomial(weights: tuple[int, ...], point: int, complement: int) -> int:
    degree = len(weights) - 1
    return sum(
        weight * point**i * complement ** (degree - i) for i, weight in enumerate(weights) if weight
    )


@lru_cache(maxsize=64)
def pearson_certificate(
    nc: int, nt: int, cutoff: Fraction, alpha: Fraction, corrected: bool
) -> tuple[int, ...] | None:
    coefficients = pearson_weights(nc, nt, cutoff, corrected)
    limit = alpha * GRID ** (nc + nt)
    return _cover(
        0,
        GRID,
        lambda low, high: _integer_polynomial(coefficients, high, GRID - low) <= limit,
    )


@lru_cache(maxsize=64)
def pearson_witness(
    nc: int, nt: int, cutoff: Fraction, alpha: Fraction, corrected: bool
) -> tuple[Fraction, Fraction] | None:
    coefficients = pearson_weights(nc, nt, cutoff, corrected)

    def probability(p: Fraction) -> Fraction:
        a, d = p.as_integer_ratio()
        return Fraction(_integer_polynomial(coefficients, a, d - a), d ** (nc + nt))

    return _witness(Fraction(0), alpha, probability)
