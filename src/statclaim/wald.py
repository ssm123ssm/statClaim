"""Find integer hints for the Lean checker of balanced Wald and score tests."""

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import ceil, comb, isqrt

# These are also the checker parameters in StatClaim/Modules/Wald.lean.
WEIGHT_SCALE = 1024
EXACT_TAIL_TERMS = 12
GRID = 16384
COUNTEREXAMPLE_GRID = 128
PROPORTION_Z_TESTS = ("wald_test", "score_test")


@dataclass(frozen=True)
class WaldCertificate:
    weights: tuple[int, ...]
    cells: tuple[int, ...]


def _upper_start(n: int, cutoff: Fraction, total: int, pooled: bool) -> int:
    size = 2 * n
    a, b = cutoff.numerator, cutoff.denominator
    multiplier = b * size if pooled else b * size + a
    return (total + isqrt(a * total * (size - total) // multiplier)) // 2 + 1


def _scaled_weight(n: int, cutoff: Fraction, total: int, pooled: bool) -> int:
    """Round up twice the upper-tail weight after bounding its remainder."""
    start = _upper_start(n, cutoff, total, pooled)
    end = min(n, total)
    residual = start + EXACT_TAIL_TERMS
    leading = sum(comb(n, k) * comb(n, total - k) for k in range(start, min(end + 1, residual)))
    remainder = Fraction(0)
    if residual <= end:
        den = (residual + 1) * (n - (total - residual) + 1)
        num = (n - residual) * (total - residual)
        remainder = Fraction(comb(n, residual) * comb(n, total - residual) * den, den - num)
    return ceil(2 * WEIGHT_SCALE * (leading + remainder))


@lru_cache(maxsize=64)
def find_certificate(
    n: int, cutoff: Fraction, alpha: Fraction, *, pooled: bool = False
) -> WaldCertificate | None:
    """Split poorly bounded cells until the entire null has a candidate certificate."""
    size = 2 * n
    weights = tuple(_scaled_weight(n, cutoff, total, pooled) for total in range(size + 1))
    nonzero = tuple((t, weight) for t, weight in enumerate(weights) if weight)
    limit = (alpha.numerator * WEIGHT_SCALE * GRID**size) // alpha.denominator
    endpoints: list[int] = []
    pending = [(0, GRID)]
    while pending:
        low, high = pending.pop()
        numerator = sum(weight * high**t * (GRID - low) ** (size - t) for t, weight in nonzero)
        if numerator <= limit:
            endpoints.append(high)
        elif high - low == 1:
            return None
        else:
            middle = (low + high) // 2
            pending.extend(((middle, high), (low, middle)))
    return WaldCertificate(weights, tuple(endpoints))


@lru_cache(maxsize=64)
def find_counterexample(
    n: int, cutoff: Fraction, alpha: Fraction, *, pooled: bool = False
) -> tuple[Fraction, Fraction] | None:
    """Propose a rational null rate and its exact rejection probability for Lean to check."""
    choose = [comb(n, k) for k in range(n + 1)]
    weights = [
        2
        * sum(
            choose[k] * choose[total - k]
            for k in range(_upper_start(n, cutoff, total, pooled), min(n, total) + 1)
        )
        for total in range(2 * n + 1)
    ]
    # Try the middle first, then the new interior points of progressively finer grids.
    for depth in range(1, COUNTEREXAMPLE_GRID.bit_length()):
        den = 1 << depth
        scale = den ** (2 * n)
        for num in range(1, den, 2):
            complement = den - num
            value, power = 0, 1
            for weight in reversed(weights):
                value = weight * power + num * value
                power *= complement
            if value * alpha.denominator > alpha.numerator * scale:
                return Fraction(num, den), Fraction(value, scale)
    return None
