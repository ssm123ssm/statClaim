"""Find integer hints for the Lean checker of the balanced Wald test."""

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import ceil, comb, isqrt

# These are also the checker parameters in StatClaim/Modules/Wald.lean.
WEIGHT_SCALE = 1024
EXACT_TAIL_TERMS = 12
GRID = 16384


@dataclass(frozen=True)
class WaldCertificate:
    weights: tuple[int, ...]
    cells: tuple[int, ...]


def _scaled_weight(n: int, cutoff: Fraction, total: int) -> int:
    """Round up twice the upper-tail weight after bounding its remainder."""
    size = 2 * n
    a, b = cutoff.numerator, cutoff.denominator
    start = (total + isqrt(a * total * (size - total) // (b * size + a))) // 2 + 1
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
def find_certificate(n: int, cutoff: Fraction, alpha: Fraction) -> WaldCertificate | None:
    """Split poorly bounded cells until the entire null has a candidate certificate."""
    size = 2 * n
    weights = tuple(_scaled_weight(n, cutoff, total) for total in range(size + 1))
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
