"""Deciding a target from a value summed exactly in floating point.

Some powers are exact sums computed in floating point: Fisher's test at interim looks,
summed over every path of counts, and the logistic Wald test, summed over both arms'
counts. Their rounding error is far below 1e-9. A target is met or missed only when the
value is clear of it by more than that; closer, the calculation cannot tell, and says so
instead of letting rounding decide.
"""

from fractions import Fraction

ROUNDING = 1e-9


def meets(value: float, target: Fraction) -> bool | None:
    """True or False when the value is clear of the target, None when too close to tell."""
    if value >= float(target) + ROUNDING:
        return True
    if value < float(target) - ROUNDING:
        return False
    return None
