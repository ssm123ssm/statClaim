"""Write exact rationals as Lean data."""

from fractions import Fraction


def rational(value: int | Fraction) -> str:
    """An exact rational as a ℚ term."""
    exact = Fraction(value)
    if exact.denominator == 1:
        return f"({exact.numerator} : ℚ)"
    return f"(({exact.numerator} : ℚ) / {exact.denominator})"
