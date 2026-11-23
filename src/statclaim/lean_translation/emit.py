"""Lean text for translated programs: names, exact numbers and comments."""

import re
from fractions import Fraction

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")
# Lean words a .stat name could spell. Such names are written «quoted».
KEYWORDS = frozenset(
    """
    at by do else end fun have if in let match then from show with where open import
    variable theorem def structure instance namespace section example deriving mutual
    inductive class abbrev axiom universe macro syntax set_option attribute protected
    private noncomputable partial unsafe opaque calc suffices obtain intro exact
    Type Prop Sort True False
    """.split()
)


def name(text: str) -> str:
    """A Lean identifier for a .stat name or a name built from one."""
    if not IDENTIFIER.fullmatch(text):
        raise ValueError(f"{text!r} cannot be a Lean name.")
    return f"«{text}»" if text in KEYWORDS or not text[0].isalpha() else text


def rational(value: int | Fraction) -> str:
    """An exact rational as a ℚ term."""
    exact = Fraction(value)
    if exact.denominator == 1:
        return f"({exact.numerator} : ℚ)"
    return f"(({exact.numerator} : ℚ) / {exact.denominator})"


def real(value: int | Fraction) -> str:
    """An exact rational cast to ℝ, the form claims state levels in."""
    return f"(↑{rational(value)} : ℝ)"


def comment(text: object) -> str:
    """One line of text that cannot end or open a Lean comment."""
    return " ".join(str(text).split()).replace("-/", "- /").replace("/-", "/ -")


class Namer:
    """Unique Lean names: binding names first, then names built for unnamed values."""

    def __init__(self, reserved: list[str]):
        self.taken = set(reserved)
        self.counts: dict[str, int] = {}

    def fresh(self, base: str) -> str:
        if base not in self.taken:
            self.taken.add(base)
            return base
        number = self.counts.get(base, 1)
        while f"{base}_{number}" in self.taken:
            number += 1
        self.counts[base] = number + 1
        self.taken.add(f"{base}_{number}")
        return f"{base}_{number}"
