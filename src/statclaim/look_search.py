"""The candidates of a search over the sizes of a design's looks.

Every look's size per control arm is free: a candidate is any increasing choice of sizes from
the grid min_per_arm, min_per_arm + step, ..., up to max_per_arm, one for each declared look.
The treatment arm keeps the declared final look's allocation. A candidate keeps the declared
test and null. Under alpha_spending each look keeps its declared level; under group_sequential
each candidate's levels are its own boundaries, which follow its share of the information at
each look.

A candidate is ranked by its criterion: "minimax" puts the smallest final size first, and among
equal final sizes the smallest expected total at the planning point; "optimal" puts the
smallest expected total first. The ranking is a calculation, not a claim.
"""

from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb

from statclaim.methods import boundaries

CRITERIA = ("minimax", "optimal")
MAX_CANDIDATES = 2000  # increasing choices of look sizes a search may list
MAX_EXACT_ARM = 300  # participants per arm at the last look, for Fisher's exact sum

Look = tuple[int, int, Fraction]  # cumulative control and treatment sizes, and the level


def grid(low: int, high: int, step: int) -> list[int]:
    """The control sizes a look may take."""
    return list(range(low, high + 1, step))


def count(looks: int, low: int, high: int, step: int) -> int:
    """How many increasing choices of look sizes the grid allows."""
    return comb(len(grid(low, high, step)), looks)


def allocation(design) -> int | None:
    """Treatment participants per control at the final look, when a whole number."""
    model = design.final.plan.model
    ratio = Fraction(model.n_treatment, model.n_control)
    return ratio.numerator if ratio.denominator == 1 else None


@cache
def _spending_levels(
    shares: tuple[Fraction, ...], alpha: Fraction, sides: int, spending: str
) -> tuple[Fraction, ...]:
    """Boundary levels depend only on the shares of information, so they are reused."""
    found = boundaries.levels([float(share) for share in shares], float(alpha), sides, spending)
    return tuple(boundaries.floor_level(level, 9) for level in found)


def levels(design, controls: tuple[int, ...], sides: int) -> tuple[Fraction, ...]:
    """Each look's level: the declared one, or the candidate's own boundary. With one
    allocation at every look, the information is proportional to the control size."""
    if design.spending is None:
        return tuple(look.alpha for _, look in design.analyses)
    shares = tuple(Fraction(c, controls[-1]) for c in controls)
    return _spending_levels(shares, design.alpha, sides, design.spending)


def candidates(design, low: int, high: int, step: int, sides: int) -> list[tuple[Look, ...]]:
    """Every increasing choice of look sizes on the grid, with its levels, smallest first."""
    ratio = allocation(design)
    assert ratio is not None
    found = []
    for controls in combinations(grid(low, high, step), len(design.analyses)):
        chosen = levels(design, controls, sides)
        found.append(
            tuple((c, ratio * c, level) for c, level in zip(controls, chosen, strict=True))
        )
    return found


def expected_total(looks, stopped: list[float]) -> float:
    """The mean total at which the trial stops."""
    totals = [look[0] + look[1] for look in looks]
    return (
        sum(p * total for p, total in zip(stopped, totals, strict=True))
        + (1.0 - sum(stopped)) * totals[-1]
    )


def rank(criterion: str, looks, expected: float) -> tuple:
    """How a candidate is ordered: smaller is better."""
    final = looks[-1][0] + looks[-1][1]
    sizes = tuple(look[0] for look in looks)
    if criterion == "minimax":
        return (final, expected, sizes)
    return (expected, final, sizes)


RANKING = (
    "Each look's size is searched freely on the grid. The criterion ranks the candidates that "
    "meet the power target: minimax the smallest final size, then the smallest expected size "
    "at the planning point; optimal the smallest expected size. The ranking is a calculation, "
    "and only the selected design is reported."
)
