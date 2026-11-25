"""Exact power of the proved observational tests at one planning point.

Fisher's test of no association, when the design fixes two groups: a cohort that sampled its
exposed and unexposed groups, or a case-control study. The table then holds two independent
binomial counts with their own probabilities: the risk of the outcome in each group of a
cohort, or the probability of exposure among controls and among cases.

McNemar's test of matched pairs: the number of discordant pairs is binomial, and given it the
number in which the case is the exposed one is binomial too, so power is an average over the
discordant pairs. The rate test, given the total number of events: the exposed share of the
events is binomial. Both reject when twice the smaller binomial tail is at most alpha.

Calculations use integers and fractions only. A certificate proposes nothing that Lean
trusts: the kernel recomputes each rejection region from the formal p-value or tails
(StatClaim.Modules.AssociationPower, StatClaim.Modules.BinomialPower). Power at a planning
point says nothing about other points, and nothing about an effect of the exposure.
"""

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb
from typing import Literal

from statclaim.association import (
    AssociationTest,
    null_words,
)
from statclaim.fisher import fraction_record
from statclaim.incidence import MAX_EVENTS, RateTest
from statclaim.matched import MatchedTest
from statclaim.planning import (
    MAX_PER_ARM,
    MAX_RATIO,
    fisher_rejection_probability,
)

GENERAL_THEOREM = "StatClaim.Modules.AssociationPower.power_of_check"
# Kernel checking enumerates every table, as for the trial Fisher analysis.
MAX_GROUP = MAX_PER_ARM
DESIGNS = ("cohort", "case_control")

# Per design: (first group, second group), the probability declared in each, and the
# names of a search's bounds and ratio. The second group is the one a search varies.
GROUPS = {
    "cohort": ("unexposed", "exposed"),
    "case_control": ("controls", "cases"),
}
POINT_KEYS = {
    "cohort": ("risk_unexposed", "risk_exposed"),
    "case_control": ("exposure_controls", "exposure_cases"),
}
SEARCH_KEYS = {
    "cohort": ("min_exposed", "max_exposed", "unexposed_per_exposed"),
    "case_control": ("min_cases", "max_cases", "controls_per_case"),
}
PLANNING_POINT = (
    "Power is evaluated at the declared planning point only; the point is a planning input, "
    "not an established fact."
)


def _probability(value: Fraction, name: str) -> None:
    if not isinstance(value, Fraction) or not 0 <= value <= 1:
        raise ValueError(f"{name} must be an exact Fraction between zero and one.")


def odds_ratio(first: Fraction, second: Fraction) -> Fraction | None:
    """The odds ratio, second group over first, or None when it is not finite."""
    if first in (0, 1) or second in (0, 1):
        return None
    return (second / (1 - second)) / (first / (1 - first))


@dataclass(frozen=True)
class AssociationPowerPlan:
    """Fisher's test of no association for a design with fixed groups, at one planning point.

    `p_first` and `p_second` are the probabilities in the test's first and second groups:
    the risk without and with exposure in a cohort, or the probability of exposure among
    controls and among cases in a case-control study. A search varies the second group,
    with `ratio` participants in the first group for each one in the second.
    """

    test: AssociationTest
    p_first: Fraction
    p_second: Fraction
    minimum_power: Fraction
    maximum_typeI: Fraction
    request: Literal["meets", "sample_size"] = "meets"
    search: tuple[int, int] | None = None
    minimal: bool = False
    ratio: int = 1

    def __post_init__(self) -> None:
        if self.test.design not in DESIGNS or self.test.groups is None:
            raise ValueError("Exact power needs a cohort or case-control study with fixed groups.")
        first, second = self.test.groups
        if max(first, second) > MAX_GROUP:
            raise ValueError(f"Each group is limited to {MAX_GROUP} participants for exact power.")
        for name in ("p_first", "p_second", "minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        if self.p_first == self.p_second:
            raise ValueError("The planning point must lie outside the null of no association.")
        if self.minimal and self.search is None:
            raise ValueError("A smallest-size claim needs a search range.")
        if (self.request == "sample_size") != (self.search is not None):
            raise ValueError("Search bounds accompany exactly the sample_size request.")
        if type(self.ratio) is not int or not 1 <= self.ratio <= MAX_RATIO:
            raise ValueError(f"The ratio between the groups must be from 1 to {MAX_RATIO}.")
        if self.ratio != 1 and self.search is None:
            raise ValueError("A ratio between the groups describes a search.")
        if self.search is not None:
            low, high = self.search
            if type(low) is not int or type(high) is not int or not 1 <= low <= high:
                raise ValueError("Search bounds must be integers with 1 <= min <= max.")
            if self.ratio * high > MAX_GROUP:
                raise ValueError(f"Each group is limited to {MAX_GROUP} participants.")
            if not (low <= second <= high and first == self.ratio * second):
                raise ValueError("The certified design must be a candidate of the search.")

    @property
    def design(self) -> str:
        return self.test.design

    @property
    def power(self) -> Fraction:
        first, second = self.test.groups
        return fisher_rejection_probability(
            first, second, self.test.alpha, self.p_first, self.p_second
        )

    @property
    def typeI_target_met(self) -> bool:
        """The theorem bounds Type I error by alpha; nothing tighter is used."""
        return self.test.alpha <= self.maximum_typeI

    def measures(self) -> dict:
        """What the planning point implies for the measures the design can estimate."""
        ratio = odds_ratio(self.p_first, self.p_second)
        measures = {"odds_ratio": None if ratio is None else fraction_record(ratio)}
        if self.design == "cohort":
            risk = self.p_second / self.p_first if self.p_first > 0 else None
            measures["risk_ratio"] = None if risk is None else fraction_record(risk)
            measures["risk_difference"] = fraction_record(self.p_second - self.p_first)
        return measures

    def evaluate(self) -> dict:
        power = self.power
        first_name, second_name = GROUPS[self.design]
        first_key, second_key = POINT_KEYS[self.design]
        first, second = self.test.groups
        return {
            "design": self.design,
            second_name: second,
            first_name: first,
            "total_sample_size": first + second,
            first_key: fraction_record(self.p_first),
            second_key: fraction_record(self.p_second),
            **self.measures(),
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
            "typeI_bound": fraction_record(self.test.alpha),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": self.typeI_target_met,
        }


def search_groups(
    test: AssociationTest,
    p_first: Fraction,
    p_second: Fraction,
    minimum_power: Fraction,
    maximum_typeI: Fraction,
    low: int,
    high: int,
    minimal: bool = False,
    ratio: int = 1,
) -> tuple[AssociationPowerPlan | None, int]:
    """The first size of the second group, ascending, whose design meets the power target.

    Power is not assumed to increase with the sample size; every candidate is evaluated.
    """
    for evaluated, size in enumerate(range(low, high + 1), 1):
        candidate = AssociationTest(
            test.design, test.alpha, (ratio * size, size), None, test.exposure, test.outcome
        )
        plan = AssociationPowerPlan(
            candidate,
            p_first,
            p_second,
            minimum_power,
            maximum_typeI,
            "sample_size",
            (low, high),
            minimal,
            ratio,
        )
        if plan.power >= minimum_power:
            return plan, evaluated
    return None, high - low + 1


def point_words(test: AssociationTest, p_first: Fraction, p_second: Fraction) -> str:
    exposure, outcome = test.exposure, test.outcome
    if test.design == "cohort":
        return f"the risk of {outcome} is {p_second} with {exposure} and {p_first} without it"
    return f"{exposure} is found in {p_second} of cases of {outcome} and {p_first} of controls"


def target_words(test: AssociationTest, target: tuple, search=None, minimal=False) -> str:
    """The planning claim in words, before anything is calculated."""
    p_first, p_second, minimum, maximum = target
    goal = (
        f"power >= {minimum} when {point_words(test, p_first, p_second)}; Type I error <= "
        f"{maximum} whenever {null_words(test)}"
    )
    if search is None:
        first, second = test.groups
        return f"Fisher's exact test with {_sizes_words(test.design, first, second)} gives {goal}."
    low, high, ratio = search
    second_name = GROUPS[test.design][1]
    scope = "No smaller candidate in the range does." if minimal else "Minimality is not claimed."
    return (
        f"Some design with {low} to {high} {second_name}{_each(test.design, ratio)} gives "
        f"{goal}. {scope}"
    )


def _each(design: str, ratio: int) -> str:
    if ratio == 1:
        return ""
    if design == "cohort":
        return f", {ratio} unexposed for each exposed"
    return f", {ratio} controls per case"


def _ratio(value: Fraction) -> str:
    numerator, denominator = value.as_integer_ratio()
    return f"((({numerator} : ℕ) : ℝ) / (({denominator} : ℕ) : ℝ))"


# Two-sided exact binomial tests: McNemar's test and the rate test ----------------------------
MATCHED_KIND = "statclaim_matched_planning_certificate"
RATE_KIND = "statclaim_rate_planning_certificate"
RATE_THEOREM = "StatClaim.Modules.BinomialPower.power_of_check"
# Pairs in a planned matched study: the kernel sums both tails for every number discordant.
MAX_PLANNED_PAIRS = 400
HALF = Fraction(1, 2)


@lru_cache(maxsize=4096)
def binomial_region(n: int, share: Fraction, alpha: Fraction) -> tuple[int, int]:
    """With n trials, the two-sided test of the share rejects the counts below `low` and those
    from `high` up: twice the smaller tail is at most alpha exactly there. Lean checks both."""
    c, f = share.as_integer_ratio()
    an, ad = alpha.as_integer_ratio()
    weights = [comb(n, k) * c**k * (f - c) ** (n - k) for k in range(n + 1)]
    limit = an * f**n
    low = cumulative = 0
    for x in range(n + 1):
        cumulative += weights[x]
        if 2 * cumulative * ad > limit:
            break
        low = x + 1
    high, cumulative = n + 1, 0
    for x in range(n, -1, -1):
        cumulative += weights[x]
        if 2 * cumulative * ad > limit:
            break
        high = x
    return low, high


def region_numerator(n: int, a: int, d: int, low: int, high: int) -> int:
    """Numerator of the probability of a count below low or from high up, at the share a/d;
    the denominator is d ** n."""
    return sum(comb(n, x) * a**x * (d - a) ** (n - x) for x in range(n + 1) if x < low or high <= x)


@dataclass(frozen=True)
class MatchedPowerPlan:
    """McNemar's test for a declared number of pairs, at one planning point: the probability
    that a pair is discordant and the conditional odds ratio."""

    test: MatchedTest
    discordant: Fraction
    odds_ratio: Fraction
    minimum_power: Fraction
    maximum_typeI: Fraction
    request: Literal["meets", "sample_size"] = "meets"
    search: tuple[int, int] | None = None
    minimal: bool = False

    def __post_init__(self) -> None:
        if not 1 <= self.test.pairs <= MAX_PLANNED_PAIRS:
            raise ValueError(f"Exact power is limited to {MAX_PLANNED_PAIRS} pairs.")
        _probability(self.discordant, "discordant")
        if self.discordant == 0:
            raise ValueError("Some pairs must be discordant for the test to have power.")
        _positive(self.odds_ratio, "odds_ratio")
        if self.odds_ratio == 1:
            raise ValueError("The planning point must lie outside the null of no association.")
        for name in ("minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        _search_checks(self, self.test.pairs, MAX_PLANNED_PAIRS)

    @property
    def case_share(self) -> Fraction:
        """In a discordant pair, the probability that the case is the exposed one."""
        return self.odds_ratio / (1 + self.odds_ratio)

    @property
    def power(self) -> Fraction:
        n, alpha = self.test.pairs, self.test.alpha
        a, d = self.discordant.as_integer_ratio()
        b, e = self.case_share.as_integer_ratio()
        numerator = sum(
            comb(n, k)
            * a**k
            * (d - a) ** (n - k)
            * region_numerator(k, b, e, *binomial_region(k, HALF, alpha))
            * e ** (n - k)
            for k in range(n + 1)
        )
        return Fraction(numerator, d**n * e**n)

    @property
    def typeI_target_met(self) -> bool:
        return self.test.alpha <= self.maximum_typeI

    def evaluate(self) -> dict:
        power = self.power
        return {
            "design": "matched_case_control",
            "pairs": self.test.pairs,
            "discordant": fraction_record(self.discordant),
            "odds_ratio": fraction_record(self.odds_ratio),
            "case_exposed_share": fraction_record(self.case_share),
            "expected_discordant_pairs": fraction_record(self.test.pairs * self.discordant),
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
            "typeI_bound": fraction_record(self.test.alpha),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": self.typeI_target_met,
        }


@dataclass(frozen=True)
class RatePowerPlan:
    """The rate test given a total number of events, at one planning point: the person-time
    in each group, of which only the exposed share matters, and the rate ratio."""

    test: RateTest
    exposed_time: Fraction
    unexposed_time: Fraction
    rate_ratio: Fraction
    events: int
    minimum_power: Fraction
    maximum_typeI: Fraction
    request: Literal["meets", "sample_size"] = "meets"
    search: tuple[int, int] | None = None
    minimal: bool = False

    def __post_init__(self) -> None:
        for name in ("exposed_time", "unexposed_time", "rate_ratio"):
            _positive(getattr(self, name), name)
        if self.rate_ratio == 1:
            raise ValueError("The planning point must lie outside the null of equal rates.")
        if type(self.events) is not int or not 1 <= self.events <= MAX_EVENTS:
            raise ValueError(f"The number of events must be from 1 to {MAX_EVENTS}.")
        for name in ("minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        _search_checks(self, self.events, MAX_EVENTS)

    @property
    def share(self) -> Fraction:
        """The exposed share of person-time: the share of events under equal rates."""
        return self.exposed_time / (self.exposed_time + self.unexposed_time)

    @property
    def event_share(self) -> Fraction:
        """The exposed share of events at the planning point's rate ratio."""
        exposed = self.rate_ratio * self.exposed_time
        return exposed / (exposed + self.unexposed_time)

    @property
    def power(self) -> Fraction:
        a, d = self.event_share.as_integer_ratio()
        low, high = binomial_region(self.events, self.share, self.test.alpha)
        return Fraction(region_numerator(self.events, a, d, low, high), d**self.events)

    @property
    def typeI_target_met(self) -> bool:
        return self.test.alpha <= self.maximum_typeI

    def evaluate(self) -> dict:
        power = self.power
        return {
            "design": "person_time_cohort",
            "events": self.events,
            "rate_ratio": fraction_record(self.rate_ratio),
            "exposed_time_share": fraction_record(self.share),
            "exposed_event_share": fraction_record(self.event_share),
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
            "typeI_bound": fraction_record(self.test.alpha),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": self.typeI_target_met,
        }


def search_pairs(plan: MatchedPowerPlan, low: int, high: int, minimal: bool = False):
    """The first number of pairs, ascending, whose design meets the power target."""
    for evaluated, size in enumerate(range(low, high + 1), 1):
        candidate = MatchedPowerPlan(
            MatchedTest(size, plan.test.alpha, plan.test.exposure, plan.test.outcome),
            plan.discordant,
            plan.odds_ratio,
            plan.minimum_power,
            plan.maximum_typeI,
            "sample_size",
            (low, high),
            minimal,
        )
        if candidate.power >= plan.minimum_power:
            return candidate, evaluated
    return None, high - low + 1


def search_events(plan: RatePowerPlan, low: int, high: int, minimal: bool = False):
    """The first total number of events, ascending, that meets the power target."""
    for evaluated, size in enumerate(range(low, high + 1), 1):
        candidate = RatePowerPlan(
            plan.test,
            plan.exposed_time,
            plan.unexposed_time,
            plan.rate_ratio,
            size,
            plan.minimum_power,
            plan.maximum_typeI,
            "sample_size",
            (low, high),
            minimal,
        )
        if candidate.power >= plan.minimum_power:
            return candidate, evaluated
    return None, high - low + 1


RATE_EVENTS = (
    "Power is given the planned total number of events; the total itself varies with the "
    "rates and the person-time."
)


# Participants in all: the kernel checks Fisher's region for every number exposed.
MAX_TOTAL = 150
TOTAL_POINT_KEYS = {
    "cohort": ("risk_unexposed", "risk_exposed"),
    "cross_sectional": ("prevalence_unexposed", "prevalence_exposed"),
}


@dataclass(frozen=True)
class TotalPowerPlan:
    """Fisher's test of no association for a cross-sectional study, or a cohort of one
    population, at one planning point: the share of participants exposed, and the
    probability of the outcome without and with exposure. Only the total is fixed."""

    test: AssociationTest
    p_first: Fraction
    p_second: Fraction
    exposed_share: Fraction
    minimum_power: Fraction
    maximum_typeI: Fraction
    request: Literal["meets", "sample_size"] = "meets"
    search: tuple[int, int] | None = None

    def __post_init__(self) -> None:
        if self.test.design not in TOTAL_POINT_KEYS or self.test.n is None:
            raise ValueError("This plan is for a design that fixes only its total.")
        if self.test.n > MAX_TOTAL:
            raise ValueError(f"Exact power is limited to {MAX_TOTAL} participants in all.")
        for name in ("p_first", "p_second", "exposed_share", "minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        if not 0 < self.exposed_share < 1:
            raise ValueError("Some participants must be exposed and some not.")
        if self.p_first == self.p_second:
            raise ValueError("The planning point must lie outside the null of no association.")
        if (self.request == "sample_size") != (self.search is not None):
            raise ValueError("Search bounds accompany exactly the sample_size request.")
        if self.search is not None:
            low, high = self.search
            if type(low) is not int or type(high) is not int or not 1 <= low <= high <= MAX_TOTAL:
                raise ValueError(f"Search bounds must be integers from 1 to {MAX_TOTAL}.")
            if not low <= self.test.n <= high:
                raise ValueError("The certified design must be a candidate of the search.")

    @property
    def design(self) -> str:
        return self.test.design

    def parts(self) -> list[int]:
        """For each number exposed k, the numerator of the groups' rejection probability;
        its denominator is d ** (n - k) * e ** k, for the points a/d and b/e."""
        n, alpha = self.test.n, self.test.alpha
        a, d = self.p_first.as_integer_ratio()
        b, e = self.p_second.as_integer_ratio()
        return [
            fisher_rejection_probability(n - k, k, alpha, self.p_first, self.p_second)
            * d ** (n - k)
            * e**k
            for k in range(n + 1)
        ]

    @property
    def power(self) -> Fraction:
        n = self.test.n
        q, r = self.exposed_share.as_integer_ratio()
        d, e = self.p_first.denominator, self.p_second.denominator
        numerator = sum(
            comb(n, k) * q**k * (r - q) ** (n - k) * int(part) * d**k * e ** (n - k)
            for k, part in enumerate(self.parts())
        )
        return Fraction(numerator, r**n * d**n * e**n)

    @property
    def typeI_target_met(self) -> bool:
        return self.test.alpha <= self.maximum_typeI

    def measures(self) -> dict:
        ratio = odds_ratio(self.p_first, self.p_second)
        noun = "risk" if self.design == "cohort" else "prevalence"
        quotient = self.p_second / self.p_first if self.p_first > 0 else None
        return {
            "odds_ratio": None if ratio is None else fraction_record(ratio),
            f"{noun}_ratio": None if quotient is None else fraction_record(quotient),
            f"{noun}_difference": fraction_record(self.p_second - self.p_first),
        }

    def evaluate(self) -> dict:
        power = self.power
        first_key, second_key = TOTAL_POINT_KEYS[self.design]
        return {
            "design": self.design,
            "total_sample_size": self.test.n,
            "exposed_share": fraction_record(self.exposed_share),
            "expected_exposed": fraction_record(self.test.n * self.exposed_share),
            first_key: fraction_record(self.p_first),
            second_key: fraction_record(self.p_second),
            **self.measures(),
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
            "typeI_bound": fraction_record(self.test.alpha),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": self.typeI_target_met,
        }


def search_totals(plan: TotalPowerPlan, low: int, high: int):
    """The first total, ascending, whose design meets the power target. A search over totals
    certifies a sufficient size only: each smaller total would need its own full check."""
    test = plan.test
    for evaluated, size in enumerate(range(low, high + 1), 1):
        candidate = TotalPowerPlan(
            AssociationTest(test.design, test.alpha, None, size, test.exposure, test.outcome),
            plan.p_first,
            plan.p_second,
            plan.exposed_share,
            plan.minimum_power,
            plan.maximum_typeI,
            "sample_size",
            (low, high),
        )
        if candidate.power >= plan.minimum_power:
            return candidate, evaluated
    return None, high - low + 1


def total_point_words(test: AssociationTest, p_first, p_second, share) -> str:
    noun = "risk" if test.design == "cohort" else "prevalence"
    return (
        f"{share} of participants are exposed to {test.exposure} and the {noun} of "
        f"{test.outcome} is {p_second} with it and {p_first} without it"
    )


def _sizes_words(design: str, first: int, second: int) -> str:
    if design == "cohort":
        return f"{second} exposed and {first} unexposed"
    return f"{second} cases and {first} controls"


def _positive(value: Fraction, name: str) -> None:
    if not isinstance(value, Fraction) or value <= 0:
        raise ValueError(f"{name} must be a positive exact number.")


def _search_checks(plan, size: int, limit: int) -> None:
    if plan.minimal and plan.search is None:
        raise ValueError("A smallest-size claim needs a search range.")
    if (plan.request == "sample_size") != (plan.search is not None):
        raise ValueError("Search bounds accompany exactly the sample_size request.")
    if plan.search is not None:
        low, high = plan.search
        if type(low) is not int or type(high) is not int or not 1 <= low <= high <= limit:
            raise ValueError(f"Search bounds must be integers with 1 <= min <= max <= {limit}.")
        if not low <= size <= high:
            raise ValueError("The certified design must be a candidate of the search.")
