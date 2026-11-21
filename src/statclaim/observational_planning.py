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
    NOT_CAUSAL,
    TEST_ID,
    TEST_VERSION,
    AssociationTest,
    association_assumptions,
    null_words,
)
from statclaim.fisher import fraction_record, parse_alpha
from statclaim.incidence import MAX_EVENTS, RateTest, rate_assumptions, rate_null_words
from statclaim.matched import MatchedTest, matched_assumptions
from statclaim.matched import null_words as matched_null_words
from statclaim.planning import (
    MAX_PER_ARM,
    MAX_RATIO,
    SMALLEST,
    _audit,
    _lean_list,
    fisher_cuts,
    fisher_rejection_probability,
)

PLAN_KIND = "statclaim_association_planning_certificate"
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
THEOREMS = ["checked_sizes", "checked_region", "checked_typeI", "checked_power"]


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


def plan_payload(plan: AssociationPowerPlan) -> dict:
    test = plan.test
    first_key, second_key = POINT_KEYS[plan.design]
    payload = {
        "schema_version": 1,
        "scope": "association_planning",
        "request": plan.request,
        "design": {
            "kind": test.design,
            "groups": list(test.groups),
            "exposure": test.exposure,
            "outcome": test.outcome,
            "stopping": "fixed",
        },
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": "no_association",
            "alpha": str(test.alpha),
        },
        "target": {
            first_key: str(plan.p_first),
            second_key: str(plan.p_second),
            "minimum_power": str(plan.minimum_power),
            "maximum_typeI": str(plan.maximum_typeI),
        },
    }
    if plan.search is not None:
        low_key, high_key, ratio_key = SEARCH_KEYS[plan.design]
        payload["search"] = {low_key: plan.search[0], high_key: plan.search[1]}
        if plan.ratio != 1:
            payload["search"][ratio_key] = plan.ratio
        if plan.minimal:
            payload["search"]["claim"] = SMALLEST
    return payload


def parse_plan_payload(payload: dict) -> AssociationPowerPlan:
    design, target, search = payload["design"], payload["target"], payload.get("search")
    kind = design["kind"]
    if kind not in DESIGNS:
        raise ValueError("Unsupported design for exact association power.")
    first_key, second_key = POINT_KEYS[kind]
    low_key, high_key, ratio_key = SEARCH_KEYS[kind]
    plan = AssociationPowerPlan(
        AssociationTest(
            kind,
            parse_alpha(payload["analysis"]["alpha"]),
            tuple(design["groups"]),
            None,
            design["exposure"],
            design["outcome"],
        ),
        *(
            parse_alpha(target[name])
            for name in (first_key, second_key, "minimum_power", "maximum_typeI")
        ),
        payload["request"],
        (search[low_key], search[high_key]) if search else None,
        bool(search) and search.get("claim") == SMALLEST,
        search.get(ratio_key, 1) if search else 1,
    )
    if payload != plan_payload(plan):
        raise ValueError("Bound planning inputs are inconsistent.")
    return plan


def plan_theorems(plan: AssociationPowerPlan) -> list[str]:
    return THEOREMS + ["checked_smaller"] if plan.minimal else list(THEOREMS)


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


def _sizes_words(design: str, first: int, second: int) -> str:
    if design == "cohort":
        return f"{second} exposed and {first} unexposed"
    return f"{second} cases and {first} controls"


def _each(design: str, ratio: int) -> str:
    if ratio == 1:
        return ""
    if design == "cohort":
        return f", {ratio} unexposed for each exposed"
    return f", {ratio} controls per case"


def plan_claims(plan: AssociationPowerPlan) -> list[str]:
    first, second = plan.test.groups
    sizes = _sizes_words(plan.design, first, second)
    common = "common risk" if plan.design == "cohort" else "common probability of exposure"
    claims = [
        f"Fisher's exact test of no association between {plan.test.exposure} and "
        f"{plan.test.outcome}, with {sizes} and alpha {plan.test.alpha}, has Type I error at "
        f"most {plan.maximum_typeI} whenever {null_words(plan.test)}, for every {common} in "
        "[0, 1].",
        f"Its power is at least {plan.minimum_power} when "
        f"{point_words(plan.test, plan.p_first, plan.p_second)}.",
    ]
    if plan.search is None:
        return claims
    low, high = plan.search
    second_name = GROUPS[plan.design][1]
    each = _each(plan.design, plan.ratio)
    if plan.minimal:
        claims.append(
            f"No candidate with {low} to {second - 1} {second_name}{each}{',' if each else ''} "
            "reaches that "
            f"power, so {sizes} is the smallest sufficient candidate in the range {low} to "
            f"{high}. Nothing is claimed outside the range."
        )
    else:
        claims.append(
            f"{sizes[0].upper()}{sizes[1:]} are therefore sufficient among candidates with "
            f"{low} to {high} {second_name}{each}. Minimality is not claimed."
        )
    return claims


def plan_assumptions(plan: AssociationPowerPlan) -> list[str]:
    return [*association_assumptions(plan.test), PLANNING_POINT]


def plan_limitations() -> list[str]:
    return [NOT_CAUSAL]


def _ratio(value: Fraction) -> str:
    numerator, denominator = value.as_integer_ratio()
    return f"((({numerator} : ℕ) : ℝ) / (({denominator} : ℕ) : ℝ))"


def render_plan_proof(plan: AssociationPowerPlan, input_sha256: str) -> str:
    """Only validated integers and rationals enter the template; names never do."""
    if not plan.typeI_target_met:
        raise ValueError("The Type I target is not established by the theorem.")
    first, second = plan.test.groups
    alpha = plan.test.alpha
    an, ad = alpha.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    (a, d), (b, e) = plan.p_first.as_integer_ratio(), plan.p_second.as_integer_ratio()
    cuts, nexts = fisher_cuts(first, second, alpha)
    point = f"(ratPoint {a} {d} (by decide) (by decide)) (ratPoint {b} {e} (by decide) (by decide))"
    arguments = (
        f"{an} {ad} (by decide) declaredLevel.value (by norm_num [declaredLevel])\n"
        f"    {a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide) {bn} {bd} (by decide)"
    )
    smaller = ""
    if plan.minimal:
        low, r = plan.search[0], plan.ratio
        # One theorem per smaller candidate: the kernel frees each one's arithmetic before
        # the next, where a single check of them all can exhaust memory.
        facts, cases = [], []
        for n in range(low, second):
            each_cuts, each_nexts = fisher_cuts(r * n, n, alpha)
            facts.append(
                f"theorem smaller_{n} : AssociationPower.FailsHinted ({r} * {n}) {n} {an} {ad} "
                f"{a} {d} {b} {e} {bn} {bd}\n    {_lean_list(each_cuts)}\n    "
                f"{_lean_list(each_nexts)} := by\n  decide +kernel\n"
            )
            cases.append(
                f"  · exact AssociationPower.power_lt_of_fails ({r} * {n}) {n}\n      "
                + arguments.replace("\n    ", "\n      ")
                + f" _ _ smaller_{n}"
            )
        body = "\n".join(cases)
        smaller = f"""
{chr(10).join(facts)}
theorem checked_smaller (n : ℕ) (lower : {low} ≤ n) (upper : n < {second}) :
    (productBinomial ({r} * n) n {point}).real
        (fisherRejectionRegionAt ({r} * n) n declaredLevel.value) <
      {_ratio(plan.minimum_power)} := by
  interval_cases n
{body}
"""
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical planning SHA-256: {input_sha256}
-- An observational {plan.design.replace("_", "-")} study. Power is recomputed in the kernel;
-- the listed thresholds are proposals that the kernel validates against the formal p-value.
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩
-- The two groups the design fixes: (unexposed, exposed) or (controls, cases).
def firstGroup : ℕ := {first}
def secondGroup : ℕ := {second}
def cuts : List ℕ := {_lean_list(cuts)}
def nexts : List ℕ := {_lean_list(nexts)}

theorem checked_sizes : firstGroup = {first} ∧ secondGroup = {second} ∧ 0 < firstGroup ∧
    0 < secondGroup := by decide

theorem checked_region : FisherPower.HintsValid firstGroup secondGroup {an} {ad} cuts nexts := by
  decide +kernel

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw firstGroup secondGroup p).real
        (fisherRejectionRegionAt firstGroup secondGroup declaredLevel.value) ≤
      {_ratio(plan.maximum_typeI)} := by
  refine le_trans (Association.groups_typeI_le_alpha firstGroup secondGroup p
    declaredLevel.value declaredLevel.nonnegative) ?_
  norm_num [declaredLevel]

theorem checked_power :
    {_ratio(plan.minimum_power)} ≤
      (productBinomial firstGroup secondGroup {point}).real
        (fisherRejectionRegionAt firstGroup secondGroup declaredLevel.value) :=
  AssociationPower.power_of_check firstGroup secondGroup {arguments} (by
      rw [FisherPower.rejectionNumerator_hint _ _ _ _ _ _ _ _ cuts nexts checked_region]
      decide +kernel)
{smaller}
end StatClaimCertificate
{_audit(plan_theorems(plan), input_sha256)}"""


# Two-sided exact binomial tests: McNemar's test and the rate test ----------------------------
MATCHED_KIND = "statclaim_matched_planning_certificate"
RATE_KIND = "statclaim_rate_planning_certificate"
MATCHED_THEOREM = "StatClaim.Modules.BinomialPower.pairs_power_of_check"
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


def _parse_number(text: str) -> Fraction:
    """An exact positive number from a bound payload, such as an odds ratio or person-time."""
    if not isinstance(text, str) or not text.replace("/", "", 1).isdigit():
        raise ValueError("Expected an exact number written as an integer or a fraction.")
    return Fraction(text)


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


def _target(plan) -> dict:
    return {"minimum_power": str(plan.minimum_power), "maximum_typeI": str(plan.maximum_typeI)}


def _search(plan, low_key: str, high_key: str) -> dict:
    search = {low_key: plan.search[0], high_key: plan.search[1]}
    if plan.minimal:
        search["claim"] = SMALLEST
    return search


def matched_plan_payload(plan: MatchedPowerPlan) -> dict:
    test = plan.test
    payload = {
        "schema_version": 1,
        "scope": "matched_planning",
        "request": plan.request,
        "design": {
            "kind": "matched_case_control",
            "pairs": test.pairs,
            "exposure": test.exposure,
            "outcome": test.outcome,
            "stopping": "fixed",
        },
        "analysis": {
            "test": "mcnemar_exact",
            "test_version": "0.1.0",
            "null": "no_association",
            "alpha": str(test.alpha),
        },
        "target": {
            "discordant": str(plan.discordant),
            "odds_ratio": str(plan.odds_ratio),
            **_target(plan),
        },
    }
    if plan.search is not None:
        payload["search"] = _search(plan, "min_pairs", "max_pairs")
    return payload


def parse_matched_plan_payload(payload: dict) -> MatchedPowerPlan:
    design, target, search = payload["design"], payload["target"], payload.get("search")
    plan = MatchedPowerPlan(
        MatchedTest(
            design["pairs"],
            parse_alpha(payload["analysis"]["alpha"]),
            design["exposure"],
            design["outcome"],
        ),
        parse_alpha(target["discordant"]),
        _parse_number(target["odds_ratio"]),
        parse_alpha(target["minimum_power"]),
        parse_alpha(target["maximum_typeI"]),
        payload["request"],
        (search["min_pairs"], search["max_pairs"]) if search else None,
        bool(search) and search.get("claim") == SMALLEST,
    )
    if payload != matched_plan_payload(plan):
        raise ValueError("Bound planning inputs are inconsistent.")
    return plan


def rate_plan_payload(plan: RatePowerPlan) -> dict:
    test = plan.test
    payload = {
        "schema_version": 1,
        "scope": "rate_planning",
        "request": plan.request,
        "design": {
            "kind": "person_time_cohort",
            "events": plan.events,
            "exposure": test.exposure,
            "outcome": test.outcome,
            "stopping": "fixed",
        },
        "analysis": {
            "test": "rate_exact",
            "test_version": "0.1.0",
            "null": "no_association",
            "alpha": str(test.alpha),
        },
        "target": {
            "exposed_time": str(plan.exposed_time),
            "unexposed_time": str(plan.unexposed_time),
            "rate_ratio": str(plan.rate_ratio),
            **_target(plan),
        },
    }
    if plan.search is not None:
        payload["search"] = _search(plan, "min_events", "max_events")
    return payload


def parse_rate_plan_payload(payload: dict) -> RatePowerPlan:
    design, target, search = payload["design"], payload["target"], payload.get("search")
    plan = RatePowerPlan(
        RateTest(parse_alpha(payload["analysis"]["alpha"]), design["exposure"], design["outcome"]),
        *(_parse_number(target[name]) for name in ("exposed_time", "unexposed_time", "rate_ratio")),
        design["events"],
        parse_alpha(target["minimum_power"]),
        parse_alpha(target["maximum_typeI"]),
        payload["request"],
        (search["min_events"], search["max_events"]) if search else None,
        bool(search) and search.get("claim") == SMALLEST,
    )
    if payload != rate_plan_payload(plan):
        raise ValueError("Bound planning inputs are inconsistent.")
    return plan


def binomial_plan_theorems(plan) -> list[str]:
    names = ["checked_typeI", "checked_region", "checked_power"]
    return names + ["checked_smaller"] if plan.minimal else names


def _smaller_claim(plan, size: int, unit: str) -> list[str]:
    if plan.search is None:
        return []
    low, high = plan.search
    if plan.minimal:
        return [
            f"No candidate with {low} to {size - 1} {unit} reaches that power, so {size} "
            f"{unit} is the smallest sufficient candidate in the range {low} to {high}. "
            "Nothing is claimed outside the range."
        ]
    return [
        f"{size} {unit} are therefore sufficient among candidates with {low} to {high} {unit}. "
        "Minimality is not claimed."
    ]


def matched_plan_claims(plan: MatchedPowerPlan) -> list[str]:
    test = plan.test
    return [
        f"McNemar's exact test of no association between {test.exposure} and {test.outcome}, "
        f"with {test.pairs} pairs and alpha {test.alpha}, has Type I error at most "
        f"{plan.maximum_typeI} whenever {matched_null_words(test)}, for every probability that "
        "a pair is discordant.",
        f"Its power is at least {plan.minimum_power} when a pair is discordant with probability "
        f"{plan.discordant} and the conditional odds ratio is {plan.odds_ratio}.",
        *_smaller_claim(plan, test.pairs, "pairs"),
    ]


def rate_plan_claims(plan: RatePowerPlan) -> list[str]:
    test = plan.test
    return [
        f"The exact test of no association between {test.exposure} and {test.outcome}, at "
        f"alpha {test.alpha}, has Type I error at most {plan.maximum_typeI} whenever "
        f"{rate_null_words(test)}, for every common rate and any person-time.",
        f"Given {plan.events} events, its power is at least {plan.minimum_power} when the rate "
        f"ratio is {plan.rate_ratio} and {plan.share} of the person-time is exposed.",
        *_smaller_claim(plan, plan.events, "events"),
    ]


def matched_plan_assumptions(plan: MatchedPowerPlan) -> list[str]:
    return [*matched_assumptions(plan.test), PLANNING_POINT]


RATE_EVENTS = (
    "Power is given the planned total number of events; the total itself varies with the "
    "rates and the person-time."
)


def rate_plan_assumptions(plan: RatePowerPlan) -> list[str]:
    return [*rate_assumptions(plan.test), PLANNING_POINT, RATE_EVENTS]


def _level_lean(alpha: Fraction) -> str:
    an, ad = alpha.as_integer_ratio()
    return f"""def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩"""


def _binomial_header(input_sha256: str, what: str) -> str:
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical planning SHA-256: {input_sha256}
-- {what} Power is recomputed in the kernel; the listed bounds of each
-- rejection region are proposals that the kernel validates against the binomial tails.
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules
"""


def render_matched_plan_proof(plan: MatchedPowerPlan, input_sha256: str) -> str:
    """Only validated integers and rationals enter the template; names never do."""
    if not plan.typeI_target_met:
        raise ValueError("The Type I target is not established by the theorem.")
    n, alpha = plan.test.pairs, plan.test.alpha
    an, ad = alpha.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    (a, d), (b, e) = plan.discordant.as_integer_ratio(), plan.case_share.as_integer_ratio()
    lows, highs = zip(*(binomial_region(k, HALF, alpha) for k in range(n + 1)), strict=True)
    point = f"(ratPoint {a} {d} (by decide) (by decide)) (ratPoint {b} {e} (by decide) (by decide))"
    arguments = (
        f"{a} {d} {b} {e} {an} {ad} (by decide) (by decide) (by decide) (by decide) (by decide)\n"
        f"    _ (by norm_num [declaredLevel]) lows highs"
    )
    smaller = ""
    if plan.minimal:
        low = plan.search[0]
        facts, cases = [], []
        for m in range(low, n):
            # One theorem per smaller candidate, so the kernel frees each one's arithmetic.
            facts.append(
                f"theorem smaller_{m} : BinomialPower.pairsNumerator {m} {a} {d} {b} {e} lows "
                f"highs * {bd} <\n    {bn} * ({d} ^ {m} * {e} ^ {m}) := by\n  decide +kernel\n"
            )
            cases.append(
                f"  · exact BinomialPower.pairs_power_lt_of_check {m} "
                + arguments.replace("\n    ", "\n      ")
                + f"\n      (checked_region.mono (by decide)) {bn} {bd} (by decide) smaller_{m}"
            )
        smaller = f"""
{chr(10).join(facts)}
theorem checked_smaller (m : ℕ) (lower : {low} ≤ m) (upper : m < {n}) :
    (Matched.pairsLaw m {point}).real
        (Matched.pairsRejection m (declaredLevel.value : ℝ)) < {_ratio(plan.minimum_power)} := by
  interval_cases m
{chr(10).join(cases)}
"""
    return f"""{_binomial_header(input_sha256, "A 1:1 matched case-control study.")}
{_level_lean(alpha)}
-- For every number of discordant pairs up to {n}: reject below the first list's entry and
-- from the second's up.
def lows : List ℕ := {_lean_list(lows)}
def highs : List ℕ := {_lean_list(highs)}

theorem checked_typeI (δ : unitInterval) :
    (Matched.pairsLaw {n} δ Matched.half).real
        (Matched.pairsRejection {n} (declaredLevel.value : ℝ)) ≤ {_ratio(plan.maximum_typeI)} := by
  refine le_trans (Matched.typeI {n} δ _ (by exact_mod_cast declaredLevel.nonnegative)) ?_
  norm_num [declaredLevel]

theorem checked_region : BinomialPower.PairsValid {n} {an} {ad} lows highs := by
  decide +kernel

theorem checked_power :
    {_ratio(plan.minimum_power)} ≤ (Matched.pairsLaw {n} {point}).real
        (Matched.pairsRejection {n} (declaredLevel.value : ℝ)) :=
  BinomialPower.pairs_power_of_check {n} {arguments} checked_region
    {bn} {bd} (by decide) (by decide +kernel)
{smaller}
end StatClaimCertificate
{_audit(binomial_plan_theorems(plan), input_sha256)}"""


def render_rate_plan_proof(plan: RatePowerPlan, input_sha256: str) -> str:
    """Only validated integers and rationals enter the template; names never do."""
    if not plan.typeI_target_met:
        raise ValueError("The Type I target is not established by the theorem.")
    n, alpha = plan.events, plan.test.alpha
    an, ad = alpha.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    (a, d), (c, f) = plan.event_share.as_integer_ratio(), plan.share.as_integer_ratio()
    low, high = binomial_region(n, plan.share, alpha)
    alternative = f"(ratPoint {a} {d} (by decide) (by decide))"
    null = f"(ratPoint {c} {f} (by decide) (by decide))"
    arguments = (
        f"{a} {d} {c} {f} {an} {ad} {low} {high}"
        f" (by decide) (by decide) (by decide) (by decide) (by decide)\n"
        f"    _ (by norm_num [declaredLevel])"
    )
    smaller = ""
    if plan.minimal:
        first = plan.search[0]
        facts, cases = [], []
        for m in range(first, n):
            m_low, m_high = binomial_region(m, plan.share, alpha)
            facts.append(
                f"theorem smaller_{m} : BinomialPower.RegionValid {m} {c} {f} {an} {ad} {m_low} "
                f"{m_high} ∧\n    BinomialPower.regionNumerator {m} {a} {d} {m_low} {m_high} "
                f"* {bd} < {bn} * {d} ^ {m} := by\n  decide +kernel\n"
            )
            cases.append(
                f"  · exact BinomialPower.power_lt_of_check {m} {a} {d} {c} {f} {an} {ad} "
                f"{m_low} {m_high}\n      (by decide) (by decide) (by decide) (by decide) "
                f"(by decide) _ (by norm_num [declaredLevel])\n      smaller_{m}.1 {bn} {bd} "
                f"(by decide) smaller_{m}.2"
            )
        smaller = f"""
{chr(10).join(facts)}
theorem checked_smaller (m : ℕ) (lower : {first} ≤ m) (upper : m < {n}) :
    (ProbabilityTheory.binomial m {alternative}).real
        (Incidence.rejectionAt {null} m (declaredLevel.value : ℝ)) <
      {_ratio(plan.minimum_power)} := by
  interval_cases m
{chr(10).join(cases)}
"""
    return f"""{_binomial_header(input_sha256, "A cohort followed over person-time.")}
{_level_lean(alpha)}

-- For every total rate and every share of person-time, under equal rates.
theorem checked_typeI (total : NNReal) (share : unitInterval) :
    (Incidence.ratesLaw total share).real
        (Incidence.given (fun n => Incidence.rejectionAt share n (declaredLevel.value : ℝ))) ≤
      {_ratio(plan.maximum_typeI)} := by
  refine le_trans (Incidence.typeI total share _
    (by exact_mod_cast declaredLevel.nonnegative)) ?_
  norm_num [declaredLevel]

-- Given {n} events, with {c}/{f} of the person-time exposed: reject below {low} and from {high} up.
theorem checked_region : BinomialPower.RegionValid {n} {c} {f} {an} {ad} {low} {high} := by
  decide +kernel

theorem checked_power :
    {_ratio(plan.minimum_power)} ≤ (ProbabilityTheory.binomial {n} {alternative}).real
        (Incidence.rejectionAt {null} {n} (declaredLevel.value : ℝ)) :=
  BinomialPower.power_of_check {n} {arguments} checked_region
    {bn} {bd} (by decide) (by decide +kernel)
{smaller}
end StatClaimCertificate
{_audit(binomial_plan_theorems(plan), input_sha256)}"""


# Designs that fix only the total -------------------------------------------------------------
TOTAL_KIND = "statclaim_total_planning_certificate"
TOTAL_THEOREM = "StatClaim.Modules.AssociationPower.total_power_of_check"
TOTAL_THEOREMS = ["checked_size", "checked_parts", "checked_typeI", "checked_power"]
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


def total_plan_payload(plan: TotalPowerPlan) -> dict:
    test = plan.test
    first_key, second_key = TOTAL_POINT_KEYS[plan.design]
    payload = {
        "schema_version": 1,
        "scope": "total_planning",
        "request": plan.request,
        "design": {
            "kind": test.design,
            "n": test.n,
            "exposure": test.exposure,
            "outcome": test.outcome,
            "stopping": "fixed",
        },
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": "no_association",
            "alpha": str(test.alpha),
        },
        "target": {
            "exposed_share": str(plan.exposed_share),
            first_key: str(plan.p_first),
            second_key: str(plan.p_second),
            **_target(plan),
        },
    }
    if plan.search is not None:
        payload["search"] = {"min_n": plan.search[0], "max_n": plan.search[1]}
    return payload


def parse_total_plan_payload(payload: dict) -> TotalPowerPlan:
    design, target, search = payload["design"], payload["target"], payload.get("search")
    kind = design["kind"]
    if kind not in TOTAL_POINT_KEYS:
        raise ValueError("Unsupported design for exact power with only the total fixed.")
    first_key, second_key = TOTAL_POINT_KEYS[kind]
    plan = TotalPowerPlan(
        AssociationTest(
            kind,
            parse_alpha(payload["analysis"]["alpha"]),
            None,
            design["n"],
            design["exposure"],
            design["outcome"],
        ),
        *(
            parse_alpha(target[name])
            for name in (first_key, second_key, "exposed_share", "minimum_power", "maximum_typeI")
        ),
        payload["request"],
        (search["min_n"], search["max_n"]) if search else None,
    )
    if payload != total_plan_payload(plan):
        raise ValueError("Bound planning inputs are inconsistent.")
    return plan


def total_point_words(test: AssociationTest, p_first, p_second, share) -> str:
    noun = "risk" if test.design == "cohort" else "prevalence"
    return (
        f"{share} of participants are exposed to {test.exposure} and the {noun} of "
        f"{test.outcome} is {p_second} with it and {p_first} without it"
    )


def total_plan_claims(plan: TotalPowerPlan) -> list[str]:
    test = plan.test
    kind = "cross-sectional sample" if plan.design == "cross_sectional" else "cohort"
    claims = [
        f"Fisher's exact test of no association between {test.exposure} and {test.outcome}, "
        f"in a {kind} of {test.n} with alpha {test.alpha}, has Type I error at most "
        f"{plan.maximum_typeI} whenever {null_words(test)}, for every probability of exposure "
        f"and every common probability of {test.outcome}, averaged over the number exposed.",
        f"Its power is at least {plan.minimum_power} when "
        f"{total_point_words(test, plan.p_first, plan.p_second, plan.exposed_share)}, averaged "
        "over the number exposed.",
    ]
    if plan.search is not None:
        low, high = plan.search
        claims.append(
            f"A total of {test.n} is therefore sufficient among totals from {low} to {high}. "
            "Minimality is not claimed."
        )
    return claims


def total_plan_assumptions(plan: TotalPowerPlan) -> list[str]:
    return [*association_assumptions(plan.test), PLANNING_POINT]


def render_total_plan_proof(plan: TotalPowerPlan, input_sha256: str) -> str:
    """One theorem for each number exposed, so the kernel frees each one's tables before the
    next. Only validated integers and rationals enter the template; names never do."""
    if not plan.typeI_target_met:
        raise ValueError("The Type I target is not established by the theorem.")
    n, alpha = plan.test.n, plan.test.alpha
    an, ad = alpha.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    (q, r) = plan.exposed_share.as_integer_ratio()
    (a, d), (b, e) = plan.p_first.as_integer_ratio(), plan.p_second.as_integer_ratio()
    hints = [fisher_cuts(n - k, k, alpha) for k in range(n + 1)]
    numerators = [int(part) for part in plan.parts()]
    parts = "\n".join(
        f"theorem part_{k} : AssociationPower.PartValid {n} {k} {an} {ad} {a} {d} {b} {e}\n"
        f"    (cutsList.getD {k} []) (nextsList.getD {k} []) (numerators.getD {k} 0) := by\n"
        "  decide +kernel\n"
        for k in range(n + 1)
    )
    cases = "\n".join(f"  · exact part_{k}" for k in range(n + 1))
    share = f"(ratPoint {q} {r} (by decide) (by decide))"
    groups = (
        f"(ratPoint {a} {d} (by decide) (by decide)) (ratPoint {b} {e} (by decide) (by decide))"
    )
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical planning SHA-256: {input_sha256}
-- An observational design that fixes only its total, {n}. For each number exposed the kernel
-- recomputes Fisher's region from the formal p-value; listed thresholds are proposals.
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩
def sampleSize : ℕ := {n}
def cutsList : List (List ℕ) := {_lean_list(_lean_list(c) for c, _ in hints)}
def nextsList : List (List ℕ) := {_lean_list(_lean_list(x) for _, x in hints)}
def numerators : List ℕ := {_lean_list(numerators)}

theorem checked_size : sampleSize = {n} ∧ 0 < sampleSize := by decide

{parts}
theorem checked_parts (k : ℕ) (below : k < {n} + 1) :
    AssociationPower.PartValid {n} k {an} {ad} {a} {d} {b} {e} (cutsList.getD k [])
      (nextsList.getD k []) (numerators.getD k 0) := by
  interval_cases k
{cases}

theorem checked_typeI (q p : unitInterval) :
    (Association.mixtureLaw sampleSize q p).real
        (Association.mixtureRejection sampleSize declaredLevel.value) ≤
      {_ratio(plan.maximum_typeI)} := by
  refine le_trans (Association.mixture_typeI_le_alpha sampleSize q p declaredLevel.value
    declaredLevel.nonnegative) ?_
  norm_num [declaredLevel]

theorem checked_power :
    {_ratio(plan.minimum_power)} ≤
      (Association.mixture {n} {share}
        (fun k => productBinomial ({n} - k) k {groups})).real
        (Association.mixtureRejection {n} declaredLevel.value) :=
  AssociationPower.total_power_of_check {n} {q} {r} {a} {d} {b} {e} {an} {ad}
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    declaredLevel.value (by norm_num [declaredLevel]) cutsList nextsList numerators checked_parts
    {bn} {bd} (by decide) (by decide +kernel)

end StatClaimCertificate
{_audit(TOTAL_THEOREMS, input_sha256)}"""
