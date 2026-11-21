"""Exact power of Fisher's test of no association in an observational study.

A cohort that sampled its exposed and unexposed groups, or a case-control study, fixes two
group sizes. The table then holds two independent binomial counts, each with its own
probability: the risk of the outcome in each group of a cohort, or the probability of
exposure among controls and among cases. At a planning point those probabilities are
declared, and power is the exact probability that Fisher's test rejects.

Calculations use integers and fractions only. A certificate proposes nothing that Lean
trusts: the kernel recomputes the rejection region from the formal p-value
(StatClaim.Modules.AssociationPower). Power at a planning point says nothing about other
points, and nothing about an effect of the exposure.
"""

from dataclasses import dataclass
from fractions import Fraction
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
