"""Exact planning calculations and the Lean claims generated for them.

Calculations use integers and fractions only. They propose nothing to Lean:
each generated proof recomputes the rejection probability in the kernel from
the formal definitions. Power at a planning point is not a guarantee at other
alternatives, and a sufficient sample size is not claimed to be the smallest.
"""

import re
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb
from typing import Literal

from statproof.design import Design
from statproof.fisher import TEST_ID, TEST_VERSION, fraction_record, parse_alpha

SMALLEST = "smallest_in_range"
PLANNING_KIND = "statproof_planning_certificate"
POLICY_KIND = "statproof_policy_certificate"


def planning_theorems(plan) -> list[str]:
    names = ["checked_sizes", "checked_region", "checked_typeI", "checked_power"]
    return names + ["checked_smaller"] if plan.minimal else names


def policy_theorems(plan) -> list[str]:
    names = ["checked_stages", "checked_typeI", "checked_power"]
    if getattr(plan, "minimal", False):
        names += ["checked_critical", "checked_smaller"]
    return names


# Kernel checking enumerates every table; larger searches remain calculations.
MAX_PER_ARM = 500
MAX_STAGE = 200
MAX_ONE_ARM = 1000

AUDIT = """
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[{names}] do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {{theoremName}}"
    for dependency in ← collectAxioms theoremName do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {{dependency}} in {{theoremName}}"
  logInfo "STATPROOF_CHECKED {input_sha256}"
"""


def _audit(theorems: list[str], input_sha256: str) -> str:
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    names = ",\n    ".join(f"``StatProofCertificate.{name}" for name in theorems)
    return AUDIT.format(names=names, input_sha256=input_sha256)


def _probability(value: Fraction, name: str) -> None:
    if not isinstance(value, Fraction) or not 0 <= value <= 1:
        raise ValueError(f"{name} must be an exact Fraction between zero and one.")


def _weights(n: int, rate: Fraction) -> list[int]:
    """Integer numerators of binomial point masses; the denominator is den ** n."""
    a, d = rate.as_integer_ratio()
    return [comb(n, k) * a**k * (d - a) ** (n - k) for k in range(n + 1)]


def _table_weights(n_control: int, n_treatment: int, total: int) -> tuple[int, list[int]]:
    lower, upper = max(0, total - n_treatment), min(n_control, total)
    return lower, [
        comb(n_control, k) * comb(n_treatment, total - k) for k in range(lower, upper + 1)
    ]


@lru_cache(maxsize=256)
def fisher_cuts(
    n_control: int, n_treatment: int, alpha: Fraction
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """For each pooled total: the largest rejected table weight and the next larger
    weight, with zero for "none". Lean validates these; they are not trusted."""
    an, ad = alpha.as_integer_ratio()
    cuts, nexts = [], []
    for total in range(n_control + n_treatment + 1):
        _, weights = _table_weights(n_control, n_treatment, total)
        limit = an * comb(n_control + n_treatment, total)
        cut = following = cumulative = 0
        for weight in sorted(set(weights)):
            cumulative += weight * weights.count(weight)
            if cumulative * ad <= limit:
                cut = weight
            else:
                following = weight
                break
        cuts.append(cut)
        nexts.append(following)
    return tuple(cuts), tuple(nexts)


@lru_cache(maxsize=256)
def fisher_rejection_region(
    n_control: int, n_treatment: int, alpha: Fraction
) -> tuple[tuple[bool, ...], ...]:
    """Whether each table (control successes, treatment successes) is rejected."""
    cuts, _ = fisher_cuts(n_control, n_treatment, alpha)
    region = [[False] * (n_treatment + 1) for _ in range(n_control + 1)]
    for total, cut in enumerate(cuts):
        lower, weights = _table_weights(n_control, n_treatment, total)
        for offset, weight in enumerate(weights):
            region[lower + offset][total - lower - offset] = weight <= cut
    return tuple(tuple(row) for row in region)


def fisher_rejection_probability(
    n_control: int, n_treatment: int, alpha: Fraction, p_control: Fraction, p_treatment: Fraction
) -> Fraction:
    """Exact probability that the fixed-sample Fisher test rejects at these rates."""
    region = fisher_rejection_region(n_control, n_treatment, alpha)
    control, treatment = _weights(n_control, p_control), _weights(n_treatment, p_treatment)
    numerator = sum(
        control[x] * sum(treatment[y] for y in range(n_treatment + 1) if region[x][y])
        for x in range(n_control + 1)
    )
    return Fraction(
        numerator, p_control.denominator**n_control * p_treatment.denominator**n_treatment
    )


@dataclass(frozen=True)
class PowerPlan:
    """A fixed Fisher design assessed against one planning point."""

    design: Design
    p_control: Fraction
    p_treatment: Fraction
    minimum_power: Fraction
    maximum_typeI: Fraction
    request: Literal["meets", "sample_size"] = "meets"
    search: tuple[int, int] | None = None
    minimal: bool = False

    def __post_init__(self) -> None:
        if self.minimal and self.search is None:
            raise ValueError("A smallest-size claim needs a search range.")
        for name in ("p_control", "p_treatment", "minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        if self.p_control == self.p_treatment:
            raise ValueError("The planning point must lie outside the equal-proportions null.")
        if (self.request == "sample_size") != (self.search is not None):
            raise ValueError("Search bounds accompany exactly the sample_size request.")
        if self.search is not None:
            low, high = self.search
            if type(low) is not int or type(high) is not int or not 1 <= low <= high:
                raise ValueError("Search bounds must be integers with 1 <= min <= max.")
            if not (low <= self.design.n_control <= high and self.equal_arms):
                raise ValueError("The certified design must be a candidate of the search.")

    @property
    def equal_arms(self) -> bool:
        return self.design.n_control == self.design.n_treatment

    @property
    def power(self) -> Fraction:
        return fisher_rejection_probability(
            self.design.n_control,
            self.design.n_treatment,
            self.design.alpha,
            self.p_control,
            self.p_treatment,
        )

    @property
    def typeI_target_met(self) -> bool:
        """The Fisher theorem bounds Type I error by alpha; nothing tighter is used."""
        return self.design.alpha <= self.maximum_typeI

    def evaluate(self) -> dict:
        power = self.power
        return {
            "n_control": self.design.n_control,
            "n_treatment": self.design.n_treatment,
            "total_sample_size": self.design.n_control + self.design.n_treatment,
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
            "typeI_bound": fraction_record(self.design.alpha),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": self.typeI_target_met,
        }


def search_equal_arms(
    alpha: Fraction,
    p_control: Fraction,
    p_treatment: Fraction,
    minimum_power: Fraction,
    maximum_typeI: Fraction,
    low: int,
    high: int,
    minimal: bool = False,
) -> tuple[PowerPlan | None, int]:
    """First equal-arm size in ascending order meeting the power target.

    Power is not assumed monotone in sample size; each candidate is evaluated.
    """
    for evaluated, size in enumerate(range(low, high + 1), 1):
        plan = PowerPlan(
            Design(size, size, "fixed", alpha),
            p_control,
            p_treatment,
            minimum_power,
            maximum_typeI,
            "sample_size",
            (low, high),
            minimal,
        )
        if plan.power >= minimum_power:
            return plan, evaluated
    return None, high - low + 1


def planning_payload(plan: PowerPlan) -> dict:
    if plan.design.stopping != "fixed":
        raise ValueError("A planning certificate requires fixed sampling.")
    payload = {
        "schema_version": 1,
        "scope": "planning",
        "request": plan.request,
        "design": {
            "module": "two_arm_binomial",
            "n_control": plan.design.n_control,
            "n_treatment": plan.design.n_treatment,
            "stopping": "fixed",
        },
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": "equal_proportions",
            "alpha": str(plan.design.alpha),
        },
        "target": {
            "p_control": str(plan.p_control),
            "p_treatment": str(plan.p_treatment),
            "minimum_power": str(plan.minimum_power),
            "maximum_typeI": str(plan.maximum_typeI),
        },
    }
    if plan.search is not None:
        payload["search"] = {"min_per_arm": plan.search[0], "max_per_arm": plan.search[1]}
        if plan.minimal:
            payload["search"]["claim"] = SMALLEST
    return payload


def parse_planning_payload(payload: dict) -> PowerPlan:
    design, target, search = payload["design"], payload["target"], payload.get("search")
    plan = PowerPlan(
        Design(
            design["n_control"],
            design["n_treatment"],
            design["stopping"],
            parse_alpha(payload["analysis"]["alpha"]),
        ),
        *(
            parse_alpha(target[name])
            for name in ("p_control", "p_treatment", "minimum_power", "maximum_typeI")
        ),
        payload["request"],
        (search["min_per_arm"], search["max_per_arm"]) if search else None,
        bool(search) and search.get("claim") == SMALLEST,
    )
    if payload != planning_payload(plan):
        raise ValueError("Bound planning inputs are inconsistent.")
    return plan


def planning_claims(plan: PowerPlan) -> list[str]:
    sizes = f"({plan.design.n_control}, {plan.design.n_treatment})"
    claims = [
        f"The two-sided Fisher analysis with arm sizes {sizes} and alpha {plan.design.alpha} "
        f"has Type I error at most {plan.maximum_typeI} under the null, for every common "
        "success probability in [0, 1].",
        f"Its power is at least {plan.minimum_power} at p_control = {plan.p_control}, "
        f"p_treatment = {plan.p_treatment}.",
    ]
    if plan.minimal:
        claims.append(
            f"No equal-arm size from {plan.search[0]} up to {plan.design.n_control - 1} reaches "
            f"that power, so {sizes} is the smallest sufficient candidate in the range "
            f"{plan.search[0]} to {plan.search[1]}. Nothing is claimed outside the range."
        )
    elif plan.search is not None:
        claims.append(
            f"Arm sizes {sizes} are therefore sufficient among equal-arm candidates "
            f"{plan.search[0]} to {plan.search[1]}. Minimality is not claimed."
        )
    return claims


PLANNING_ASSUMPTIONS = [
    "The samples follow two independent binomial distributions.",
    "Positive arm sizes were fixed before outcomes were observed.",
    "The error bound is under the null of equal success probabilities, for every p in [0, 1].",
    "Power is evaluated at the declared planning point only; "
    "the point is a planning input, not an established fact.",
]


def _lean_list(values) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def render_planning_proof(plan: PowerPlan, input_sha256: str) -> str:
    if not plan.typeI_target_met or plan.design.stopping != "fixed":
        raise ValueError("The Type I target is not established by the Fisher theorem.")
    nc, nt = plan.design.n_control, plan.design.n_treatment
    alpha = plan.design.alpha
    an, ad = alpha.as_integer_ratio()
    mn, md = plan.maximum_typeI.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    (a, d), (b, e) = plan.p_control.as_integer_ratio(), plan.p_treatment.as_integer_ratio()
    cuts, nexts = fisher_cuts(nc, nt, alpha)
    point = f"{a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide)"
    smaller = ""
    if plan.minimal:
        low = plan.search[0]
        hints = [fisher_cuts(n, n, alpha) for n in range(low, nc)]
        smaller = f"""
def smallerCuts : List (List ℕ) := {_lean_list(_lean_list(c) for c, _ in hints)}
def smallerNexts : List (List ℕ) := {_lean_list(_lean_list(x) for _, x in hints)}

theorem checked_smaller (n : ℕ) (positive : 0 < n) (lower : {low} ≤ n) (upper : n < {nc}) :
    ((Core.Policy.fixed (TwoArmBinomial.model ⟨n, n, positive, positive⟩)).law
        planningPoint).real
        (FisherPower.analysis ⟨n, n, positive, positive⟩ declaredLevel).rejection <
      ((({bn} : ℕ) : ℝ) / (({bd} : ℕ) : ℝ)) :=
  FisherPower.power_lt_of_smallerFail declaredLevel {an} {ad} (by decide)
    (by norm_num [declaredLevel]) {point} {bn} {bd} (by decide) {low} {nc}
    (FisherPower.smallerFail_of_hinted _ _ _ _ _ _ _ _ _ _ smallerCuts smallerNexts
      (by decide +kernel)) n positive lower upper
"""
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical planning SHA-256: {input_sha256}
-- Power is recomputed in the kernel. The listed thresholds are proposals that
-- the kernel validates against the formal p-value; they are not trusted.
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace StatProofCertificate
open StatProof StatProof.Modules

def declaredSizes : FixedSampleDesign := ⟨{nc}, {nt}, by decide, by decide⟩
def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := FisherPower.analysis declaredSizes declaredLevel
noncomputable def planningPoint : TwoArmBinomial.Parameters :=
  FisherPower.ratePoint {point}
def cuts : List ℕ := {_lean_list(cuts)}
def nexts : List ℕ := {_lean_list(nexts)}

theorem checked_sizes : declaredSizes.nControl = {nc} ∧ declaredSizes.nTreatment = {nt} ∧
    0 < declaredSizes.nControl ∧ 0 < declaredSizes.nTreatment := by decide

theorem checked_region : FisherPower.HintsValid declaredSizes.nControl
    declaredSizes.nTreatment {an} {ad} cuts nexts := by
  decide +kernel

theorem checked_typeI :
    (declaredAnalysis.typeIClaim ((({mn} : ℕ) : ℝ) / (({md} : ℕ) : ℝ))).statement := by
  intro parameter null
  refine le_trans (FisherPower.typeI_statement declaredSizes declaredLevel parameter null) ?_
  norm_num [declaredLevel]

theorem checked_power :
    (declaredAnalysis.powerClaim (fun parameter => parameter = planningPoint)
      ((({bn} : ℕ) : ℝ) / (({bd} : ℕ) : ℝ))).statement :=
  FisherPower.power_of_check declaredSizes declaredLevel {an} {ad} (by decide)
    (by norm_num [declaredLevel]) {point}
    {bn} {bd} (by decide) (by
      rw [FisherPower.rejectionNumerator_hint _ _ _ _ _ _ _ _ cuts nexts checked_region]
      decide +kernel)
{smaller}
end StatProofCertificate
{_audit(planning_theorems(plan), input_sha256)}"""


@dataclass(frozen=True)
class TwoStageRule:
    """Interim continuation and final rejection rules of a two-stage design."""

    kind: Literal["threshold", "posterior"]
    continue_above: int = 0
    reject_above: int = 0
    prior_a: int = 1
    prior_b: int = 1
    reference: Fraction = Fraction(1, 2)
    continue_at_least: Fraction = Fraction(0)
    success_at_least: Fraction = Fraction(1)

    def __post_init__(self) -> None:
        if self.kind not in ("threshold", "posterior"):
            raise ValueError("Unsupported two-stage rule.")
        for name in ("continue_above", "reject_above"):
            if type(getattr(self, name)) is not int or getattr(self, name) < 0:
                raise ValueError(f"{name} must be a nonnegative integer.")
        for name in ("prior_a", "prior_b"):
            if type(getattr(self, name)) is not int or getattr(self, name) < 1:
                raise ValueError(f"{name} must be a positive integer.")
        for name in ("reference", "continue_at_least", "success_at_least"):
            _probability(getattr(self, name), name)

    def posterior_at_least(self, level: Fraction, successes: int, trials: int) -> bool:
        """Posterior P(rate > reference) >= level, by the binomial form of the Beta tail."""
        a, b = self.prior_a + successes, self.prior_b + trials - successes
        rn, rd = self.reference.as_integer_ratio()
        tail = sum(comb(a + b - 1, j) * rn**j * (rd - rn) ** (a + b - 1 - j) for j in range(a))
        return level.numerator * rd ** (a + b - 1) <= tail * level.denominator

    def to_dict(self) -> dict:
        if self.kind == "threshold":
            return {
                "kind": "threshold",
                "continue_above": self.continue_above,
                "reject_above": self.reject_above,
            }
        return {
            "kind": "posterior",
            "prior_a": self.prior_a,
            "prior_b": self.prior_b,
            "reference": str(self.reference),
            "continue_at_least": str(self.continue_at_least),
            "success_at_least": str(self.success_at_least),
        }

    @staticmethod
    def from_dict(record: dict) -> "TwoStageRule":
        if record["kind"] == "threshold":
            return TwoStageRule("threshold", record["continue_above"], record["reject_above"])
        return TwoStageRule(
            "posterior",
            prior_a=record["prior_a"],
            prior_b=record["prior_b"],
            reference=parse_alpha(record["reference"]),
            continue_at_least=parse_alpha(record["continue_at_least"]),
            success_at_least=parse_alpha(record["success_at_least"]),
        )


@dataclass(frozen=True)
class TwoStagePlan:
    """A complete two-stage policy assessed at a null and an alternative rate."""

    n_first: int
    n_second: int
    rule: TwoStageRule
    null_rate: Fraction
    alternative_rate: Fraction
    minimum_power: Fraction
    maximum_typeI: Fraction

    def __post_init__(self) -> None:
        for name in ("n_first", "n_second"):
            if type(getattr(self, name)) is not int or not 1 <= getattr(self, name) <= MAX_STAGE:
                raise ValueError(f"{name} must be an integer between 1 and {MAX_STAGE}.")
        for name in ("null_rate", "alternative_rate", "minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        if self.null_rate == self.alternative_rate:
            raise ValueError("The alternative rate must differ from the null rate.")
        if self.rule.kind == "threshold" and self.alternative_rate < self.null_rate:
            raise ValueError("The alternative rate must exceed the null rate.")

    def continues(self, first: int) -> bool:
        if self.rule.kind == "threshold":
            return first > self.rule.continue_above
        return self.rule.posterior_at_least(self.rule.continue_at_least, first, self.n_first)

    def rejects(self, first: int, second: int) -> bool:
        if self.rule.kind == "threshold":
            return first + second > self.rule.reject_above
        return self.rule.posterior_at_least(
            self.rule.success_at_least, first + second, self.n_first + self.n_second
        )

    def continuation_probability(self, rate: Fraction) -> Fraction:
        first = _weights(self.n_first, rate)
        return Fraction(
            sum(first[x] for x in range(self.n_first + 1) if self.continues(x)),
            rate.denominator**self.n_first,
        )

    def rejection_probability(self, rate: Fraction) -> Fraction:
        first, second = _weights(self.n_first, rate), _weights(self.n_second, rate)
        numerator = sum(
            first[x] * sum(second[y] for y in range(self.n_second + 1) if self.rejects(x, y))
            for x in range(self.n_first + 1)
            if self.continues(x)
        )
        return Fraction(numerator, rate.denominator ** (self.n_first + self.n_second))

    def expected_sample_size(self, rate: Fraction) -> Fraction:
        return self.n_first + self.n_second * self.continuation_probability(rate)

    def evaluate(self) -> dict:
        typeI = self.rejection_probability(self.null_rate)
        power = self.rejection_probability(self.alternative_rate)
        return {
            "n_stage1": self.n_first,
            "n_stage2": self.n_second,
            "maximum_sample_size": self.n_first + self.n_second,
            "typeI": fraction_record(typeI),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": typeI <= self.maximum_typeI,
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
            "expected_sample_size_null": fraction_record(self.expected_sample_size(self.null_rate)),
            "expected_sample_size_alternative": fraction_record(
                self.expected_sample_size(self.alternative_rate)
            ),
            "early_stop_probability_null": fraction_record(
                1 - self.continuation_probability(self.null_rate)
            ),
        }


@dataclass(frozen=True)
class OneSamplePlan:
    """One-sided exact binomial test: reject when responses reach the critical value."""

    n: int
    null_rate: Fraction
    alpha: Fraction
    alternative_rate: Fraction
    minimum_power: Fraction
    maximum_typeI: Fraction
    search: tuple[int, int] | None = None
    minimal: bool = False

    def __post_init__(self) -> None:
        if self.minimal and self.search is None:
            raise ValueError("A smallest-size claim needs a search range.")
        if type(self.n) is not int or not 1 <= self.n <= MAX_ONE_ARM:
            raise ValueError(f"n must be an integer between 1 and {MAX_ONE_ARM}.")
        for name in ("null_rate", "alpha", "alternative_rate", "minimum_power", "maximum_typeI"):
            _probability(getattr(self, name), name)
        if self.alternative_rate <= self.null_rate:
            raise ValueError("The alternative rate must exceed the null rate.")
        if self.search is not None:
            low, high = self.search
            if type(low) is not int or type(high) is not int or not 1 <= low <= self.n <= high:
                raise ValueError("The certified design must be a candidate of the search.")

    def tail(self, rate: Fraction, critical: int) -> Fraction:
        return Fraction(sum(_weights(self.n, rate)[critical:]), rate.denominator**self.n)

    @property
    def critical(self) -> int:
        """Smallest response count whose upper tail at the null rate is at most alpha."""
        weights = _weights(self.n, self.null_rate)
        limit = self.alpha * self.null_rate.denominator**self.n
        tail, critical = 0, self.n + 1
        while critical > 0 and tail + weights[critical - 1] <= limit:
            critical -= 1
            tail += weights[critical]
        return critical

    def rejection_probability(self, rate: Fraction) -> Fraction:
        return self.tail(rate, self.critical)

    def evaluate(self) -> dict:
        typeI = self.rejection_probability(self.null_rate)
        power = self.rejection_probability(self.alternative_rate)
        return {
            "n": self.n,
            "critical_value": self.critical,
            "typeI": fraction_record(typeI),
            "maximum_typeI": fraction_record(self.maximum_typeI),
            "typeI_target_met": typeI <= self.maximum_typeI,
            "power": fraction_record(power),
            "minimum_power": fraction_record(self.minimum_power),
            "power_target_met": power >= self.minimum_power,
        }


def search_one_sample(
    template: OneSamplePlan, low: int, high: int, minimal: bool = False
) -> tuple[OneSamplePlan | None, int]:
    """First sample size in ascending order meeting both targets; each is evaluated."""
    for evaluated, n in enumerate(range(low, high + 1), 1):
        plan = OneSamplePlan(
            n,
            template.null_rate,
            template.alpha,
            template.alternative_rate,
            template.minimum_power,
            template.maximum_typeI,
            (low, high),
            minimal,
        )
        values = plan.evaluate()
        if values["power_target_met"] and values["typeI_target_met"]:
            return plan, evaluated
    return None, high - low + 1


RESULT_KIND = "statproof_binomial_result_certificate"
RESULT_CHECKED_THEOREMS = [
    "checked_p_value",
    "checked_critical",
    "checked_decision",
    "checked_typeI",
]


@dataclass(frozen=True)
class OneSampleResult:
    """An observed response count analysed by the one-sided exact binomial test."""

    n: int
    null_rate: Fraction
    alpha: Fraction
    responses: int

    def __post_init__(self) -> None:
        if type(self.n) is not int or not 1 <= self.n <= MAX_ONE_ARM:
            raise ValueError(f"n must be an integer between 1 and {MAX_ONE_ARM}.")
        if type(self.responses) is not int or not 0 <= self.responses <= self.n:
            raise ValueError("responses must be an integer between 0 and n.")
        _probability(self.null_rate, "null_rate")
        _probability(self.alpha, "alpha")

    @property
    def _test(self) -> OneSamplePlan:
        return OneSamplePlan(
            self.n, self.null_rate, self.alpha, Fraction(1), Fraction(0), self.alpha
        )

    @property
    def critical(self) -> int:
        return self._test.critical

    @property
    def p_value(self) -> Fraction:
        return self._test.tail(self.null_rate, self.responses)

    @property
    def reject_null(self) -> bool:
        return self.responses >= self.critical

    def evaluate(self) -> dict:
        return {
            "test": "binomial_exact_one_sided",
            "n": self.n,
            "responses": self.responses,
            "critical_value": self.critical,
            "p_value": fraction_record(self.p_value),
            "alpha": fraction_record(self.alpha),
            "reject_null": self.reject_null,
        }


def result_payload(result: OneSampleResult) -> dict:
    return {
        "schema_version": 1,
        "scope": "result",
        "design": {
            "module": "one_sample_binomial",
            "module_version": "0.1.0",
            "n": result.n,
            "critical_value": result.critical,
        },
        "analysis": {
            "null_rate": str(result.null_rate),
            "alpha": str(result.alpha),
            "alternative": "greater",
        },
        "result": {
            "responses": result.responses,
            "p_value": str(result.p_value),
            "reject_null": result.reject_null,
        },
    }


def parse_result_payload(payload: dict) -> OneSampleResult:
    result = OneSampleResult(
        payload["design"]["n"],
        parse_alpha(payload["analysis"]["null_rate"]),
        parse_alpha(payload["analysis"]["alpha"]),
        payload["result"]["responses"],
    )
    if payload != result_payload(result):
        raise ValueError("Bound result inputs are inconsistent.")
    return result


def result_claims(result: OneSampleResult) -> list[str]:
    decision = "reject the null" if result.reject_null else "do not reject the null"
    return [
        f"The exact one-sided p-value for {result.responses} responses out of {result.n} "
        f"at the null rate {result.null_rate} is {result.p_value} "
        f"(approximately {float(result.p_value):.4g}).",
        f"The test at level {result.alpha} rejects at {result.critical} or more responses, "
        f"so the decision is: {decision}.",
        f"That test rejects with probability at most {result.alpha} for every response rate "
        f"at or below {result.null_rate}.",
    ]


RESULT_ASSUMPTIONS = [
    "Responses are independent with one common response rate.",
    "The sample size, null rate and level were fixed before outcomes were observed.",
    "The supplied count describes the declared study.",
]


def render_result_proof(result: OneSampleResult, input_sha256: str) -> str:
    n, k, c = result.n, result.responses, result.critical
    a, d = result.null_rate.as_integer_ratio()
    an, ad = result.alpha.as_integer_ratio()
    pn, pd = result.p_value.as_integer_ratio()
    decision = f"{c} ≤ {k}" if result.reject_null else f"¬ {c} ≤ {k}"
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical result SHA-256: {input_sha256}
-- The proposed p-value is confirmed by the kernel against the formal definition.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatProofCertificate
open StatProof StatProof.Modules

theorem checked_p_value :
    ((OneSampleBinomial.policy ⟨{n}, {k}⟩).law (ratPoint {a} {d} (by decide) (by decide))).real
        {{count | {k} ≤ count}} = ((({pn} : ℕ) : ℝ) / (({pd} : ℕ) : ℝ)) :=
  OneSampleBinomial.pValue_eq_of_cross_product {n} {k} {a} {d} (by decide) (by decide)
    {pn} {pd} (by decide) (by decide +kernel)

theorem checked_critical :
    OneSampleBinomial.criticalValue {n} {a} {d} {an} {ad} = {c} := by decide +kernel

theorem checked_decision : {decision} := by decide

theorem checked_typeI :
    ((OneSampleBinomial.analysis ⟨{n}, {c}⟩ (ratPoint {a} {d} (by decide) (by decide))).typeIClaim
      ((({an} : ℕ) : ℝ) / (({ad} : ℕ) : ℝ))).statement :=
  OneSampleBinomial.typeI_of_check ⟨{n}, {c}⟩ {a} {d} (by decide) (by decide)
    {an} {ad} (by decide) (by decide +kernel)

end StatProofCertificate
{_audit(RESULT_CHECKED_THEOREMS, input_sha256)}"""


def policy_payload(plan: "TwoStagePlan | OneSamplePlan") -> dict:
    if isinstance(plan, OneSamplePlan):
        payload = {
            "schema_version": 1,
            "scope": "policy",
            "design": {
                "module": "one_sample_binomial",
                "module_version": "0.1.0",
                "n": plan.n,
                "critical_value": plan.critical,
            },
            "analysis": {
                "null_rate": str(plan.null_rate),
                "alpha": str(plan.alpha),
                "alternative": "greater",
            },
            "target": {
                "alternative_rate": str(plan.alternative_rate),
                "minimum_power": str(plan.minimum_power),
                "maximum_typeI": str(plan.maximum_typeI),
            },
        }
        if plan.search is not None:
            payload["search"] = {"min_n": plan.search[0], "max_n": plan.search[1]}
            if plan.minimal:
                payload["search"]["claim"] = SMALLEST
        return payload
    return {
        "schema_version": 1,
        "scope": "policy",
        "design": {
            "module": "two_stage_binomial",
            "module_version": "0.1.0",
            "n_stage1": plan.n_first,
            "n_stage2": plan.n_second,
            "rule": plan.rule.to_dict(),
        },
        "analysis": {"null_rate": str(plan.null_rate)},
        "target": {
            "alternative_rate": str(plan.alternative_rate),
            "minimum_power": str(plan.minimum_power),
            "maximum_typeI": str(plan.maximum_typeI),
        },
    }


def parse_policy_payload(payload: dict) -> "TwoStagePlan | OneSamplePlan":
    design, target = payload["design"], payload["target"]
    if design["module"] == "one_sample_binomial":
        search = payload.get("search")
        plan = OneSamplePlan(
            design["n"],
            parse_alpha(payload["analysis"]["null_rate"]),
            parse_alpha(payload["analysis"]["alpha"]),
            parse_alpha(target["alternative_rate"]),
            parse_alpha(target["minimum_power"]),
            parse_alpha(target["maximum_typeI"]),
            (search["min_n"], search["max_n"]) if search else None,
            bool(search) and search.get("claim") == SMALLEST,
        )
        if payload != policy_payload(plan):
            raise ValueError("Bound policy inputs are inconsistent.")
        return plan
    plan = TwoStagePlan(
        design["n_stage1"],
        design["n_stage2"],
        TwoStageRule.from_dict(design["rule"]),
        parse_alpha(payload["analysis"]["null_rate"]),
        parse_alpha(target["alternative_rate"]),
        parse_alpha(target["minimum_power"]),
        parse_alpha(target["maximum_typeI"]),
    )
    if payload != policy_payload(plan):
        raise ValueError("Bound policy inputs are inconsistent.")
    return plan


def composite_null(plan: "TwoStagePlan | OneSamplePlan") -> bool:
    """Whether the error bound covers every rate at or below the null rate."""
    return isinstance(plan, OneSamplePlan) or plan.rule.kind == "threshold"


def _null_scope(plan: "TwoStagePlan | OneSamplePlan") -> str:
    if composite_null(plan):
        return f"for every response rate at or below {plan.null_rate}"
    return f"at the null response rate {plan.null_rate}"


def policy_claims(plan: "TwoStagePlan | OneSamplePlan") -> list[str]:
    if isinstance(plan, OneSamplePlan):
        claims = [
            f"The exact binomial test with {plan.n} participants, rejecting at "
            f"{plan.critical} or more responses, rejects with probability at most "
            f"{plan.maximum_typeI} {_null_scope(plan)}.",
            f"It rejects with probability at least {plan.minimum_power} at the response rate "
            f"{plan.alternative_rate}.",
        ]
        if plan.minimal:
            claims.append(
                f"No sample size from {plan.search[0]} up to {plan.n - 1} meets both bounds "
                f"with this test, so {plan.n} is the smallest sufficient candidate in the "
                f"range {plan.search[0]} to {plan.search[1]}. Nothing is claimed outside it."
            )
        elif plan.search is not None:
            claims.append(
                f"A sample size of {plan.n} is therefore sufficient among candidates "
                f"{plan.search[0]} to {plan.search[1]}. Minimality is not claimed."
            )
        return claims
    return [
        f"The complete two-stage policy (stages {plan.n_first} and {plan.n_second}, with its "
        f"interim stop) rejects with probability at most {plan.maximum_typeI} "
        f"{_null_scope(plan)}.",
        f"It rejects with probability at least {plan.minimum_power} at the response rate "
        f"{plan.alternative_rate}.",
    ]


def policy_assumptions(plan: "TwoStagePlan | OneSamplePlan") -> list[str]:
    power = "The power bound is at one planning point, which is an input, not a fact."
    if isinstance(plan, OneSamplePlan):
        return [
            "Responses are independent with one common response rate.",
            "The sample size and critical value were fixed before outcomes were observed.",
            power,
        ]
    assumptions = [
        "Responses are independent with one common response rate in both stages.",
        "Stage sizes and the interim and final rules were fixed before outcomes were observed "
        "and are followed exactly.",
        power,
    ]
    if not composite_null(plan):
        assumptions.append(
            "The error bound is at the declared null rate only, not for every smaller rate."
        )
    if plan.rule.kind == "posterior":
        assumptions.append(
            "The posterior rule is the binomial-sum form of the Beta tail probability for "
            "integer prior parameters; its identity with the Beta integral is standard and "
            "is not proved in Lean. The bounds hold for the rule as defined."
        )
    return assumptions


def _lean_design(plan: TwoStagePlan) -> str:
    rule = plan.rule
    if rule.kind == "threshold":
        return (
            f"TwoStageBinomial.thresholdDesign {plan.n_first} {plan.n_second} "
            f"{rule.continue_above} {rule.reject_above}"
        )
    numbers = (
        rule.prior_a,
        rule.prior_b,
        *rule.reference.as_integer_ratio(),
        *rule.continue_at_least.as_integer_ratio(),
        *rule.success_at_least.as_integer_ratio(),
    )
    return f"TwoStageBinomial.posteriorDesign {plan.n_first} {plan.n_second} " + " ".join(
        str(number) for number in numbers
    )


def render_policy_proof(plan: "TwoStagePlan | OneSamplePlan", input_sha256: str) -> str:
    (a, d), (b, e) = plan.null_rate.as_integer_ratio(), plan.alternative_rate.as_integer_ratio()
    mn, md = plan.maximum_typeI.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    if isinstance(plan, OneSamplePlan):
        module, design = "OneSampleBinomial", f"⟨{plan.n}, {plan.critical}⟩"
        analysis, typeI, power = "analysis", "typeI_of_check declaredDesign", "power_of_check"
        shape = f"declaredDesign.n = {plan.n} ∧ declaredDesign.critical = {plan.critical}"
    else:
        module, design = "TwoStageBinomial", _lean_design(plan)
        shape = f"declaredDesign.nFirst = {plan.n_first} ∧ declaredDesign.nSecond = {plan.n_second}"
        if composite_null(plan):
            rule = plan.rule
            analysis, power = "analysisAtMost", "power_atMost_of_check"
            typeI = (
                "typeI_atMost_of_check declaredDesign (TwoStageBinomial.thresholdDesign_monotone "
                f"{plan.n_first} {plan.n_second} {rule.continue_above} {rule.reject_above})"
            )
        else:
            analysis, typeI, power = "analysis", "typeI_of_check declaredDesign", "power_of_check"
    smaller = ""
    if getattr(plan, "minimal", False):
        an, ad = plan.alpha.as_integer_ratio()
        level = f"levelDesign n {a} {d} {an} {ad}"
        smaller = f"""
theorem checked_critical :
    OneSampleBinomial.criticalValue {plan.n} {a} {d} {an} {ad} = {plan.critical} := by
  decide +kernel

theorem checked_smaller (n : ℕ) (lower : {plan.search[0]} ≤ n) (upper : n < {plan.n}) :
    ((({mn} : ℕ) : ℝ) / (({md} : ℕ) : ℝ)) <
        ((OneSampleBinomial.policy (OneSampleBinomial.{level})).law
          (ratPoint {a} {d} (by decide) (by decide))).real
          {{count | (OneSampleBinomial.{level}).critical ≤ count}} ∨
      ((OneSampleBinomial.policy (OneSampleBinomial.{level})).law
          (ratPoint {b} {e} (by decide) (by decide))).real
          {{count | (OneSampleBinomial.{level}).critical ≤ count}} <
        ((({bn} : ℕ) : ℝ) / (({bd} : ℕ) : ℝ)) :=
  OneSampleBinomial.fails_of_smallerFail {a} {d} (by decide) (by decide) {an} {ad}
    {mn} {md} (by decide) {b} {e} (by decide) (by decide) {bn} {bd} (by decide)
    {plan.search[0]} {plan.n} (by decide +kernel) n lower upper
"""
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical policy SHA-256: {input_sha256}
-- Both probabilities are recomputed in the kernel for the complete policy.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatProofCertificate
open StatProof StatProof.Modules

def declaredDesign : {module}.Design :=
  {design}
noncomputable def nullRate : unitInterval := ratPoint {a} {d} (by decide) (by decide)
noncomputable def declaredAnalysis := {module}.{analysis} declaredDesign nullRate

theorem checked_stages : {shape} := ⟨rfl, rfl⟩

theorem checked_typeI :
    (declaredAnalysis.typeIClaim ((({mn} : ℕ) : ℝ) / (({md} : ℕ) : ℝ))).statement :=
  {module}.{typeI} {a} {d} (by decide) (by decide)
    {mn} {md} (by decide) (by decide +kernel)

theorem checked_power :
    (declaredAnalysis.powerClaim (fun rate => rate = ratPoint {b} {e} (by decide) (by decide))
      ((({bn} : ℕ) : ℝ) / (({bd} : ℕ) : ℝ))).statement :=
  {module}.{power} declaredDesign nullRate {b} {e} (by decide) (by decide)
    {bn} {bd} (by decide) (by decide +kernel)
{smaller}
end StatProofCertificate
{_audit(policy_theorems(plan), input_sha256)}"""
