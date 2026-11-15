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

PLANNING_KIND = "statproof_planning_certificate"
POLICY_KIND = "statproof_policy_certificate"
PLANNING_CHECKED_THEOREMS = ["checked_sizes", "checked_typeI", "checked_power"]
POLICY_CHECKED_THEOREMS = ["checked_stages", "checked_typeI", "checked_power"]
# Kernel checking enumerates every table; larger searches remain calculations.
MAX_PER_ARM = 500
MAX_STAGE = 200

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


@lru_cache(maxsize=256)
def fisher_rejection_region(
    n_control: int, n_treatment: int, alpha: Fraction
) -> tuple[tuple[bool, ...], ...]:
    """Whether each table (control successes, treatment successes) is rejected."""
    an, ad = alpha.as_integer_ratio()
    region = [[False] * (n_treatment + 1) for _ in range(n_control + 1)]
    for total in range(n_control + n_treatment + 1):
        lower, upper = max(0, total - n_treatment), min(n_control, total)
        weights = [
            comb(n_control, k) * comb(n_treatment, total - k) for k in range(lower, upper + 1)
        ]
        denominator = comb(n_control + n_treatment, total)
        for offset, observed in enumerate(weights):
            extreme = sum(weight for weight in weights if weight <= observed)
            region[lower + offset][total - lower - offset] = extreme * ad <= an * denominator
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

    def __post_init__(self) -> None:
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
    if plan.search is not None:
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


def render_planning_proof(plan: PowerPlan, input_sha256: str) -> str:
    if not plan.typeI_target_met or plan.design.stopping != "fixed":
        raise ValueError("The Type I target is not established by the Fisher theorem.")
    nc, nt = plan.design.n_control, plan.design.n_treatment
    an, ad = plan.design.alpha.as_integer_ratio()
    mn, md = plan.maximum_typeI.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    (a, d), (b, e) = plan.p_control.as_integer_ratio(), plan.p_treatment.as_integer_ratio()
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical planning SHA-256: {input_sha256}
-- Power is recomputed in the kernel; no calculated value is supplied.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatProofCertificate
open StatProof StatProof.Modules

def declaredSizes : FixedSampleDesign := ⟨{nc}, {nt}, by decide, by decide⟩
def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := FisherPower.analysis declaredSizes declaredLevel
noncomputable def planningPoint : TwoArmBinomial.Parameters :=
  FisherPower.ratePoint {a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide)

theorem checked_sizes : declaredSizes.nControl = {nc} ∧ declaredSizes.nTreatment = {nt} ∧
    0 < declaredSizes.nControl ∧ 0 < declaredSizes.nTreatment := by decide

theorem checked_typeI :
    (declaredAnalysis.typeIClaim ((({mn} : ℕ) : ℝ) / (({md} : ℕ) : ℝ))).statement := by
  intro parameter null
  refine le_trans (FisherPower.typeI_statement declaredSizes declaredLevel parameter null) ?_
  norm_num [declaredLevel]

theorem checked_power :
    (declaredAnalysis.powerClaim (fun parameter => parameter = planningPoint)
      ((({bn} : ℕ) : ℝ) / (({bd} : ℕ) : ℝ))).statement :=
  FisherPower.power_of_check declaredSizes declaredLevel {an} {ad} (by decide)
    (by norm_num [declaredLevel]) {a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide)
    {bn} {bd} (by decide) (by decide +kernel)

end StatProofCertificate
{_audit(PLANNING_CHECKED_THEOREMS, input_sha256)}"""


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


def policy_payload(plan: TwoStagePlan) -> dict:
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


def parse_policy_payload(payload: dict) -> TwoStagePlan:
    design, target = payload["design"], payload["target"]
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


def policy_claims(plan: TwoStagePlan) -> list[str]:
    return [
        f"The complete two-stage policy (stages {plan.n_first} and {plan.n_second}, with its "
        f"interim stop) rejects with probability at most {plan.maximum_typeI} at the null "
        f"response rate {plan.null_rate}.",
        f"It rejects with probability at least {plan.minimum_power} at the response rate "
        f"{plan.alternative_rate}.",
    ]


def policy_assumptions(plan: TwoStagePlan) -> list[str]:
    assumptions = [
        "Responses are independent with one common response rate in both stages.",
        "Stage sizes and the interim and final rules were fixed before outcomes were observed "
        "and are followed exactly.",
        "Both bounds are at the declared rates only: the error bound is at the null rate, "
        "not for every smaller rate, and the power bound is at one planning point.",
    ]
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


def render_policy_proof(plan: TwoStagePlan, input_sha256: str) -> str:
    (a, d), (b, e) = plan.null_rate.as_integer_ratio(), plan.alternative_rate.as_integer_ratio()
    mn, md = plan.maximum_typeI.as_integer_ratio()
    bn, bd = plan.minimum_power.as_integer_ratio()
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical policy SHA-256: {input_sha256}
-- Both probabilities are recomputed in the kernel for the complete policy.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatProofCertificate
open StatProof StatProof.Modules

def declaredDesign : TwoStageBinomial.Design :=
  {_lean_design(plan)}
noncomputable def nullRate : unitInterval := ratPoint {a} {d} (by decide) (by decide)
noncomputable def declaredAnalysis := TwoStageBinomial.analysis declaredDesign nullRate

theorem checked_stages : declaredDesign.nFirst = {plan.n_first} ∧
    declaredDesign.nSecond = {plan.n_second} := ⟨rfl, rfl⟩

theorem checked_typeI :
    (declaredAnalysis.typeIClaim ((({mn} : ℕ) : ℝ) / (({md} : ℕ) : ℝ))).statement :=
  TwoStageBinomial.typeI_of_check declaredDesign {a} {d} (by decide) (by decide)
    {mn} {md} (by decide) (by decide +kernel)

theorem checked_power :
    (declaredAnalysis.powerClaim (fun rate => rate = ratPoint {b} {e} (by decide) (by decide))
      ((({bn} : ℕ) : ℝ) / (({bd} : ℕ) : ℝ))).statement :=
  TwoStageBinomial.power_of_check declaredDesign nullRate {b} {e} (by decide) (by decide)
    {bn} {bd} (by decide) (by decide +kernel)

end StatProofCertificate
{_audit(POLICY_CHECKED_THEOREMS, input_sha256)}"""
