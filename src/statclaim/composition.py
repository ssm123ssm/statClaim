"""Combining members' error bounds into a familywise bound, checked by Lean.

The members' own guarantees are hypotheses here. Lean checks only that the
levels add up and that the union bound then gives the family bound. This is the
"conditional" evidence grade: the combination is proved, the parts are not.
"""

import re
from dataclasses import dataclass
from fractions import Fraction

from statclaim.fisher import parse_alpha, validate_alpha
from statclaim.methods.assumptions import PRESPECIFIED_FAMILY
from statclaim.methods.core import SCOPES, Guarantee
from statclaim.planning import _audit

COMPOSITION_KIND = "statclaim_composition_certificate"
COMPOSITION_THEOREMS = ["checked_allocation", "checked_composition"]
GENERAL_THEOREM = "StatClaim.Modules.Composition.familywise_le_of_levels"
# How a member's own bound is established. Either way it is a hypothesis here.
MEMBER_GRADES = {
    "proved": "provable in Lean; verify the member's own Type I claim",
    "cited": "cited from the literature; not machine-checked",
}
PRESPECIFIED = PRESPECIFIED_FAMILY.text
MAX_MEMBERS = 20
# What has to grow for a family with large-sample members to reach its bound.
FAMILY_LIMIT = "each member's sample size or number of events grows"


@dataclass(frozen=True)
class Component:
    """One member, reduced to what the union bound needs and how it is justified."""

    name: str
    level: Fraction
    scope: str
    grade: str
    basis: str  # the contract or method that supplies the member's bound
    null: str

    def __post_init__(self):
        validate_alpha(self.level)
        if self.scope not in SCOPES or self.grade not in MEMBER_GRADES:
            raise ValueError("Unknown member scope or grade.")
        for text in (self.name, self.basis, self.null):
            if not isinstance(text, str) or not text.strip() or "\n" in text:
                raise ValueError("Member names and descriptions must be single-line text.")

    @property
    def sentence(self) -> str:
        bound = Guarantee("type_I_error", "at_most", self.level, self.null, "finite_sample")
        return f"{self.name}: {bound.sentence} ({MEMBER_GRADES[self.grade]})"

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "level": str(self.level),
            "scope": self.scope,
            "grade": self.grade,
            "basis": self.basis,
            "null": self.null,
        }


@dataclass(frozen=True)
class Composition:
    alpha: Fraction
    components: tuple[Component, ...]

    def __post_init__(self):
        validate_alpha(self.alpha)
        if not 2 <= len(self.components) <= MAX_MEMBERS:
            raise ValueError(f"A family needs between 2 and {MAX_MEMBERS} analyses.")
        if len({item.name for item in self.components}) != len(self.components):
            raise ValueError("Analysis names must be distinct.")

    @property
    def allocated(self) -> Fraction:
        return sum((item.level for item in self.components), Fraction())

    @property
    def scope(self) -> str:
        """A family is only as exact as its least exact member."""
        exact = all(item.scope == "finite_sample" for item in self.components)
        return "finite_sample" if exact else "asymptotic"

    @property
    def guarantee(self) -> Guarantee:
        return Guarantee(
            "familywise_error",
            "at_most",
            self.alpha,
            "any subset of the member nulls is true",
            self.scope,
            FAMILY_LIMIT,
        )


def composition_payload(composition: Composition) -> dict:
    if composition.allocated > composition.alpha:
        raise ValueError("The allocated alpha exceeds the requested familywise bound.")
    return {
        "schema_version": 1,
        "scope": "composition",
        "method": "bonferroni",
        "alpha": str(composition.alpha),
        "members": [item.to_dict() for item in composition.components],
    }


def parse_composition_payload(payload: dict) -> Composition:
    composition = Composition(
        parse_alpha(payload["alpha"]),
        tuple(
            Component(
                item["name"],
                parse_alpha(item["level"]),
                item["scope"],
                item["grade"],
                item["basis"],
                item["null"],
            )
            for item in payload["members"]
        ),
    )
    if payload != composition_payload(composition):
        raise ValueError("Bound family, members, or requested guarantee is inconsistent.")
    return composition


def composition_claims(composition: Composition) -> list[str]:
    claims = [
        f"The member levels sum to {composition.allocated}, which does not exceed the "
        f"familywise bound {composition.alpha}.",
        "If each member rejects its own true null with probability at most its level, the "
        f"probability of rejecting any true member null is at most {composition.alpha}, for "
        "every configuration of true and false nulls and any dependence between members.",
    ]
    if composition.scope == "asymptotic":
        claims.append(
            "If a member's bound holds only up to a slack, the familywise bound holds up to "
            "the sum of the slacks. With large-sample members the bound is therefore "
            "approached as the sample sizes grow; none is claimed at the declared sizes."
        )
    claims.append("Not checked here: the members' own error bounds, listed as assumptions.")
    return claims


def composition_assumptions(composition: Composition) -> list[str]:
    return [PRESPECIFIED, *(item.sentence for item in composition.components)]


def render_composition_proof(composition: Composition, input_sha256: str) -> str:
    """Only validated rational literals and the member count enter the template."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    if composition.allocated > composition.alpha:
        raise ValueError("The allocated alpha exceeds the requested familywise bound.")
    count = len(composition.components)
    levels = []
    for item in composition.components:
        numerator, denominator = item.level.as_integer_ratio()
        levels.append(f"⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩")
    numerator, denominator = composition.alpha.as_integer_ratio()
    separator = ",\n    "
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical composition SHA-256: {input_sha256}
-- The members' own error bounds are the hypothesis `marginal`; they are not proved here.
namespace StatClaimCertificate
open StatClaim MeasureTheory
open Modules.Composition

def levels : Fin {count} → SignificanceLevel :=
  ![{separator.join(levels)}]
def familyLevel : ℚ := ({numerator} : ℚ) / {denominator}

theorem checked_allocation : ∑ i, (levels i).value ≤ familyLevel := by
  norm_num [Fin.sum_univ_succ, levels, familyLevel]

theorem checked_composition {{Outcome : Type}} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (trueNull : Fin {count} → Prop) (reject : Fin {count} → Set Outcome)
    (slack : Fin {count} → ℝ) (slack_nonnegative : ∀ i, 0 ≤ slack i)
    (marginal : ∀ i, trueNull i →
      law.real (reject i) ≤ ((levels i).value : ℝ) + slack i) :
    law.real (falseRejection trueNull reject) ≤ (familyLevel : ℝ) + ∑ i, slack i :=
  familywise_le_of_levels law trueNull reject levels slack slack_nonnegative marginal
    familyLevel checked_allocation

end StatClaimCertificate
{_audit(COMPOSITION_THEOREMS, input_sha256)}"""
