"""Combining members' error bounds into one overall bound, checked by Lean.

The members' own guarantees are hypotheses here. Lean checks only that the
levels fit and that the combination rule then gives the overall bound. This is
the "conditional" evidence grade: the combination is proved, the parts are not.

There are three ways to combine, each a Mode below. To add one, add a Mode, a
Lean theorem for it and a proof template; the language, derivations and reports
read the table.
"""

import re
from dataclasses import dataclass
from fractions import Fraction

from statclaim.fisher import parse_alpha, validate_alpha
from statclaim.methods.assumptions import (
    FIXED_SIZES,
    PRESPECIFIED_FAMILY,
    PRESPECIFIED_LOOKS,
    PRESPECIFIED_ORDER,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import SCOPES, Assumption, Guarantee
from statclaim.planning import _audit

COMPOSITION_KIND = "statclaim_composition_certificate"
# How a member's own bound is established. Either way it is a hypothesis here.
MEMBER_GRADES = {
    "proved": "provable in Lean; verify the member's own Type I claim",
    "cited": "cited from the literature; not machine-checked",
    "conditional": "holds if each of its own looks' bounds holds; verify its own Type I claim",
}
MAX_MEMBERS = 20


@dataclass(frozen=True)
class Mode:
    method: str  # the name recorded in certificates and derivations
    contract: str
    own: Assumption  # the assumption this way of combining adds
    discharged: tuple[str, ...]  # member assumptions it replaces, by id
    rule: str  # the derivation rule that concludes the contract
    extra_rules: tuple[str, ...]
    splits: bool  # True: levels sum to at most alpha. False: each equals alpha.
    quantity: str
    limit: str  # what must grow for a large-sample combination to reach its bound
    theorem: str
    part: str  # what a member is called in messages


MODES = {
    # Different questions, each at its own share of the level.
    "family": Mode(
        "bonferroni",
        "multiplicity.bonferroni/bonferroni",
        PRESPECIFIED_FAMILY,
        (),
        "composed-family-contract",
        (),
        True,
        "familywise_error",
        "each member's sample size or number of events grows",
        "familywise_le_of_levels",
        "member",
    ),
    # One question at several looks. Each look is one fixed-size test, and the
    # design itself accounts for looking repeatedly.
    "sequential": Mode(
        "alpha_spending",
        "designs.group_sequential/alpha_spending",
        PRESPECIFIED_LOOKS,
        (FIXED_SIZES.id, SINGLE_ANALYSIS.id),
        "sequential-contract",
        ("same-question", "increasing-looks"),
        True,
        "type_I_error",
        "the sample size at each look grows",
        "familywise_le_of_levels",
        "look",
    ),
    # Different questions in a fixed order, each at the full level, each tested
    # only if every earlier one was rejected.
    "fixed_sequence": Mode(
        "fixed_sequence",
        "multiplicity.fixed_sequence/fixed_sequence",
        PRESPECIFIED_ORDER,
        (),
        "fixed-sequence-contract",
        ("full-level",),
        False,
        "familywise_error",
        "each member's sample size or number of events grows",
        "fixed_sequence_le_of_levels",
        "test",
    ),
}
METHODS_TO_MODES = {mode.method: key for key, mode in MODES.items()}
DISCHARGED = {key: mode.discharged for key, mode in MODES.items()}


@dataclass(frozen=True)
class Component:
    """One member, reduced to what the combination needs and how it is justified."""

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
    mode: str = "family"

    def __post_init__(self):
        validate_alpha(self.alpha)
        if self.mode not in MODES:
            raise ValueError("Unknown composition mode.")
        if not 2 <= len(self.components) <= MAX_MEMBERS:
            raise ValueError(f"A combination needs between 2 and {MAX_MEMBERS} analyses.")
        if len({item.name for item in self.components}) != len(self.components):
            raise ValueError("Analysis names must be distinct.")
        if self.mode == "sequential" and len({item.null for item in self.components}) != 1:
            raise ValueError("Every look of a sequential design tests the same null.")

    @property
    def rules(self) -> Mode:
        return MODES[self.mode]

    @property
    def allocated(self) -> Fraction:
        return sum((item.level for item in self.components), Fraction())

    @property
    def fits(self) -> bool:
        """The levels are within what this way of combining allows."""
        if self.rules.splits:
            return self.allocated <= self.alpha
        return all(item.level == self.alpha for item in self.components)

    @property
    def scope(self) -> str:
        """A combination is only as exact as its least exact member."""
        exact = all(item.scope == "finite_sample" for item in self.components)
        return "finite_sample" if exact else "asymptotic"

    @property
    def prespecified(self) -> Assumption:
        return self.rules.own

    @property
    def guarantee(self) -> Guarantee:
        null = (
            self.components[0].null
            if self.mode == "sequential"  # rejecting at any look rejects the one null
            else "any subset of the member nulls is true"
        )
        return Guarantee(
            self.rules.quantity, "at_most", self.alpha, null, self.scope, self.rules.limit
        )


def composition_payload(composition: Composition) -> dict:
    if not composition.fits:
        raise ValueError("The member levels do not fit the requested overall bound.")
    return {
        "schema_version": 1,
        "scope": "composition",
        "method": composition.rules.method,
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
        METHODS_TO_MODES[payload["method"]],
    )
    if payload != composition_payload(composition):
        raise ValueError("Bound combination, members, or requested guarantee is inconsistent.")
    return composition


def composition_theorems(composition: Composition) -> list[str]:
    first = "checked_allocation" if composition.rules.splits else "checked_levels"
    return [first, "checked_composition"]


def general_theorem(composition: Composition) -> str:
    return f"StatClaim.Modules.Composition.{composition.rules.theorem}"


def composition_claims(composition: Composition) -> list[str]:
    alpha, part = composition.alpha, composition.rules.part
    if composition.mode == "fixed_sequence":
        claims = [
            f"Every test in the sequence uses the full level {alpha}.",
            "If each test rejects its own true null with probability at most that level, and "
            "a test is carried out only when every earlier test rejected, the probability of "
            f"rejecting any true null is at most {alpha}, for every configuration of true "
            "and false nulls and any dependence between tests.",
        ]
        whole = "familywise bound"
    elif composition.mode == "sequential":
        claims = [
            f"The look levels sum to {composition.allocated}, which does not exceed the "
            f"overall error bound {alpha}.",
            "If the test at each look rejects the true null with probability at most its "
            f"level, the probability of rejecting it at any look is at most {alpha}, "
            "whatever the dependence between looks. This split is conservative: it does not "
            "use the correlation between looks.",
        ]
        whole = "overall error bound"
    else:
        claims = [
            f"The member levels sum to {composition.allocated}, which does not exceed the "
            f"familywise bound {alpha}.",
            "If each member rejects its own true null with probability at most its level, "
            f"the probability of rejecting any true member null is at most {alpha}, "
            "for every configuration of true and false nulls and any dependence between members.",
        ]
        whole = "familywise bound"
    if composition.scope == "asymptotic":
        slack = "the sum of the slacks" if composition.rules.splits else "the largest slack"
        claims.append(
            f"If a {part}'s bound holds only up to a slack, the {whole} holds up to "
            f"{slack}. With large-sample {part}s the bound is therefore "
            "approached as the sample sizes grow; none is claimed at the declared sizes."
        )
    claims.append(f"Not checked here: each {part}'s own error bound, listed as an assumption.")
    return claims


def composition_assumptions(composition: Composition) -> list[str]:
    return [composition.prespecified.text, *(item.sentence for item in composition.components)]


def render_composition_proof(composition: Composition, input_sha256: str) -> str:
    """Only validated rational literals and the member count enter the template."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    if not composition.fits:
        raise ValueError("The member levels do not fit the requested overall bound.")
    count = len(composition.components)
    levels = []
    for item in composition.components:
        numerator, denominator = item.level.as_integer_ratio()
        levels.append(f"⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩")
    numerator, denominator = composition.alpha.as_integer_ratio()
    separator = ",\n    "
    header = f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical composition SHA-256: {input_sha256}
-- The members' own error bounds are the hypothesis `marginal`; they are not proved here.
namespace StatClaimCertificate
open StatClaim MeasureTheory
open Modules.Composition

def levels : Fin {count} → SignificanceLevel :=
  ![{separator.join(levels)}]
def familyLevel : ℚ := ({numerator} : ℚ) / {denominator}
"""
    if composition.rules.splits:
        body = f"""
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
"""
    else:
        body = f"""
theorem checked_levels : ∀ i, (levels i).value = familyLevel := by
  intro i
  fin_cases i <;> norm_num [levels, familyLevel]

-- A null is rejected only if its own test and every earlier test reject.
theorem checked_composition {{Outcome : Type}} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (trueNull : Fin {count} → Prop) (reject : Fin {count} → Set Outcome)
    (slack : ℝ) (slack_nonnegative : 0 ≤ slack)
    (marginal : ∀ i, trueNull i →
      law.real (reject i) ≤ ((levels i).value : ℝ) + slack) :
    law.real (sequenceFalseRejection trueNull reject) ≤ (familyLevel : ℝ) + slack :=
  fixed_sequence_le_of_levels law trueNull reject levels slack slack_nonnegative marginal
    familyLevel (by norm_num [familyLevel]) checked_levels
"""
    return f"""{header}{body}
end StatClaimCertificate
{_audit(composition_theorems(composition), input_sha256)}"""
