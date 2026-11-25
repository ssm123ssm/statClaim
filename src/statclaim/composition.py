"""Combining members' error bounds into one overall bound, checked by Lean.

The members' own guarantees are hypotheses here. Lean checks only that the
levels fit and that the combination rule then gives the overall bound. This is
the "conditional" evidence grade: the combination is proved, the parts are not.

There are five ways to combine, each a Mode below. To add one, add a Mode, a
Lean theorem for it and a proof template; the language, derivations and reports
read the table.
"""

from dataclasses import dataclass
from fractions import Fraction

from statclaim.fisher import validate_alpha
from statclaim.methods.assumptions import (
    CANONICAL_JOINT,
    FIXED_SIZES,
    PRESPECIFIED_FAMILY,
    PRESPECIFIED_GRAPH,
    PRESPECIFIED_LOOKS,
    PRESPECIFIED_ORDER,
    PRESPECIFIED_SPENDING,
    SINGLE_ANALYSIS,
)
from statclaim.methods.boundaries import JENNISON_TURNBULL, LAN_DEMETS
from statclaim.methods.core import SCOPES, Assumption, Guarantee

# How a member's own bound is established. Either way it is a hypothesis here.
MEMBER_GRADES = {
    "proved": "provable in Lean; verify the member's own Type I claim",
    "cited": "cited from the literature; not machine-checked",
    "conditional": "holds if each of its own members' bounds holds; verify its own claim",
    "declared": "declared by the author; not checked and not cited",
}
BRETZ = (
    "Bretz, F., Maurer, W., Brannath, W. and Posch, M. (2009). A graphical approach to "
    "sequentially rejective multiple test procedures. Statistics in Medicine 28(4), 586-604."
)
BURMAN = (
    "Burman, C.-F., Sonesson, C. and Guilbaud, O. (2009). A recycling framework for the "
    "construction of Bonferroni-based multiple tests. Statistics in Medicine 28(5), 739-761."
)
MAX_MEMBERS = 20


@dataclass(frozen=True)
class Mode:
    method: str  # the name recorded in certificates and derivations
    contract: str
    own: Assumption  # the assumption this way of combining adds
    discharged: tuple[str, ...]  # member assumptions it replaces, by id
    rule: str  # the derivation rule that concludes the contract
    extra_rules: tuple[str, ...]
    # True: levels sum to at most alpha. False: each equals alpha, or for a design with
    # spending boundaries, each is at most its look's boundary.
    splits: bool
    quantity: str
    limit: str  # what must grow for a large-sample combination to reach its bound
    theorem: str | None  # the Lean theorem; None when the rule itself is cited
    part: str  # what a member is called in messages
    title: str = ""
    references: tuple[str, ...] = ()
    version: int = 1
    also: tuple[Assumption, ...] = ()  # further assumptions the rule adds

    @property
    def grade(self) -> str:
        """conditional: Lean checks the rule. cited: the rule is taken from the literature."""
        return "conditional" if self.theorem else "cited"


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
    # One question at several looks, with boundaries that use the correlation between
    # looks: each look's level is at most the nominal level an error-spending function
    # gives it. The rule is cited: Lean does not check it.
    "spending": Mode(
        "group_sequential",
        "designs.group_sequential/group_sequential",
        PRESPECIFIED_SPENDING,
        (FIXED_SIZES.id, SINGLE_ANALYSIS.id),
        "spending-contract",
        ("same-question", "increasing-looks", "spending-boundaries"),
        False,
        "type_I_error",
        "the sample size at each look grows",
        None,
        "look",
        "Group-sequential boundaries from an error-spending function",
        (LAN_DEMETS, JENNISON_TURNBULL),
        also=(CANONICAL_JOINT,),
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
    # Different questions that pass their share of the level on after a rejection.
    # The rule is cited: Lean does not check it.
    "graphical": Mode(
        "graphical",
        "multiplicity.graphical/graphical",
        PRESPECIFIED_GRAPH,
        (),
        "graphical-contract",
        ("full-level", "graph-weights", "graph-transitions"),
        False,
        "familywise_error",
        "each member's sample size or number of events grows",
        None,
        "test",
        "Graphical multiple testing procedure",
        (BRETZ, BURMAN),
    ),
}
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
    # type_I_error for a single test or a design with looks; familywise_error for
    # a member that is itself a family, a sequence or a graph.
    quantity: str = "type_I_error"

    def __post_init__(self):
        validate_alpha(self.level)
        if self.scope not in SCOPES or self.grade not in MEMBER_GRADES:
            raise ValueError("Unknown member scope or grade.")
        if self.quantity not in ("type_I_error", "familywise_error"):
            raise ValueError("Unknown member error quantity.")
        for text in (self.name, self.basis, self.null):
            if not isinstance(text, str) or not text.strip() or "\n" in text:
                raise ValueError("Member names and descriptions must be single-line text.")

    @property
    def sentence(self) -> str:
        bound = Guarantee(self.quantity, "at_most", self.level, self.null, "finite_sample")
        return f"{self.name}: {bound.sentence} ({MEMBER_GRADES[self.grade]})"

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "level": str(self.level),
            "scope": self.scope,
            "grade": self.grade,
            "basis": self.basis,
            "null": self.null,
            "quantity": self.quantity,
        }


@dataclass(frozen=True)
class Composition:
    alpha: Fraction
    components: tuple[Component, ...]
    mode: str = "family"
    # For spending boundaries only: the largest level each look may use.
    limits: tuple[Fraction, ...] = ()

    def __post_init__(self):
        validate_alpha(self.alpha)
        if self.mode not in MODES:
            raise ValueError("Unknown composition mode.")
        if not 2 <= len(self.components) <= MAX_MEMBERS:
            raise ValueError(f"A combination needs between 2 and {MAX_MEMBERS} analyses.")
        if len({item.name for item in self.components}) != len(self.components):
            raise ValueError("Analysis names must be distinct.")
        if self.looks and len({item.null for item in self.components}) != 1:
            raise ValueError("Every look of a sequential design tests the same null.")

    @property
    def rules(self) -> Mode:
        return MODES[self.mode]

    @property
    def looks(self) -> bool:
        """One question asked at several looks."""
        return self.mode in ("sequential", "spending")

    @property
    def allocated(self) -> Fraction:
        return sum((item.level for item in self.components), Fraction())

    @property
    def fits(self) -> bool:
        """The levels are within what this way of combining allows."""
        if self.rules.splits:
            return self.allocated <= self.alpha
        if self.mode == "spending":
            return len(self.limits) == len(self.components) and all(
                item.level <= limit
                for item, limit in zip(self.components, self.limits, strict=True)
            )
        return all(item.level == self.alpha for item in self.components)

    @property
    def scope(self) -> str:
        """A combination is only as exact as its least exact member."""
        exact = self.mode != "spending" and all(
            item.scope == "finite_sample" for item in self.components
        )
        return "finite_sample" if exact else "asymptotic"

    @property
    def prespecified(self) -> Assumption:
        return self.rules.own

    @property
    def assumed(self) -> tuple[Assumption, ...]:
        """The assumptions the way of combining adds."""
        return (self.rules.own, *self.rules.also)

    @property
    def guarantee(self) -> Guarantee:
        null = (
            self.components[0].null
            if self.looks  # rejecting at any look rejects the one null
            else "any subset of the member nulls is true"
        )
        return Guarantee(
            self.rules.quantity, "at_most", self.alpha, null, self.scope, self.rules.limit
        )


def general_theorem(composition: Composition) -> str:
    return f"StatClaim.Modules.Composition.{composition.rules.theorem}"


def composition_claims(composition: Composition) -> list[str]:
    alpha, part = composition.alpha, composition.rules.part
    if composition.mode == "spending":
        return [
            f"Cited, not checked by Lean: {composition.guarantee.sentence}",
            "Each look's level is at most the nominal level that the declared error-spending "
            "function gives it, under the canonical joint distribution of the statistics at "
            "the looks. StatClaim computes those boundaries numerically.",
            f"Not checked here: each {part}'s own error bound, listed as an assumption.",
        ]
    if composition.mode == "graphical":
        return [
            f"Cited, not checked: {composition.guarantee.sentence}",
            "The procedure tests each null at its current share of the level and, after a "
            "rejection, passes that share on as the declared rules state.",
        ]
    if composition.mode == "fixed_sequence":
        claims = [
            f"Every test in the sequence uses the full level {alpha}.",
            "If each test rejects its own true null with probability at most that level, and "
            "a test is carried out only when every earlier test rejected (every null of an "
            "earlier entry that holds several), the probability of "
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
    return [
        *(item.text for item in composition.assumed),
        *(c.sentence for c in composition.components),
    ]
