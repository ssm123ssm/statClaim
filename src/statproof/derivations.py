"""Derivations: why a compatibility contract is satisfied.

A derivation records the inference rules applied, the facts each rule used, the
real-world assumptions the contract depends on and any obligation still open.
It concerns compatibility of declarations only. It establishes no statistical
guarantee; that is the separate job of verify(...) and Lean.

The rules below are data. `derivation_checker` re-validates a derivation from
the serialized subject without using the code in this module that built it.
"""

from dataclasses import dataclass
from fractions import Fraction

from statproof.family import MAX_ENDPOINTS
from statproof.language import AnalysisIR, FamilyIR, ProgramIR, normalize
from statproof.language_contracts import FISHER_CONTRACT


@dataclass(frozen=True)
class Rule:
    """One inference rule: when the premise holds for the facts, conclude."""

    premise: str
    conclusion: str
    # An obligation rule may fail without making the declaration invalid; the
    # failure is then recorded as an unresolved obligation.
    obligation: str | None = None
    code: str | None = None


RULES = {
    "same-model": Rule(
        "The design and the null refer to the same model.",
        "{subject}: the null and the design describe the same study model.",
    ),
    "supported-null": Rule(
        "The null's form is one the analysis supports.",
        "{subject}: the declared null ({statement}) is supported by this analysis.",
    ),
    "level-range": Rule(
        "The level is a number between 0 and 1.",
        "{subject}: the level {alpha} is a probability.",
    ),
    "analysis-contract": Rule(
        "The same-model, supported-null and level-range rules hold for this analysis.",
        "{subject}: the design, the null and the level fit this analysis.",
    ),
    "distinct-members": Rule(
        "No analysis is listed twice.",
        "{subject}: the member analyses are distinct.",
    ),
    "family-size": Rule(
        f"The family has between 2 and {MAX_ENDPOINTS} analyses.",
        "{subject}: the family size {count} is supported.",
    ),
    "joint-law": Rule(
        "The declared joint law is one the composition rule supports.",
        '{subject}: the joint law "{joint_law}" is supported.',
    ),
    "family-contract": Rule(
        "Every member satisfies its analysis contract, and the distinct-members, "
        "family-size and joint-law rules hold.",
        "{subject}: the analyses can be composed as one family.",
    ),
    "fixed-sampling": Rule(
        "The sample sizes are fixed before outcomes are observed.",
        "{subject}: sampling is fixed, as the fixed-sample error theorem requires.",
        obligation="{subject}: sampling depends on the data. The fixed-sample error theorem "
        "does not apply until a sampling law is justified. This is not evidence of "
        "inflated error.",
        code="sampling_scope",
    ),
    "allocation": Rule(
        "The members' levels sum to at most the family level.",
        "{subject}: the allocated levels sum to {allocated}, within the family level {alpha}.",
        obligation="{subject}: the allocated levels sum to {allocated}, above the family level "
        "{alpha}. No familywise bound follows from this allocation.",
        code="allocation",
    ),
}

ANALYSIS_ASSUMPTIONS = (
    "The two samples are independent, each with one common success probability.",
    "The arm sizes are fixed before outcomes are observed.",
    "The analysis and its level are chosen before outcomes are observed.",
)
FAMILY_ASSUMPTIONS = (
    *ANALYSIS_ASSUMPTIONS,
    "Each outcome follows its own two-arm model; dependence between outcomes is unrestricted.",
    "The set of analyses and their levels are chosen before outcomes are observed.",
)
NOT_ESTABLISHED = (
    "No statistical guarantee is established here. Error rates and power are separate "
    "claims, checked by verify(...)."
)


@dataclass(frozen=True)
class Step:
    rule: str
    facts: dict
    conclusion: str
    uses: tuple[int, ...] = ()

    def to_dict(self) -> dict:
        return {
            "rule": self.rule,
            "premise": RULES[self.rule].premise,
            "facts": self.facts,
            "uses": list(self.uses),
            "conclusion": self.conclusion,
        }


@dataclass(frozen=True)
class Obligation:
    rule: str
    code: str
    facts: dict
    statement: str

    def to_dict(self) -> dict:
        return {
            "rule": self.rule,
            "code": self.code,
            "facts": self.facts,
            "statement": self.statement,
        }


@dataclass(frozen=True)
class Derivation:
    """A checked-in-principle justification attached to one named declaration."""

    name: str
    contract: str
    conclusion: str
    steps: tuple[Step, ...]
    assumptions: tuple[str, ...]
    obligations: tuple[Obligation, ...]
    subject: dict

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "contract": self.contract,
            "scope": "compatibility",
            "conclusion": self.conclusion,
            "steps": [step.to_dict() for step in self.steps],
            "assumptions": list(self.assumptions),
            "obligations": [obligation.to_dict() for obligation in self.obligations],
            "not_established": NOT_ESTABLISHED,
            "subject": self.subject,
        }


def conclude(rule: str, facts: dict) -> str:
    return RULES[rule].conclusion.format(**facts)


def oblige(rule: str, facts: dict) -> str:
    return RULES[rule].obligation.format(**facts)


class _Builder:
    def __init__(self):
        self.steps: list[Step] = []
        self.obligations: list[Obligation] = []

    def apply(self, rule: str, facts: dict, uses: tuple[int, ...] = ()) -> int:
        self.steps.append(Step(rule, facts, conclude(rule, facts), uses))
        return len(self.steps) - 1

    def settle(self, rule: str, facts: dict, holds: bool) -> None:
        """Record an obligation rule as a step when it holds, as an open obligation if not."""
        if holds:
            self.apply(rule, facts)
        else:
            self.obligations.append(Obligation(rule, RULES[rule].code, facts, oblige(rule, facts)))


def _sizes(model) -> dict:
    return {"n_control": model.n_control, "n_treatment": model.n_treatment}


def _analysis_steps(builder: _Builder, name: str, analysis: AnalysisIR) -> int:
    plan, null = analysis.plan, analysis.hypothesis
    used = (
        builder.apply(
            "same-model",
            {"subject": name, "design_model": _sizes(plan.model), "null_model": _sizes(null.model)},
        ),
        builder.apply(
            "supported-null",
            {
                "subject": name,
                "predicate": null.predicate,
                "statement": null.statement,
                "supported": list(FISHER_CONTRACT.supported_predicates),
            },
        ),
        builder.apply("level-range", {"subject": name, "alpha": str(analysis.alpha)}),
    )
    return builder.apply("analysis-contract", {"subject": name}, used)


def _sampling(builder: _Builder, name: str, analysis: AnalysisIR) -> None:
    stopping = analysis.plan.stopping
    builder.settle("fixed-sampling", {"subject": name, "stopping": stopping}, stopping == "fixed")


def derive_analysis(name: str, analysis: AnalysisIR) -> Derivation:
    builder = _Builder()
    final = _analysis_steps(builder, name, analysis)
    _sampling(builder, name, analysis)
    return Derivation(
        name,
        "tests.fisher/fisher",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        ANALYSIS_ASSUMPTIONS,
        tuple(builder.obligations),
        normalize(analysis),
    )


def derive_family(name: str, family: FamilyIR) -> Derivation:
    builder = _Builder()
    members = [_analysis_steps(builder, member, analysis) for member, analysis in family.analyses]
    names = [member for member, _ in family.analyses]
    used = (
        *members,
        builder.apply("distinct-members", {"subject": name, "members": names}),
        builder.apply("family-size", {"subject": name, "count": len(names)}),
        builder.apply("joint-law", {"subject": name, "joint_law": family.joint_law}),
    )
    final = builder.apply("family-contract", {"subject": name, "members": names}, used)
    allocated = sum((analysis.alpha for _, analysis in family.analyses), Fraction())
    builder.settle(
        "allocation",
        {"subject": name, "allocated": str(allocated), "alpha": str(family.alpha)},
        allocated <= family.alpha,
    )
    for member, analysis in family.analyses:
        _sampling(builder, member, analysis)
    return Derivation(
        name,
        "multiplicity.bonferroni/bonferroni",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        FAMILY_ASSUMPTIONS,
        tuple(builder.obligations),
        normalize(family),
    )


def derive_program(program: ProgramIR) -> tuple[Derivation, ...]:
    """Derivations for every named declaration that passed a contract.

    A declaration that failed its contract has no binding, so it has no derivation;
    the failure is reported as a diagnostic instead.
    """
    derivations = []
    for binding in program.bindings:
        if isinstance(binding.value, AnalysisIR):
            derivations.append(derive_analysis(binding.name, binding.value))
        elif isinstance(binding.value, FamilyIR):
            derivations.append(derive_family(binding.name, binding.value))
    return tuple(derivations)
