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

from statclaim.composition import DISCHARGED, MODES
from statclaim.family import MAX_ENDPOINTS
from statclaim.language import (
    AnalysisIR,
    CandidatesIR,
    CitedAnalysisIR,
    ClaimIR,
    ComposedFamilyIR,
    FamilyIR,
    FeasibilityIR,
    OneArmCandidatesIR,
    OneSampleAnalysisIR,
    ProgramIR,
    RandomisationAnalysisIR,
    RatesIR,
    TwoStageAnalysisIR,
    normalize,
)
from statclaim.planning import MAX_ONE_ARM, MAX_STAGE
from statclaim.randomisation import ASSUMPTIONS as RANDOMISATION_ASSUMPTIONS


@dataclass(frozen=True)
class Rule:
    """One inference rule: when the premise holds for the facts, conclude."""

    premise: str
    conclusion: str
    # An obligation rule may fail without making the declaration invalid; the
    # failure is then recorded as an unresolved obligation.
    obligation: str | None = None
    code: str | None = None
    # Bump when the premise or what counts as satisfying it changes.
    version: int = 1


RULES = {
    "same-model": Rule(
        "The design and the null refer to the same model.",
        "{subject}: the null and the design describe the same study model.",
    ),
    "supported-null": Rule(
        "The null's form, its margin where the analysis fixes one, and its direction where "
        "the model declares which direction is better, are supported.",
        "{subject}: the declared null ({statement}) is supported by this analysis.",
        version=2,
    ),
    "level-range": Rule(
        "The level is a number between 0 and 1.",
        "{subject}: the level {alpha} is a probability.",
    ),
    "level-interior": Rule(
        "The level is strictly between 0 and 1.",
        "{subject}: the level {alpha} lies strictly between 0 and 1.",
    ),
    "enough-data": Rule(
        "Each arm and the whole study are large enough for the method to estimate variance.",
        "{subject}: arm sizes ({n_control}, {n_treatment}) meet the method's minimum of "
        "{min_per_arm} per arm and {min_total} in total.",
    ),
    "enough-clusters": Rule(
        "The assignment randomises clusters, and each arm and the whole study have enough "
        "clusters for the method, which takes one summary per cluster.",
        "{subject}: ({clusters_control}, {clusters_treatment}) clusters per arm meet the "
        "method's minimum of {min_per_arm} per arm and {min_total} in total.",
    ),
    "cluster-contract": Rule(
        "The same-model, supported-null, level-interior and enough-clusters rules hold.",
        "{subject}: the design, the null and the level fit this cited method, with the "
        "clusters as the sample.",
    ),
    "declared-design": Rule(
        "No assumption of the method is contradicted by the declared design: several "
        "measurements per participant contradict independent observations, and randomisation "
        "by cluster contradicts independent participants.",
        "{subject}: the declared design ({design}) contradicts none of the method's assumptions.",
    ),
    "declared-randomisation": Rule(
        "The assignment declares how it was randomised, by a scheme the test's theorem "
        "covers: complete randomisation, every split of the units into arms of the declared "
        "sizes equally likely.",
        "{subject}: the assignment declares {randomisation} randomisation of {units} {unit}s, "
        "{treated} treated.",
    ),
    "can-reject": Rule(
        "One over the number of equally likely splits, the smallest p-value the test can "
        "give, is at most the level.",
        "{subject}: {splits} splits give a smallest p-value of 1/{splits}, within the level "
        "{alpha}.",
    ),
    "randomisation-contract": Rule(
        "The same-model, supported-null, level-range, declared-randomisation and can-reject "
        "rules hold.",
        "{subject}: the design, the null and the level fit the randomisation test.",
    ),
    "cited-contract": Rule(
        "The same-model, supported-null, level-interior and enough-data rules hold.",
        "{subject}: the design, the null and the level fit this cited method.",
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
    "composed-family-contract": Rule(
        "Every member satisfies its own contract, and the distinct-members and family-size "
        "rules hold.",
        "{subject}: its members can be combined under one familywise bound.",
    ),
    "same-question": Rule(
        "Every look uses the same test and the same null.",
        "{subject}: every look asks the same question ({statement}) with {test}.",
    ),
    "increasing-looks": Rule(
        "Each look has at least as many participants per arm as the one before, and more in total.",
        "{subject}: the looks' cumulative arm sizes grow: {sizes}.",
    ),
    "sequential-contract": Rule(
        "Every look satisfies its own contract, and the distinct-members, family-size, "
        "same-question and increasing-looks rules hold.",
        "{subject}: its looks form one sequential test of the same null.",
    ),
    "full-level": Rule(
        "Every test in the sequence uses the sequence's level.",
        "{subject}: every test uses the full level {alpha}.",
    ),
    "graph-weights": Rule(
        "There is one starting share for each test, each from 0 to 1, summing to at most 1.",
        "{subject}: the starting shares {weights} sum to {total}.",
    ),
    "graph-transitions": Rule(
        "Each test has one row of shares, from 0 to 1, passing nothing to itself and at "
        "most its whole level in total.",
        "{subject}: every row of transitions is a valid way to pass a level on.",
    ),
    "graphical-contract": Rule(
        "Every test satisfies its own contract, and the distinct-members, family-size, "
        "full-level, graph-weights and graph-transitions rules hold.",
        "{subject}: its tests, shares and transitions form one graphical procedure.",
    ),
    "fixed-sequence-contract": Rule(
        "Every test satisfies its own contract, and the distinct-members, family-size and "
        "full-level rules hold.",
        "{subject}: its tests form one fixed sequence.",
    ),
    "family-contract": Rule(
        "Every member satisfies its analysis contract, and the distinct-members, "
        "family-size and joint-law rules hold.",
        "{subject}: the analyses can be composed as one family.",
    ),
    "sample-size-range": Rule(
        f"The sample size is between 1 and {MAX_ONE_ARM}.",
        "{subject}: the sample size {n} is supported.",
    ),
    "null-rate-interior": Rule(
        "The null rate lies strictly between 0 and 1.",
        "{subject}: the null rate {rate} leaves room for both larger and smaller rates.",
    ),
    "one-sample-contract": Rule(
        "The sample-size-range, null-rate-interior and level-range rules hold for this test.",
        "{subject}: the model, the null rate and the level fit this test.",
    ),
    "stage-sizes": Rule(
        f"Each stage has between 1 and {MAX_STAGE} participants.",
        "{subject}: the stage sizes {n_stage1} and {n_stage2} are supported.",
    ),
    "null-rate": Rule(
        "The null rate is a probability.",
        "{subject}: the null rate {rate} is a probability.",
    ),
    "decision-rule": Rule(
        "The interim and final rules are well formed: counts are whole numbers, prior "
        "parameters are positive whole numbers, and probabilities lie in range.",
        "{subject}: the interim and final rules are well formed.",
    ),
    "two-stage-contract": Rule(
        "The stage-sizes, null-rate and decision-rule rules hold for this design.",
        "{subject}: the stages, the rule and the null rate form a complete design.",
    ),
    "planning-point": Rule(
        "The planning point has one rate per arm of the analysis.",
        "{subject}: the planning point belongs to the analysis's parameters.",
    ),
    "alternative": Rule(
        "The planning point lies outside the analysis's null.",
        "{subject}: the planning point lies outside the null ({null}).",
    ),
    "target-range": Rule(
        "The required power is in (0, 1] and the error bound is in [0, 1].",
        "{subject}: the power {minimum} and error bound {maximum_typeI} are valid targets.",
    ),
    "search-range": Rule(
        "The search bounds are ordered and within the supported sizes.",
        "{subject}: the search range is valid.",
    ),
    "planning-contract": Rule(
        "The analysis satisfies its own contract where it has one, and the planning-point, "
        "alternative, target-range and, for a search, search-range rules hold.",
        "{subject}: the target can be assessed for this analysis.",
    ),
    "power-formula": Rule(
        "The method has a power formula, and the planning point is the kind that formula "
        "takes, with valid values.",
        "{subject}: {method} has the power formula {formula} (version {version}) for this "
        "planning point.",
    ),
    "cited-planning-contract": Rule(
        "The cited-contract, power-formula, alternative, target-range and, for a search, "
        "search-range rules hold.",
        "{subject}: approximate power can be calculated for this cited analysis.",
    ),
    "cited-error-budget": Rule(
        "The test's level is at most the requested error bound.",
        "{subject}: the level {alpha} is within the requested error bound {maximum_typeI}.",
        obligation="{subject}: the level {alpha} exceeds the requested error bound "
        "{maximum_typeI}. The cited guarantee is at the test's level only. This is not "
        "evidence that the actual error exceeds the request.",
        code="typeI_target_not_established",
    ),
    "error-budget": Rule(
        "The analysis's level is at most the requested error bound.",
        "{subject}: the level {alpha} is within the requested error bound {maximum_typeI}.",
        obligation="{subject}: the level {alpha} exceeds the requested error bound "
        "{maximum_typeI}. The error theorem bounds error by the level only. This is not "
        "evidence that the actual error exceeds the request.",
        code="typeI_target_not_established",
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

RANDOMISATION_CONTRACT_ID = "tests.randomisation/randomisation_test"
ONE_SIDED_CONTRACT = "tests.fisher/fisher_one_sided"
MARGIN_CONTRACT_ID = "tests.difference/difference_test"
CONTRACT_IDS = {
    "two_sided": "tests.fisher/fisher",
    "greater": ONE_SIDED_CONTRACT,
    "margin": MARGIN_CONTRACT_ID,
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
ONE_SAMPLE_ASSUMPTIONS = (
    "Responses are independent with one common response rate.",
    "The sample size, null rate and level are fixed before outcomes are observed.",
)
TWO_STAGE_ASSUMPTIONS = (
    "Responses are independent with one common response rate in both stages.",
    "Stage sizes and the interim and final rules are fixed before outcomes are observed "
    "and are followed exactly.",
)
PLANNING_POINT_ASSUMPTION = "The planning point is an input for planning, not an established fact."
CITED_NOT_ESTABLISHED = (
    "The guarantee below is cited from the literature and holds only under the listed "
    "assumptions. It is not proved here or in Lean."
)
COMPOSED_NOT_ESTABLISHED = (
    "The familywise bound below follows from the members' own error bounds, which are "
    "assumed here. Lean checks the combination when you verify the familywise claim."
)
DECLARED_NOT_ESTABLISHED = (
    "The guarantee below is the author's own statement about a test StatClaim has no "
    "contract or source for. Nothing about it is checked."
)
NOT_ESTABLISHED = (
    "No statistical guarantee is established here. Error rates and power are separate "
    "claims, checked by verify(...)."
)


def not_established(guarantee: dict | None) -> str:
    """What a derivation does not establish, by the grade of any guarantee it carries."""
    if not guarantee:
        return NOT_ESTABLISHED
    return {
        "conditional": COMPOSED_NOT_ESTABLISHED,
        "declared": DECLARED_NOT_ESTABLISHED,
    }.get(guarantee["grade"], CITED_NOT_ESTABLISHED)


@dataclass(frozen=True)
class Step:
    rule: str
    facts: dict
    conclusion: str
    uses: tuple[int, ...] = ()

    def to_dict(self) -> dict:
        return {
            "rule": self.rule,
            "rule_version": RULES[self.rule].version,
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
    # Set when the contract carries a guarantee that holds given the assumptions.
    guarantee: dict | None = None

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "contract": self.contract,
            "scope": "conditional_guarantee" if self.guarantee else "compatibility",
            "guarantee": self.guarantee,
            "conclusion": self.conclusion,
            "steps": [step.to_dict() for step in self.steps],
            "assumptions": list(self.assumptions),
            "obligations": [obligation.to_dict() for obligation in self.obligations],
            "not_established": not_established(self.guarantee),
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


def _direction(model) -> dict:
    """The declared better direction, recorded so the checker can compare it with the null."""
    return {"better": model.better} if model.better else {}


def describe_design(measurements: int, clusters: tuple[int, int] | None) -> str:
    """The declared design features in words. derivation_checker words them the same way."""
    parts = [f"{measurements} measurements per participant"] if measurements > 1 else []
    if clusters:
        parts.append(f"{clusters[0]} and {clusters[1]} clusters randomised")
    return "; ".join(parts)


def _declared_design(builder: _Builder, name: str, analysis: CitedAnalysisIR) -> None:
    """Recorded only when the model declares a feature a test's assumptions could contradict."""
    model = analysis.plan.model
    if not model.features:
        return
    assignment = model.assignment
    clusters = (
        (assignment.clusters_control, assignment.clusters_treatment)
        if assignment.clustered
        else None
    )
    builder.apply(
        "declared-design",
        {
            "subject": name,
            "design": describe_design(model.measured.measurements, clusters),
            "features": list(model.features),
            "assumptions": [item.id for item in analysis.method.assumptions],
        },
    )


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
                "supported": list(analysis.contract.supported_predicates),
                **_direction(null.model),
            },
        ),
        builder.apply("level-range", {"subject": name, "alpha": str(analysis.alpha)}),
    )
    return builder.apply("analysis-contract", {"subject": name}, used)


def _fixed(name: str, analysis) -> tuple[str, dict, bool]:
    stopping = analysis.plan.stopping
    return ("fixed-sampling", {"subject": name, "stopping": stopping}, stopping == "fixed")


def _sampling(builder: _Builder, name: str, analysis: AnalysisIR) -> None:
    builder.settle(*_fixed(name, analysis))


def derive_analysis(name: str, analysis: AnalysisIR) -> Derivation:
    builder = _Builder()
    final = _analysis_steps(builder, name, analysis)
    _sampling(builder, name, analysis)
    return Derivation(
        name,
        CONTRACT_IDS[analysis.alternative],
        builder.steps[final].conclusion,
        tuple(builder.steps),
        ANALYSIS_ASSUMPTIONS,
        tuple(builder.obligations),
        normalize(analysis),
    )


def derive_randomisation(name: str, analysis: RandomisationAnalysisIR) -> Derivation:
    """Why the randomisation test's contract holds. Its guarantee is proved, not carried."""
    builder, plan, null = _Builder(), analysis.plan, analysis.hypothesis
    test = analysis.lower()
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
                "supported": ["no_effect"],
                **_direction(null.model),
            },
        ),
        builder.apply("level-range", {"subject": name, "alpha": str(analysis.alpha)}),
        builder.apply(
            "declared-randomisation",
            {
                "subject": name,
                "randomisation": plan.model.assignment.randomisation,
                "unit": test.unit,
                "units": test.units,
                "treated": test.treated,
            },
        ),
        builder.apply(
            "can-reject", {"subject": name, "splits": str(test.splits), "alpha": str(test.alpha)}
        ),
    )
    final = builder.apply("randomisation-contract", {"subject": name}, used)
    _sampling(builder, name, analysis)
    return Derivation(
        name,
        RANDOMISATION_CONTRACT_ID,
        builder.steps[final].conclusion,
        tuple(builder.steps),
        RANDOMISATION_ASSUMPTIONS,
        tuple(builder.obligations),
        normalize(analysis),
    )


def cited_guarantee(analysis: CitedAnalysisIR) -> dict:
    """The guarantee a satisfied cited contract carries, with what it rests on."""
    method = analysis.method
    return {
        **analysis.guarantee.to_dict(),
        "sentence": analysis.guarantee.sentence,
        "grade": method.grade,
        "method": method.to_dict(),
        "given": [item.id for item in analysis.assumptions],
        "references": list(method.references),
    }


def _cited_steps(builder: _Builder, name: str, analysis: CitedAnalysisIR) -> int:
    plan, null, method = analysis.plan, analysis.hypothesis, analysis.method
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
                "supported": list(method.nulls),
                **_direction(null.model),
            },
        ),
        builder.apply("level-interior", {"subject": name, "alpha": str(analysis.alpha)}),
        _enough(builder, name, plan.model, method),
    )
    _declared_design(builder, name, analysis)
    contract = "cluster-contract" if method.unit == "cluster" else "cited-contract"
    return builder.apply(contract, {"subject": name}, used)


def _enough(builder: _Builder, name: str, model, method) -> int:
    """Enough participants, or for a test of one summary per cluster, enough clusters."""
    minimum = {"min_per_arm": method.min_per_arm, "min_total": method.min_total}
    if method.unit != "cluster":
        return builder.apply("enough-data", {"subject": name, **_sizes(model), **minimum})
    assignment = model.assignment
    return builder.apply(
        "enough-clusters",
        {
            "subject": name,
            "clusters_control": assignment.clusters_control,
            "clusters_treatment": assignment.clusters_treatment,
            **minimum,
        },
    )


def derive_cited(name: str, analysis: CitedAnalysisIR) -> Derivation:
    builder, method = _Builder(), analysis.method
    final = _cited_steps(builder, name, analysis)
    _sampling(builder, name, analysis)
    return Derivation(
        name,
        f"{method.module}/{method.key}",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        tuple(item.text for item in analysis.assumptions),
        tuple(builder.obligations),
        normalize(analysis),
        # An open obligation means the guarantee does not apply yet.
        None if builder.obligations else cited_guarantee(analysis),
    )


def composed_assumptions(family: ComposedFamilyIR) -> tuple[str, ...]:
    """Its own assumption and member bounds, those of designs inside it, then the tests'."""
    own, nested, cited = _assumption_parts(family)
    return (*own, *nested, *cited)


def _assumption_parts(family: ComposedFamilyIR) -> tuple[list[str], list[str], list[str]]:
    composition = family.lower()
    own = [composition.prespecified.text, *(item.sentence for item in composition.components)]
    nested: list[str] = []
    cited: list[str] = []
    for _, analysis in family.analyses:
        if isinstance(analysis, ComposedFamilyIR):
            inner_own, inner_nested, inner_cited = _assumption_parts(analysis)
            nested += [text for text in (*inner_own, *inner_nested) if text not in nested]
            cited += [text for text in inner_cited if text not in cited]
        elif isinstance(analysis, CitedAnalysisIR):
            cited += [
                item.text
                for item in analysis.assumptions
                if item.text not in cited and item.id not in DISCHARGED[composition.mode]
            ]
    return own, nested, cited


def composed_guarantee(family: ComposedFamilyIR) -> dict:
    composition = family.lower()
    rules = composition.rules
    guarantee = {
        **composition.guarantee.to_dict(),
        "sentence": composition.guarantee.sentence,
        "grade": rules.grade,
        "members": [item.to_dict() for item in composition.components],
        "given": [
            composition.prespecified.id,
            *(f"member_guarantee:{n}" for n, _ in family.analyses),
        ],
    }
    if rules.grade == "cited":
        guarantee["method"] = {
            "key": rules.method,
            "version": rules.version,
            "title": rules.title,
        }
        guarantee["references"] = list(rules.references)
    return guarantee


def test_key(analysis) -> str:
    if isinstance(analysis, CitedAnalysisIR):
        return analysis.method.key
    return CONTRACT_IDS[analysis.alternative].split("/")[1]


def _composed_steps(builder: _Builder, name: str, family: ComposedFamilyIR, pending: list) -> int:
    """Steps for a combination; its open-or-met obligation rules are added to pending."""
    rules = MODES[family.mode]
    inner: list = []
    members = []
    for member, analysis in family.analyses:
        if isinstance(analysis, ComposedFamilyIR):
            members.append(_composed_steps(builder, member, analysis, inner))
        else:
            members.append(
                _cited_steps(builder, member, analysis)
                if isinstance(analysis, CitedAnalysisIR)
                else _analysis_steps(builder, member, analysis)
            )
            inner.append(_fixed(member, analysis))
    names = [member for member, _ in family.analyses]
    used = [
        *members,
        builder.apply("distinct-members", {"subject": name, "members": names}),
        builder.apply("family-size", {"subject": name, "count": len(names)}),
    ]
    if family.mode == "sequential":
        first = family.analyses[0][1]
        used += [
            builder.apply(
                "same-question",
                {
                    "subject": name,
                    "test": test_key(first),
                    "statement": first.hypothesis.statement,
                },
            ),
            builder.apply(
                "increasing-looks",
                {
                    "subject": name,
                    "sizes": [
                        [a.plan.model.n_control, a.plan.model.n_treatment]
                        for _, a in family.analyses
                    ],
                },
            ),
        ]
    if family.mode in ("fixed_sequence", "graphical"):
        used.append(builder.apply("full-level", {"subject": name, "alpha": str(family.alpha)}))
    if family.mode == "graphical":
        weights = [str(weight) for weight in family.weights]
        used += [
            builder.apply(
                "graph-weights",
                {"subject": name, "weights": weights, "total": str(sum(family.weights))},
            ),
            builder.apply(
                "graph-transitions",
                {
                    "subject": name,
                    "transitions": [[str(share) for share in row] for row in family.transitions],
                },
            ),
        ]
    final = builder.apply(rules.rule, {"subject": name, "members": names}, tuple(used))
    if rules.splits:
        allocated = sum((analysis.alpha for _, analysis in family.analyses), Fraction())
        pending.append(
            (
                "allocation",
                {"subject": name, "allocated": str(allocated), "alpha": str(family.alpha)},
                allocated <= family.alpha,
            )
        )
    pending += inner
    return final


def derive_composed(name: str, family: ComposedFamilyIR) -> Derivation:
    builder = _Builder()
    pending: list = []
    final = _composed_steps(builder, name, family, pending)
    for rule, facts, holds in pending:
        builder.settle(rule, facts, holds)
    return Derivation(
        name,
        MODES[family.mode].contract,
        builder.steps[final].conclusion,
        tuple(builder.steps),
        composed_assumptions(family),
        tuple(builder.obligations),
        normalize(family),
        None if builder.obligations else composed_guarantee(family),
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


def _one_sample_steps(builder: _Builder, name: str, analysis: OneSampleAnalysisIR) -> int:
    used = (
        builder.apply("sample-size-range", {"subject": name, "n": analysis.model.n}),
        builder.apply("null-rate-interior", {"subject": name, "rate": str(analysis.null_rate)}),
        builder.apply("level-range", {"subject": name, "alpha": str(analysis.alpha)}),
    )
    return builder.apply("one-sample-contract", {"subject": name}, used)


def _two_stage_steps(builder: _Builder, name: str, analysis: TwoStageAnalysisIR) -> int:
    design = analysis.design
    used = (
        builder.apply(
            "stage-sizes",
            {"subject": name, "n_stage1": design.n_stage1, "n_stage2": design.n_stage2},
        ),
        builder.apply("null-rate", {"subject": name, "rate": str(analysis.null_rate)}),
        builder.apply("decision-rule", {"subject": name, "rule": analysis.rule.rule.to_dict()}),
    )
    return builder.apply("two-stage-contract", {"subject": name}, used)


def derive_one_sample(name: str, analysis: OneSampleAnalysisIR) -> Derivation:
    builder = _Builder()
    final = _one_sample_steps(builder, name, analysis)
    return Derivation(
        name,
        "tests.binomial/binomial_test",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        ONE_SAMPLE_ASSUMPTIONS,
        (),
        normalize(analysis),
    )


def derive_two_stage(name: str, analysis: TwoStageAnalysisIR) -> Derivation:
    builder = _Builder()
    final = _two_stage_steps(builder, name, analysis)
    return Derivation(
        name,
        "designs.two_stage/two_stage_test",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        TWO_STAGE_ASSUMPTIONS,
        (),
        normalize(analysis),
    )


def derive_cited_planning(name: str, claim: ClaimIR, analysis: CitedAnalysisIR) -> Derivation:
    """Approximate power for a cited test: its contract fits and it has a power formula."""
    subject, method = claim.subject, analysis.method
    target, inner = subject.target, f"{name}.analysis"
    search = None if isinstance(subject, FeasibilityIR) else subject.candidates
    formula, point = method.power, normalize(subject.target.at)
    builder = _Builder()
    used = [
        _cited_steps(builder, inner, analysis),
        builder.apply(
            "power-formula",
            {
                "subject": name,
                "method": method.key,
                "formula": formula.key,
                "version": formula.version,
                "point": point,
            },
        ),
        builder.apply(
            "alternative",
            {"subject": name, "point": point, "null": analysis.hypothesis.statement},
        ),
        builder.apply(
            "target-range",
            {
                "subject": name,
                "minimum": str(target.minimum),
                "maximum_typeI": str(target.maximum_typeI),
            },
        ),
    ]
    if search is not None:
        bounds = {key: value for key, value in normalize(search).items() if key != "analysis"}
        used.append(builder.apply("search-range", {"subject": name, "search": bounds}))
    final = builder.apply("cited-planning-contract", {"subject": name}, tuple(used))
    builder.settle(
        "cited-error-budget",
        {"subject": name, "alpha": str(analysis.alpha), "maximum_typeI": str(target.maximum_typeI)},
        analysis.alpha <= target.maximum_typeI,
    )
    _sampling(builder, inner, analysis)
    return Derivation(
        name,
        f"planning/{claim.kind}",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        (
            *(item.text for item in (*analysis.assumptions, *formula.assumptions)),
            PLANNING_POINT_ASSUMPTION,
        ),
        tuple(builder.obligations),
        normalize(claim),
    )


def derive_planning(name: str, claim: ClaimIR) -> Derivation:
    """A planning claim: its analysis fits, and the target can be assessed for it."""
    subject = claim.subject
    search = None if isinstance(subject, FeasibilityIR) else subject.candidates
    analysis = subject.analysis if search is None else None
    if isinstance(search, (CandidatesIR, OneArmCandidatesIR)):
        analysis = search.analysis
    if isinstance(analysis, CitedAnalysisIR):
        return derive_cited_planning(name, claim, analysis)
    target, inner = subject.target, f"{name}.analysis"
    builder = _Builder()
    used: list[int] = []
    if isinstance(analysis, AnalysisIR):
        used.append(_analysis_steps(builder, inner, analysis))
        assumptions = ANALYSIS_ASSUMPTIONS
    elif isinstance(analysis, OneSampleAnalysisIR):
        used.append(_one_sample_steps(builder, inner, analysis))
        assumptions = ONE_SAMPLE_ASSUMPTIONS
    elif isinstance(analysis, TwoStageAnalysisIR):
        used.append(_two_stage_steps(builder, inner, analysis))
        assumptions = TWO_STAGE_ASSUMPTIONS
    else:
        assumptions = TWO_STAGE_ASSUMPTIONS
    two_arm = isinstance(analysis, AnalysisIR)
    point = normalize(target.at)
    used.append(
        builder.apply(
            "planning-point",
            {"subject": name, "analysis": "two_arm" if two_arm else "single_arm", "point": point},
        )
    )
    if isinstance(target.at, RatesIR):
        facts = {
            "subject": name,
            "p_control": str(target.at.p_control),
            "p_treatment": str(target.at.p_treatment),
            "null": {
                "two_sided": "p_treatment = p_control",
                "greater": "p_treatment <= p_control",
                "margin": f"p_treatment - p_control <= {analysis.hypothesis.value}",
            }[analysis.alternative],
        }
    else:
        null_rate = search.null_rate if analysis is None else analysis.null_rate
        facts = {
            "subject": name,
            "rate": str(target.at.value),
            "null_rate": str(null_rate),
            "null": f"response rate <= {null_rate}",
        }
    used.append(builder.apply("alternative", facts))
    used.append(
        builder.apply(
            "target-range",
            {
                "subject": name,
                "minimum": str(target.minimum),
                "maximum_typeI": str(target.maximum_typeI),
            },
        )
    )
    if search is not None:
        bounds = {key: value for key, value in normalize(search).items() if key != "analysis"}
        used.append(builder.apply("search-range", {"subject": name, "search": bounds}))
    final = builder.apply("planning-contract", {"subject": name}, tuple(used))
    if two_arm:
        builder.settle(
            "error-budget",
            {
                "subject": name,
                "alpha": str(analysis.alpha),
                "maximum_typeI": str(target.maximum_typeI),
            },
            analysis.alpha <= target.maximum_typeI,
        )
        _sampling(builder, inner, analysis)
    return Derivation(
        name,
        f"planning/{claim.kind}",
        builder.steps[final].conclusion,
        tuple(builder.steps),
        (*assumptions, PLANNING_POINT_ASSUMPTION),
        tuple(builder.obligations),
        normalize(claim),
    )


def derive_program(program: ProgramIR) -> tuple[Derivation, ...]:
    """Derivations for every named declaration that passed a contract.

    A declaration that failed its contract has no binding, so it has no derivation;
    the failure is reported as a diagnostic instead.
    """
    derivations = []
    for binding in program.bindings:
        value = binding.value
        if isinstance(value, AnalysisIR):
            derivations.append(derive_analysis(binding.name, value))
        elif isinstance(value, CitedAnalysisIR):
            derivations.append(derive_cited(binding.name, value))
        elif isinstance(value, RandomisationAnalysisIR):
            derivations.append(derive_randomisation(binding.name, value))
        elif isinstance(value, ComposedFamilyIR):
            derivations.append(derive_composed(binding.name, value))
        elif isinstance(value, FamilyIR):
            derivations.append(derive_family(binding.name, value))
        elif isinstance(value, OneSampleAnalysisIR):
            derivations.append(derive_one_sample(binding.name, value))
        elif isinstance(value, TwoStageAnalysisIR):
            derivations.append(derive_two_stage(binding.name, value))
        elif isinstance(value, ClaimIR) and value.kind in ("meets", "sample_size"):
            derivations.append(derive_planning(binding.name, value))
    return tuple(derivations)
