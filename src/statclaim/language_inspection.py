"""Pure claim descriptions and inspection data for reports and editor views."""

from statclaim import cited_planning
from statclaim.composition import DISCHARGED, composition_assumptions
from statclaim.design import inspect_design
from statclaim.family import inspect_family
from statclaim.language import (
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationResultIR,
    CalculationResultIR,
    CitedAnalysisIR,
    ClaimIR,
    ComposedFamilyIR,
    DifferenceIntervalIR,
    EffectIntervalIR,
    FamilyIR,
    FeasibilityIR,
    IntervalIR,
    LocatedValue,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedResultIR,
    ObservationIR,
    OneSampleObservationIR,
    ProportionIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateRatioIR,
    RateResultIR,
    RequestIR,
    SizingIR,
    TwoStageAnalysisIR,
    TwoStageCandidatesIR,
    TwoStageObservationIR,
    VerificationResultIR,
    normalize,
    planned_analysis,
    population_conditions,
)
from statclaim.language_compiler import Compilation, requirements
from statclaim.methods.identify import identify, mark
from statclaim.planning import (
    RESULT_ASSUMPTIONS,
    TwoStagePlan,
    TwoStageRule,
    composite_null,
    margin_assumptions,
    planning_assumptions,
    policy_assumptions,
)
from statclaim.report import (
    association_report,
    association_result_report,
    effect_interval_report,
    incidence_report,
    interval_report,
    margin_report,
    matched_report,
    planning_report,
    randomisation_report,
    stage_result_report,
)


def _allocation(candidates) -> str:
    return "equal-arm" if candidates.ratio == 1 else f"1:{candidates.ratio} allocation"


def _scope(sizing) -> str:
    if sizing.minimal:
        return "No smaller candidate in the range does."
    return "Minimality is not claimed."


def inspect_planning(request: RequestIR) -> dict:
    """Describe a planning claim from its declaration, without calculating."""
    subject = request.claim.subject
    target = subject.target
    feasibility = isinstance(subject, FeasibilityIR)
    analysis = subject.analysis if feasibility else subject.candidates.analysis
    if isinstance(analysis, CitedAnalysisIR):
        return cited_planning.describe(subject)
    if isinstance(analysis, AnalysisIR) and analysis.alternative == "margin":
        if feasibility:
            return margin_report(subject.lower(), verify=request.operation == "verify")
        candidates = subject.candidates
        null = f"p_treatment - p_control <= {analysis.hypothesis.value}"
        return planning_report(
            "margin_test",
            f"Some {_allocation(candidates)} size from {candidates.min_per_arm} to "
            f"{candidates.max_per_arm} controls gives the exact difference test power >= "
            f"{target.minimum} at p_control = {target.at.p_control}, p_treatment = "
            f"{target.at.p_treatment}, with Type I error <= {target.maximum_typeI} whenever "
            f"{null}. Minimality is not claimed.",
            margin_assumptions(analysis.margin_test(target)),
        )
    if isinstance(analysis, AnalysisIR):
        point = f"p_control = {target.at.p_control}, p_treatment = {target.at.p_treatment}"
        goal = (
            f"power >= {target.minimum} at {point}; "
            f"Type I error <= {target.maximum_typeI} under the null"
        )
        if feasibility:
            model = analysis.plan.model
            text = f"Arm sizes ({model.n_control}, {model.n_treatment}) give {goal}."
        else:
            candidates = subject.candidates
            text = (
                f"Some {_allocation(candidates)} size from {candidates.min_per_arm} to "
                f"{candidates.max_per_arm} controls "
                f"gives {goal}. {_scope(subject)}"
            )
        return planning_report("planning", text, planning_assumptions(analysis.alternative))
    if not feasibility and isinstance(subject.candidates, TwoStageCandidatesIR):
        candidates = subject.candidates
        return planning_report(
            "policy",
            f"Some two-stage design with at most {candidates.max_total} participants has "
            f"rejection probability <= {target.maximum_typeI} for every response rate at or "
            f"below {candidates.null_rate} and >= {target.minimum} at the response rate "
            f"{target.at.value}. The {candidates.criterion} ranking is not certified.",
            policy_assumptions(
                TwoStagePlan(
                    1,
                    1,
                    TwoStageRule("threshold"),
                    candidates.null_rate,
                    target.at.value,
                    target.minimum,
                    target.maximum_typeI,
                )
            ),
        )
    plan = subject.lower() if feasibility else analysis.plan(target, subject.candidates.min_n)
    null = (
        f"for every response rate at or below {analysis.null_rate}"
        if composite_null(plan)
        else f"at the null response rate {analysis.null_rate}"
    )
    goal = (
        f"rejection probability <= {target.maximum_typeI} {null} "
        f"and >= {target.minimum} at the response rate {target.at.value}"
    )
    if isinstance(analysis, TwoStageAnalysisIR):
        text = f"Complete two-stage policy: {goal}."
    elif feasibility:
        text = f"Exact binomial test with {analysis.model.n} participants: {goal}."
    else:
        candidates = subject.candidates
        text = (
            f"Some sample size from {candidates.min_n} to {candidates.max_n} gives {goal}. "
            f"{_scope(subject)}"
        )
    return planning_report("policy", text, policy_assumptions(plan))


def cited_report(analysis: CitedAnalysisIR) -> dict:
    """Describe a cited guarantee. Nothing is calculated, proved or certified."""
    method = analysis.method
    report = planning_report(
        "cited", analysis.guarantee.sentence, [item.text for item in analysis.assumptions]
    )
    report["method"] = method.to_dict()
    report["assumptions"] = [mark(item) for item in analysis.assumptions]
    report["references"] = list(method.references)
    return report


def _register(family: ComposedFamilyIR, assumptions: dict, references: list) -> None:
    """Add a combination's assumptions, and those of the tests inside it, by id."""
    composition = family.lower()
    own = composition.prespecified
    assumptions.setdefault(own.id, mark(own))
    references += [r for r in composition.rules.references if r not in references]
    for name, _ in family.analyses:
        # The member's own bound is the hypothesis the combination rests on.
        assumptions[f"member_guarantee:{name}"] = {
            "id": f"member_guarantee:{name}",
            "kind": "member",
            "text": next(c.sentence for c in composition.components if c.name == name),
            "status": "assumed",
        }
    for name, analysis in family.analyses:
        if isinstance(analysis, ComposedFamilyIR):
            _register(analysis, assumptions, references)
        elif isinstance(analysis, CitedAnalysisIR):
            for item in analysis.assumptions:
                if item.id in DISCHARGED[composition.mode]:
                    continue
                entry = assumptions.setdefault(item.id, {**mark(item), "members": []})
                entry["members"].append(name)
            references += [r for r in analysis.method.references if r not in references]


def composed_report(family: ComposedFamilyIR) -> dict:
    """Describe a combination whose members' bounds are assumed. Nothing is checked yet."""
    composition = family.lower()
    report = planning_report(
        "composition", composition.guarantee.sentence, composition_assumptions(composition)
    )
    report["members"] = [item.to_dict() for item in composition.components]
    rules = composition.rules
    if rules.grade == "cited":
        report["method"] = {"key": rules.method, "version": rules.version, "title": rules.title}
    assumptions, references = {}, []
    _register(family, assumptions, references)
    report["assumptions"] = list(assumptions.values())
    report["references"] = references
    return report


def with_population(report: dict, subject: object) -> dict:
    """Add which population the claim's bounds cover, when an assignment declares it.

    These are conditions on what the claim is about, listed with its assumptions; a
    per-protocol population also adds that exclusions were not chosen from the results.
    They are not part of any certificate: Lean's theorem is the same for either population.
    """
    conditions = [
        item
        for item in population_conditions(subject)
        if item.text not in report.get("required_assumptions", ())
    ]
    if not conditions or "required_assumptions" not in report:
        return report
    report = {
        **report,
        "required_assumptions": [
            *report["required_assumptions"],
            *(item.text for item in conditions),
        ],
    }
    if report.get("assumptions"):
        report["assumptions"] = [*report["assumptions"], *(mark(item) for item in conditions)]
    return report


def inspect_request(request: RequestIR) -> dict:
    return with_population(_inspect(request), request.claim.subject)


def _inspect(request: RequestIR) -> dict:
    subject = request.claim.subject
    if request.claim.kind in ("meets", "sample_size"):
        return inspect_planning(request)
    if isinstance(subject, (RateAnalysisIR, RateResultIR, RateRatioIR, ProportionIR)):
        plan = getattr(getattr(subject, "analysis", subject), "plan", None)
        return incidence_report(
            subject.lower(),
            stopping=plan.stopping if plan is not None else "fixed",
            verify=request.operation == "verify",
        )
    if isinstance(subject, (MatchedAnalysisIR, MatchedResultIR, MatchedIntervalIR)):
        plan = getattr(getattr(subject, "analysis", subject), "plan", None)
        return matched_report(
            subject.lower(),
            stopping=plan.stopping if plan is not None else "fixed",
            verify=request.operation == "verify",
        )
    if isinstance(subject, EffectIntervalIR):
        return effect_interval_report(subject.lower(), verify=request.operation == "verify")
    if isinstance(subject, AssociationResultIR):
        return association_result_report(subject.lower(), verify=request.operation == "verify")
    if isinstance(subject, (IntervalIR, DifferenceIntervalIR)):
        return interval_report(subject.lower(), verify=request.operation == "verify")
    if isinstance(subject, TwoStageObservationIR):
        return stage_result_report(subject.lower(), verify=request.operation == "verify")
    if isinstance(subject, OneSampleObservationIR):
        result = subject.lower()
        return planning_report(
            "result",
            f"Exact one-sided p-value and decision for {result.responses} responses out of "
            f"{result.n} at alpha {result.alpha}."
            + (
                " Calculate only; no formal evidence."
                if request.operation == "calculate"
                else " Also check the test's Type I bound."
            ),
            RESULT_ASSUMPTIONS,
        )
    if isinstance(subject, CitedAnalysisIR):
        return cited_report(subject)
    if isinstance(subject, ComposedFamilyIR):
        return composed_report(subject)
    if isinstance(subject, FamilyIR):
        return inspect_family(subject.lower())
    if isinstance(subject, RandomisationAnalysisIR):
        return randomisation_report(subject.lower(), stopping=subject.plan.stopping)
    if isinstance(subject, AssociationAnalysisIR):
        return association_report(subject.lower(), stopping=subject.plan.stopping)
    analysis = subject.analysis if isinstance(subject, ObservationIR) else subject
    if analysis.alternative == "margin":
        observed = None
        if isinstance(subject, ObservationIR):
            observed = (subject.control_successes, subject.treatment_successes)
        return margin_report(
            analysis.margin_test(observed=observed), verify=request.operation == "verify"
        )
    report = inspect_design(analysis.lower())
    if isinstance(subject, ObservationIR):
        report["verification_scope"] = "result"
        report["target_property"] = (
            "Exact p-value, table probability, support, and decision for "
            f"counts ({subject.control_successes}, {subject.treatment_successes}) "
            f"at alpha {analysis.alpha}."
        )
        report["target_property"] += (
            " Calculate only; no formal evidence."
            if request.operation == "calculate"
            else " Also check the model's Type I bound."
        )
    return report


def best_status(claim: ClaimIR) -> str:
    """The strongest status verify(...) can give this claim. Nothing is run."""
    if isinstance(claim.subject, CitedAnalysisIR):
        return claim.subject.method.grade
    if isinstance(claim.subject, ComposedFamilyIR):
        return claim.subject.lower().rules.grade
    if claim.kind in ("meets", "sample_size") and isinstance(
        planned_analysis(claim.subject), CitedAnalysisIR
    ):
        return "calculated"
    return "verified"


# From strongest to weakest. A plan is only as strong as its weakest part.
GRADE_ORDER = ("proved", "conditional", "cited", "declared")


def weakest_link(subject: object) -> dict:
    """The weakest grade anywhere in a claim's subject, and the parts that have it.

    A combination's own rule counts as a part, under the name "its rule".
    """
    found: dict[str, list[str]] = {}

    def visit(name: str, item: object) -> None:
        if isinstance(item, ComposedFamilyIR):
            found.setdefault(item.lower().rules.grade, []).append(f"{name}: its rule")
            for member, analysis in item.analyses:
                visit(member, analysis)
        elif isinstance(item, CitedAnalysisIR):
            found.setdefault(item.method.grade, []).append(name)
        elif isinstance(item, (FeasibilityIR, SizingIR)):
            visit(name, planned_analysis(item))
        else:
            found.setdefault("proved", []).append(name)

    visit("the claim", subject)
    grade = max(found, key=GRADE_ORDER.index)
    return {"grade": grade, "parts": found[grade]}


def inspect_program(compilation: Compilation) -> list[dict]:
    program = compilation.program
    claims = {}
    result_names = {}

    def visit(name, value, span):
        if isinstance(value, ClaimIR):
            item = claims.setdefault(id(value), {"claim": value, "names": [], "span": span})
            item["names"].append(name)
        elif isinstance(value, (VerificationResultIR, CalculationResultIR)):
            result_names.setdefault(value.request_id, []).append(name)
        elif isinstance(value, tuple):
            for index, item in enumerate(value):
                visit(
                    f"{name}[{index}]", item.value if isinstance(item, LocatedValue) else item, span
                )

    for binding in program.bindings:
        visit(binding.name, binding.value, binding.span)
    for request in program.requests:
        claims.setdefault(
            id(request.claim), {"claim": request.claim, "names": [], "span": request.span}
        )
    output = []
    for item in claims.values():
        claim, span = item["claim"], item["span"]
        description = inspect_request(RequestIR("verify", claim, span))
        output.append(
            {
                "names": item["names"],
                "kind": claim.kind,
                "scope": claim.scope,
                "best_status": best_status(claim),
                "weakest_link": weakest_link(claim.subject),
                "guarantee": claim.guarantee.to_dict() if claim.guarantee else None,
                "identified_assumptions": description.get("assumptions")
                or [identify(text) for text in description["required_assumptions"]],
                "claim": normalize(claim),
                "source": span.to_dict(),
                "description": description["target_property"],
                "assumptions": description["required_assumptions"],
                "requirements": [
                    d.to_dict() for d in requirements(program, RequestIR("verify", claim, span))
                ],
                "requests": [
                    {
                        "request_id": index,
                        "operation": request.operation,
                        "names": result_names.get(index, []),
                        "requirements": [
                            d.to_dict() for d in compilation.request_diagnostics[index - 1]
                        ],
                    }
                    for index, request in enumerate(program.requests, 1)
                    if request.claim is claim
                ],
            }
        )
    return output
