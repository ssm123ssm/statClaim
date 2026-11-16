"""Pure claim descriptions and inspection data for reports and editor views."""

from statproof.design import inspect_design
from statproof.family import inspect_family
from statproof.language import (
    AnalysisIR,
    CalculationResultIR,
    ClaimIR,
    DifferenceIntervalIR,
    FamilyIR,
    FeasibilityIR,
    IntervalIR,
    LocatedValue,
    ObservationIR,
    OneSampleObservationIR,
    RequestIR,
    TwoStageAnalysisIR,
    TwoStageCandidatesIR,
    TwoStageObservationIR,
    VerificationResultIR,
    normalize,
)
from statproof.language_compiler import Compilation, requirements
from statproof.planning import (
    PLANNING_ASSUMPTIONS,
    RESULT_ASSUMPTIONS,
    TwoStagePlan,
    TwoStageRule,
    composite_null,
    margin_assumptions,
    policy_assumptions,
)
from statproof.report import (
    interval_report,
    margin_report,
    planning_report,
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
        return planning_report("planning", text, PLANNING_ASSUMPTIONS)
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


def inspect_request(request: RequestIR) -> dict:
    subject = request.claim.subject
    if request.claim.kind in ("meets", "sample_size"):
        return inspect_planning(request)
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
    if isinstance(subject, FamilyIR):
        return inspect_family(subject.lower())
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
