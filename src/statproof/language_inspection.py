"""Pure claim descriptions and inspection data for reports and editor views."""

from statproof.design import inspect_design
from statproof.family import inspect_family
from statproof.language import (
    CalculationResultIR,
    ClaimIR,
    FamilyIR,
    LocatedValue,
    ObservationIR,
    RequestIR,
    VerificationResultIR,
    normalize,
)
from statproof.language_compiler import Compilation, requirements


def inspect_request(request: RequestIR) -> dict:
    subject = request.claim.subject
    if isinstance(subject, FamilyIR):
        return inspect_family(subject.lower())
    analysis = subject.analysis if isinstance(subject, ObservationIR) else subject
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
