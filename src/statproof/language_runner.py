"""Execute typed language requests through the existing verification backend."""

import json
import math
import tempfile
from pathlib import Path

from statproof.design import inspect_design
from statproof.family import inspect_family
from statproof.language import (
    AnalysisIR,
    FamilyIR,
    ObservationIR,
    PlanIR,
    ProgramIR,
    RequestIR,
    elaborate,
)
from statproof.language_syntax import Diagnostic, Source, Span
from statproof.report import test_design, verify_design, verify_design_only, verify_family
from statproof.verification import digest


def _origin(program: ProgramIR, name: str, fallback: Span, field: str | None = None) -> Span:
    binding = next((binding for binding in program.bindings if binding.name == name), None)
    if binding is None:
        return fallback
    return dict(binding.argument_sources).get(field, binding.span)


def _plan_source(program: ProgramIR, analysis: AnalysisIR, fallback: Span) -> Span:
    return next(
        (
            binding.span
            for binding in program.bindings
            if isinstance(binding.value, PlanIR) and binding.value is analysis.plan
        ),
        fallback,
    )


def _obligation(program: ProgramIR, request: RequestIR) -> Diagnostic | None:
    subject, name = request.claim.subject, request.claim.name
    if isinstance(subject, FamilyIR):
        family = subject.lower()
        if family.allocated_alpha > family.alpha:
            return Diagnostic(
                "allocation",
                f"{name}: allocated alpha {family.allocated_alpha} "
                f"exceeds the requested family bound {family.alpha}. No Bonferroni certificate "
                "can be supplied from this allocation; this does not prove excessive actual error.",
                _origin(program, name, request.span, "alpha"),
                "obligation",
            )
        if not family.supported:
            return Diagnostic(
                "sampling_scope",
                f"{name}: an analysis uses data-dependent stopping. "
                "Its marginal sampling law needs separate justification; this is not evidence "
                "of inflated error.",
                _plan_source(
                    program,
                    next(
                        analysis
                        for _, analysis in subject.analyses
                        if analysis.plan.stopping != "fixed"
                    ),
                    request.span,
                ),
                "obligation",
            )
    else:
        analysis = subject.analysis if isinstance(subject, ObservationIR) else subject
        if analysis.plan.stopping != "fixed" and request.operation == "verify":
            return Diagnostic(
                "sampling_scope",
                f"{name}: data-dependent stopping needs a justified "
                "sampling law before the fixed-sample guarantee can be used. This is not "
                "evidence of inflated error.",
                _plan_source(program, analysis, request.span),
                "obligation",
            )
    return None


def _run_request(request: RequestIR, project: Path, output: Path, timeout: float) -> dict:
    subject = request.claim.subject
    if request.claim.kind == "familywise" and isinstance(subject, FamilyIR):
        return verify_family(subject.lower(), project=project, output=output, timeout=timeout)
    if request.claim.kind == "typeI" and isinstance(subject, AnalysisIR):
        return verify_design_only(subject.lower(), project=project, output=output, timeout=timeout)
    if request.claim.kind != "result" or not isinstance(subject, ObservationIR):
        raise ValueError("This claim has no registered verification adapter.")
    options = {
        "control_successes": subject.control_successes,
        "treatment_successes": subject.treatment_successes,
    }
    if request.operation == "calculate":
        return test_design(subject.analysis.lower(), **options)
    return verify_design(
        subject.analysis.lower(), **options, project=project, output=output, timeout=timeout
    )


def _inspection(request: RequestIR) -> dict:
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
            f"at alpha {analysis.alpha}, plus the model's Type I bound."
        )
    return report


def check_source(
    source: Source,
    *,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
    elaborate_only: bool = False,
) -> dict:
    """Elaborate the entire file before any calculation, build, or certificate write.

    Each verified request has its own ordinary certificate. The run receipt is a
    source/IR provenance record, not an additional mathematical certificate.
    """
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("Timeout must be a positive, finite number of seconds.")
    if elaborate_only and output is not None:
        raise ValueError("--output is for execution; --elaborate-only does not write artifacts.")
    program, diagnostics = elaborate(source)
    source_id = digest(source.text.encode())
    report = {
        "schema_version": 1,
        "language_version": "0.1.0",
        "source": {"path": source.path, "sha256": source_id},
        "status": "invalid" if diagnostics else "elaborated",
        "backend_invoked": False,
        "certificate_issued": False,
        "program": program.to_dict(),
        "requests": [],
        "diagnostics": [diagnostic.to_dict() for diagnostic in diagnostics],
    }
    if diagnostics or not program.requests:
        return report
    obligations = [_obligation(program, request) for request in program.requests]
    if elaborate_only:
        report["requests"] = [
            {
                "operation": request.operation,
                "claim": request.claim.kind,
                "subject": request.claim.name,
                "source": request.span.to_dict(),
                "status": "planned",
                "report": _inspection(request),
            }
            for request in program.requests
        ]
        report["diagnostics"] = [obligation.to_dict() for obligation in obligations if obligation]
        if report["diagnostics"]:
            report["status"] = "unresolved_obligation"
        return report
    source_path = Path(source.path)
    original_present = source_path.is_file()
    # Purely unsupported files leave no output directory behind.
    executable = any(obligation is None for obligation in obligations)
    directory = None
    if executable:
        if output is None:
            parent = project.resolve() / ".statproof/programs"
            parent.mkdir(parents=True, exist_ok=True)
            directory = Path(tempfile.mkdtemp(prefix=f"{source_id[:12]}-", dir=parent))
        else:
            directory = output.resolve()
            directory.mkdir(parents=True, exist_ok=False)
        (directory / "Source.stat").write_bytes(source.text.encode("utf-8"))
        report["run_directory"] = str(directory)
    for index, (request, obligation) in enumerate(
        zip(program.requests, obligations, strict=True), 1
    ):
        if obligation:
            diagnostics.append(obligation)
            result = _inspection(request)
            status = "unresolved_obligation"
        else:
            result = _run_request(request, project, directory / f"request-{index:03d}", timeout)
            status = result["status"]
            if request.operation == "calculate":
                status = "calculated" if result["decision"] is not None else "unresolved_obligation"
            if status == "unresolved_obligation":
                message = result.get("verification", {}).get(
                    "message",
                    "The requested guarantee remains unresolved under the declared sampling plan.",
                )
                diagnostics.append(Diagnostic("verification", message, request.span, "obligation"))
        report["requests"].append(
            {
                "operation": request.operation,
                "claim": request.claim.kind,
                "subject": request.claim.name,
                "source": request.span.to_dict(),
                "status": status,
                "report": result,
            }
        )
    report["backend_invoked"] = any(r["report"]["backend_invoked"] for r in report["requests"])
    report["certificate_issued"] = any(
        r["report"]["certificate_issued"] for r in report["requests"]
    )
    statuses = [r["status"] for r in report["requests"]]
    report["status"] = (
        "unresolved_obligation"
        if "unresolved_obligation" in statuses
        else "verified"
        if "verified" in statuses
        else "calculated"
    )
    # Certificates concern the retained snapshot. Do not display their status as
    # verification of a file that was edited while the backend was checking it.
    try:
        current_source = (
            source_path.read_bytes().decode("utf-8") if original_present else source.text
        )
    except (OSError, UnicodeError):
        current_source = None
    if original_present and current_source != source.text:
        report["status"] = "stale_source"
        diagnostics.append(
            Diagnostic(
                "source_changed",
                "The source changed during execution. "
                "Certificates refer to the retained Source.stat snapshot; rerun the current file.",
                program.requests[0].span,
                "obligation",
            )
        )
    if directory and digest((directory / "Source.stat").read_bytes()) != source_id:
        report["status"] = "stale_source"
        diagnostics.append(
            Diagnostic(
                "snapshot_changed",
                "The retained source snapshot changed "
                "during execution. The run cannot attest source provenance; rerun the program.",
                program.requests[0].span,
                "obligation",
            )
        )
    report["diagnostics"] = [diagnostic.to_dict() for diagnostic in diagnostics]
    if directory:
        pending = directory / "run.pending.json"
        pending.write_text(json.dumps(report, indent=2) + "\n")
        pending.replace(directory / "run.json")
    return report


def render_report(report: dict, source: Source) -> str:
    lines = []
    for diagnostic in report["diagnostics"]:
        lines.append(
            Diagnostic(
                diagnostic["code"],
                diagnostic["message"],
                Span(**diagnostic["source"]),
                diagnostic["severity"],
            ).format(source)
        )
    for request in report["requests"]:
        details = request["report"]
        lines.append(f"{request['status']}: {request['claim']}({request['subject']})")
        if details["certificate_issued"]:
            for claim in details["established_properties"]:
                lines.append(f"  {claim}")
            lines.append("  Assumptions:")
            lines.extend(f"    {assumption}" for assumption in details["required_assumptions"])
            lines.append(f"  Certificate: {details['certificate']['directory']}")
        elif request["status"] == "planned":
            lines.append(f"  {details['target_property']}")
            lines.append("  Assumptions:")
            lines.extend(f"    {assumption}" for assumption in details["required_assumptions"])
        elif request["status"] == "calculated":
            lines.append(
                f"  p-value = {details['calculation']['p_value']['fraction']}; "
                f"decision = {details['decision']}; no formal certificate issued."
            )
    lines.append(f"Program status: {report['status']}")
    if report["status"] == "elaborated":
        lines.append("Structural checks passed; no Lean proof or certificate was produced.")
    if report.get("run_directory"):
        lines.append(f"Source snapshot and run report: {report['run_directory']}")
    return "\n".join(lines)
