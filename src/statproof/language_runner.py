"""Execute typed language requests through the existing verification backend."""

import json
import math
import tempfile
from fractions import Fraction
from pathlib import Path

from statproof.language import (
    LANGUAGE_VERSION,
    AnalysisIR,
    FamilyIR,
    FeasibilityIR,
    ObservationIR,
    OneArmCandidatesIR,
    OneSampleObservationIR,
    RequestIR,
)
from statproof.language_compiler import compile_source
from statproof.language_inspection import inspect_planning, inspect_request
from statproof.language_syntax import Diagnostic, Source, Span
from statproof.language_values import (
    CalculationResult,
    Evidence,
    ExecutionResult,
    VerificationResult,
    resolve,
    serialize,
)
from statproof.report import (
    run_binomial_result,
    run_interval,
    run_one_sample_search,
    run_policy_plan,
    run_power_plan,
    run_sample_size,
    test_design,
    verify_design,
    verify_design_only,
    verify_family,
)
from statproof.verification import digest


def _run_request(request: RequestIR, project: Path, output: Path, timeout: float) -> dict:
    subject = request.claim.subject
    if request.claim.kind in ("meets", "sample_size"):
        options = {
            "verify": request.operation == "verify",
            "project": project,
            "output": output,
            "timeout": timeout,
        }
        report = inspect_planning(request)
        if isinstance(subject, FeasibilityIR):
            run = run_power_plan if isinstance(subject.analysis, AnalysisIR) else run_policy_plan
            return run(report, subject.lower(), **options)
        target, candidates = subject.target, subject.candidates
        if isinstance(candidates, OneArmCandidatesIR):
            return run_one_sample_search(
                report,
                candidates.analysis.plan(target, candidates.min_n),
                (candidates.min_n, candidates.max_n),
                minimal=subject.minimal,
                **options,
            )
        return run_sample_size(
            report,
            candidates.analysis.alpha,
            (target.at.p_control, target.at.p_treatment, target.minimum, target.maximum_typeI),
            (candidates.min_per_arm, candidates.max_per_arm),
            minimal=subject.minimal,
            **options,
        )
    if request.claim.kind == "interval":
        return run_interval(
            subject.lower(),
            verify=request.operation == "verify",
            project=project,
            output=output,
            timeout=timeout,
        )
    if request.claim.kind == "result" and isinstance(subject, OneSampleObservationIR):
        return run_binomial_result(
            subject.lower(),
            verify=request.operation == "verify",
            project=project,
            output=output,
            timeout=timeout,
        )
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


def _result_value(
    index: int,
    request: RequestIR,
    source_id: str,
    status: str,
    details: dict,
    diagnostics: tuple[Diagnostic, ...],
) -> ExecutionResult:
    if request.operation == "calculate":
        return CalculationResult(
            index,
            request.claim,
            source_id,
            status,
            details.get("calculation"),
            details.get("decision"),
            diagnostics,
        )
    evidence = None
    if status == "verified":
        evidence = Evidence(
            request.claim,
            details["certificate"],
            tuple(details["established_properties"]),
            tuple(details["required_assumptions"]),
        )
    # Keep the established aggregate report status for CLI compatibility, but
    # distinguish backend errors from missing statistical requirements in values.
    failure = details.get("verification", {})
    if (
        status == "unresolved_obligation"
        and failure
        and failure.get("stage")
        not in ("sampling_scope", "allocation", "typeI_target", "power_target", "search_exhausted")
    ):
        status = "backend_error"
    return VerificationResult(index, request.claim, source_id, status, evidence, diagnostics)


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
    compilation = compile_source(source)
    program = compilation.program
    diagnostics = list(compilation.diagnostics)
    source_id = digest(source.text.encode())
    report = {
        "schema_version": 1,
        "language_version": LANGUAGE_VERSION,
        "source": {"path": source.path, "sha256": source_id},
        "status": compilation.status,
        "backend_invoked": False,
        "certificate_issued": False,
        "program": program.to_dict(),
        "requests": [],
        "values": {},
        "diagnostics": [diagnostic.to_dict() for diagnostic in diagnostics],
    }
    if compilation.status == "invalid":
        return report
    obligations = compilation.request_diagnostics
    values: dict[int, ExecutionResult] = {}
    if elaborate_only:
        for index, (request, blockers) in enumerate(
            zip(program.requests, obligations, strict=True), 1
        ):
            details = inspect_request(request)
            value = _result_value(index, request, source_id, "not_executed", {}, blockers)
            values[index] = value
            report["requests"].append(
                {
                    "request_id": index,
                    "operation": request.operation,
                    "claim": request.claim.kind,
                    "subject": request.claim.name,
                    "source": request.span.to_dict(),
                    "status": "blocked" if blockers else "planned",
                    "value": value.to_dict(),
                    "report": details,
                }
            )
        report["values"] = {
            binding.name: serialize(resolve(binding.value, values)) for binding in program.bindings
        }
        return report
    if not program.requests:
        report["values"] = {binding.name: serialize(binding.value) for binding in program.bindings}
        return report
    source_path = Path(source.path)
    original_present = source_path.is_file()
    # Purely unsupported files leave no output directory behind.
    executable = any(not blockers for blockers in obligations)
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
    for index, (request, blockers) in enumerate(zip(program.requests, obligations, strict=True), 1):
        request_diagnostics = list(blockers)
        if blockers:
            result = inspect_request(request)
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
                code = result.get("verification", {}).get("code", "verification")
                diagnostic = Diagnostic(code, message, request.span, "obligation")
                diagnostics.append(diagnostic)
                request_diagnostics.append(diagnostic)
        value = _result_value(index, request, source_id, status, result, tuple(request_diagnostics))
        values[index] = value
        report["requests"].append(
            {
                "request_id": index,
                "operation": request.operation,
                "claim": request.claim.kind,
                "subject": request.claim.name,
                "source": request.span.to_dict(),
                "status": status,
                "value": value.to_dict(),
                "report": result,
            }
        )
    report["values"] = {
        binding.name: serialize(resolve(binding.value, values)) for binding in program.bindings
    }
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


def _planning_lines(details: dict) -> list[str]:
    calculation = details["calculation"]
    lines = []
    if "n_control" in calculation:
        lines.append(
            f"  arm sizes = ({calculation['n_control']}, {calculation['n_treatment']}); "
            f"total = {calculation['total_sample_size']}"
        )
    if "critical_value" in calculation:
        lines.append(
            f"  n = {calculation['n']}; reject at {calculation['critical_value']} or more "
            f"responses; Type I at the null rate ~ {calculation['typeI']['decimal_approximation']}"
        )
    if "n_stage1" in calculation:
        lines.append(
            f"  stages = ({calculation['n_stage1']}, {calculation['n_stage2']}); "
            f"Type I at the null rate ~ {calculation['typeI']['decimal_approximation']}; "
            "expected sample size under the null ~ "
            f"{calculation['expected_sample_size_null']['decimal_approximation']}"
        )
    if "power" in calculation:
        lines.append(
            f"  power ~ {calculation['power']['decimal_approximation']}; "
            f"power target met = {str(calculation['power_target_met']).lower()}; "
            f"Type I target met = {str(calculation['typeI_target_met']).lower()}"
        )
    if "candidates_evaluated" in calculation:
        lines.append(
            f"  candidates evaluated = {calculation['candidates_evaluated']}; "
            "smallest-in-range claim: "
            f"{calculation['minimum_sample_size_claim'].replace('_', ' ')}"
        )
    lines.append(f"  decision = {details['decision']}; no formal certificate issued.")
    return lines


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
        names = [
            name
            for name, value in report.get("values", {}).items()
            if isinstance(value, dict)
            and value.get("type") in ("VerificationResult", "CalculationResult")
            and value["request_id"] == request["request_id"]
        ]
        label = f" [{', '.join(names)}]" if names else ""
        status = request["value"]["status"]
        if status == "not_executed":
            status = request["status"]
        lines.append(f"{status}{label}: {request['claim']}({request['subject']})")
        if details["certificate_issued"]:
            for claim in details["established_properties"]:
                lines.append(f"  {claim}")
            lines.append("  Assumptions:")
            lines.extend(f"    {assumption}" for assumption in details["required_assumptions"])
            lines.append(f"  Certificate: {details['certificate']['directory']}")
        elif request["status"] in ("planned", "blocked"):
            lines.append(f"  {details['target_property']}")
            lines.append("  Assumptions:")
            lines.extend(f"    {assumption}" for assumption in details["required_assumptions"])
        elif request["status"] == "calculated" and request["claim"] in ("meets", "sample_size"):
            lines.extend(_planning_lines(details))
        elif request["status"] == "calculated" and request["claim"] == "interval":
            calculation = details["calculation"]
            lines.append(
                f"  {calculation['responses']} responses out of {calculation['n']}; "
                f"estimate ~ {float(Fraction(calculation['estimate']['fraction'])):.4f}; "
                f"interval = [{calculation['lower']['decimal_approximation']}, "
                f"{calculation['upper']['decimal_approximation']}] at level "
                f"{calculation['level']['fraction']}; no formal certificate issued."
            )
        elif request["status"] == "calculated" and "responses" in details["calculation"]:
            calculation = details["calculation"]
            lines.append(
                f"  {calculation['responses']} responses out of {calculation['n']}; "
                f"p-value ~ {calculation['p_value']['decimal_approximation']}; "
                f"rejects at {calculation['critical_value']} or more; "
                f"decision = {details['decision']}; no formal certificate issued."
            )
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
