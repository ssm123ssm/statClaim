"""Execute typed language requests through the existing verification backend."""

import json
import math
import tempfile
from collections.abc import Collection
from fractions import Fraction
from pathlib import Path

from statclaim import association_planning, cited_planning, precision_planning, simulated_planning
from statclaim.composition import composition_claims
from statclaim.language import (
    LANGUAGE_VERSION,
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationResultIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    ComposedFamilyIR,
    EffectIntervalIR,
    FamilyIR,
    FeasibilityIR,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedResultIR,
    ObservationIR,
    OneArmCandidatesIR,
    OneSampleObservationIR,
    PlannedIntervalIR,
    ProportionIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateRatioIR,
    RateResultIR,
    RequestIR,
    TotalCandidatesIR,
    TwoStageCandidatesIR,
    TwoStageObservationIR,
    group_probabilities,
)
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import (
    GRADE_ORDER,
    cited_report,
    inspect_planning,
    inspect_request,
    weakest_link,
    with_population,
)
from statclaim.language_syntax import Diagnostic, Source, Span
from statclaim.language_values import (
    STATUS_GRADES,
    CalculationResult,
    Evidence,
    ExecutionResult,
    VerificationResult,
    resolve,
    serialize,
)
from statclaim.methods.core import GRADES, SCOPES
from statclaim.methods.identify import identify
from statclaim.reference import SCOPE_NOTE
from statclaim.report import (
    run_association,
    run_association_plan,
    run_association_result,
    run_association_search,
    run_binomial_result,
    run_composition,
    run_count_search,
    run_effect_interval,
    run_incidence,
    run_interval,
    run_margin,
    run_margin_search,
    run_matched,
    run_one_sample_search,
    run_policy_plan,
    run_power_plan,
    run_randomisation,
    run_sample_size,
    run_stage_result,
    run_total_search,
    run_two_stage_search,
    test_design,
    verify_design,
    verify_design_only,
    verify_family,
)
from statclaim.verification import digest

STATUS_OF_GRADE = {grade: status for status, grade in STATUS_GRADES.items()}


def _weakest_line(request: dict) -> list[str]:
    """Say so when a claim's own status is stronger than the weakest part inside it."""
    link = request["weakest_link"]
    own = STATUS_GRADES.get(request["status"])
    if own is None or GRADE_ORDER.index(link["grade"]) <= GRADE_ORDER.index(own):
        return []
    parts = ", ".join(link["parts"])
    return [f"  Weakest part: {GRADES[link['grade']].label} ({parts})"]


def _count_template(analysis, target, bounds: tuple[int, int], minimal: bool):
    """The first candidate of a search over pairs or events; the search builds the others."""
    from statclaim.matched import MatchedTest
    from statclaim.observational_planning import MatchedPowerPlan, RatePowerPlan

    point, low = target.at, bounds[0]
    common = (target.minimum, target.maximum_typeI, "sample_size", bounds, minimal)
    if isinstance(analysis, MatchedAnalysisIR):
        test = analysis.lower()
        return MatchedPowerPlan(
            MatchedTest(low, test.alpha, test.exposure, test.outcome),
            point.share,
            point.odds_ratio,
            *common,
        )
    return RatePowerPlan(
        analysis.lower(),
        point.exposed_time,
        point.unexposed_time,
        point.rate_ratio,
        low,
        *common,
    )


def _run_request(request: RequestIR, project: Path, output: Path, timeout: float) -> dict:
    subject = request.claim.subject
    if isinstance(subject, (CitedAnalysisIR, CitedAssociationIR)):
        # The contract checks passed during compilation. No backend runs: the
        # guarantee is the published result, restated with its assumptions.
        report = cited_report(subject)
        grade = subject.method.grade
        prefix = (
            "Declared by the author, not checked" if grade == "declared" else "Cited, not checked"
        )
        report.update(
            status=grade,
            evidence_grade=grade,
            established_properties=[f"{prefix}: {report['target_property']}"],
        )
        return report
    if request.claim.kind in ("meets", "sample_size"):
        options = {
            "verify": request.operation == "verify",
            "project": project,
            "output": output,
            "timeout": timeout,
        }
        report = inspect_planning(request)
        if request.operation == "simulate":
            # Refused while compiling unless the analysis has a simulation model.
            return simulated_planning.run(report, subject, request.settings)
        analysis = (
            subject.analysis if isinstance(subject, FeasibilityIR) else subject.candidates.analysis
        )
        if isinstance(analysis, PlannedIntervalIR):
            return precision_planning.run(report, subject)
        if isinstance(analysis, CitedAnalysisIR):
            # verify(...) was refused while compiling: approximate power is a calculation.
            return cited_planning.run(report, subject)
        if isinstance(analysis, CitedAssociationIR):
            return association_planning.run(report, subject)
        if isinstance(analysis, (MatchedAnalysisIR, RateAnalysisIR)):
            if isinstance(subject, FeasibilityIR):
                return run_association_plan(report, subject.lower(), **options)
            candidates = subject.candidates
            bounds = (candidates.min_size, candidates.max_size)
            return run_count_search(
                report,
                _count_template(analysis, subject.target, bounds, subject.minimal),
                bounds,
                minimal=subject.minimal,
                **options,
            )
        if isinstance(analysis, AssociationAnalysisIR):
            if isinstance(subject, FeasibilityIR):
                return run_association_plan(report, subject.lower(), **options)
            if isinstance(subject.candidates, TotalCandidatesIR):
                from statclaim.association import AssociationTest
                from statclaim.observational_planning import TotalPowerPlan

                candidates, target, test = subject.candidates, subject.target, analysis.lower()
                bounds = (candidates.min_n, candidates.max_n)
                template = TotalPowerPlan(
                    AssociationTest(
                        test.design, test.alpha, None, bounds[0], test.exposure, test.outcome
                    ),
                    *group_probabilities(target.at),
                    target.at.exposed_share,
                    target.minimum,
                    target.maximum_typeI,
                    "sample_size",
                    bounds,
                )
                return run_total_search(report, template, bounds, **options)
            target, candidates = subject.target, subject.candidates
            return run_association_search(
                report,
                analysis.lower(),
                (*group_probabilities(target.at), target.minimum, target.maximum_typeI),
                (candidates.min_size, candidates.max_size),
                minimal=subject.minimal,
                ratio=candidates.ratio,
                **options,
            )
        if isinstance(analysis, AnalysisIR) and analysis.alternative == "margin":
            del options["verify"]
            verify = request.operation == "verify"
            if isinstance(subject, FeasibilityIR):
                return run_margin(subject.lower(), verify=verify, **options)
            candidates = subject.candidates
            return run_margin_search(
                analysis.margin_test(subject.target, sizes=(1, 1)),
                (candidates.min_per_arm, candidates.max_per_arm),
                candidates.ratio,
                verify=verify,
                **options,
            )
        if isinstance(subject, FeasibilityIR):
            run = run_power_plan if isinstance(subject.analysis, AnalysisIR) else run_policy_plan
            return run(report, subject.lower(), **options)
        target, candidates = subject.target, subject.candidates
        if isinstance(candidates, TwoStageCandidatesIR):
            return run_two_stage_search(
                report,
                candidates.null_rate,
                (target.at.value, target.minimum, target.maximum_typeI),
                candidates.max_total,
                candidates.criterion,
                **options,
            )
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
            ratio=candidates.ratio,
            alternative=candidates.analysis.alternative,
            **options,
        )
    if isinstance(subject, (RateAnalysisIR, RateResultIR, RateRatioIR, ProportionIR)):
        plan = getattr(getattr(subject, "analysis", subject), "plan", None)
        return run_incidence(
            subject.lower(),
            verify=request.operation == "verify",
            stopping=plan.stopping if plan is not None else "fixed",
            project=project,
            output=output,
            timeout=timeout,
        )
    if isinstance(subject, (MatchedAnalysisIR, MatchedResultIR, MatchedIntervalIR)):
        analysis = getattr(subject, "analysis", subject)
        plan = getattr(analysis, "plan", None)
        return run_matched(
            subject.lower(),
            verify=request.operation == "verify",
            stopping=plan.stopping if plan is not None else "fixed",
            project=project,
            output=output,
            timeout=timeout,
        )
    if isinstance(subject, EffectIntervalIR):
        return run_effect_interval(
            subject.lower(),
            verify=request.operation == "verify",
            project=project,
            output=output,
            timeout=timeout,
        )
    if isinstance(subject, AssociationResultIR):
        return run_association_result(
            subject.lower(),
            verify=request.operation == "verify",
            stopping=subject.analysis.plan.stopping,
            project=project,
            output=output,
            timeout=timeout,
        )
    if request.claim.kind == "interval":
        return run_interval(
            subject.lower(),
            verify=request.operation == "verify",
            project=project,
            output=output,
            timeout=timeout,
        )
    if request.claim.kind == "result" and isinstance(subject, TwoStageObservationIR):
        return run_stage_result(
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
    if isinstance(subject, ComposedFamilyIR) and subject.lower().rules.grade == "cited":
        # A cited combination rule: its contract was checked while compiling.
        report = inspect_request(request)
        report.update(
            status="cited",
            evidence_grade="cited",
            established_properties=composition_claims(subject.lower()),
        )
        return report
    if isinstance(subject, ComposedFamilyIR):
        return run_composition(
            inspect_request(request),
            subject.lower(),
            project=project,
            output=output,
            timeout=timeout,
        )
    if request.claim.kind == "familywise" and isinstance(subject, FamilyIR):
        return verify_family(subject.lower(), project=project, output=output, timeout=timeout)
    margin = subject.analysis if isinstance(subject, ObservationIR) else subject
    if isinstance(margin, AnalysisIR) and margin.alternative == "margin":
        observed = None
        if isinstance(subject, ObservationIR):
            observed = (subject.control_successes, subject.treatment_successes)
        return run_margin(
            margin.margin_test(observed=observed),
            verify=request.operation == "verify",
            project=project,
            output=output,
            timeout=timeout,
        )
    if isinstance(subject, AssociationAnalysisIR):
        return run_association(
            subject.lower(),
            stopping=subject.plan.stopping,
            project=project,
            output=output,
            timeout=timeout,
        )
    if isinstance(subject, RandomisationAnalysisIR):
        return run_randomisation(
            subject.lower(),
            stopping=subject.plan.stopping,
            project=project,
            output=output,
            timeout=timeout,
        )
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


def _effect_line(calculation: dict) -> str:
    """An effect measure's estimate and interval, in decimals."""
    decimal = lambda record: f"{float(Fraction(record['fraction'])):.4g}"  # noqa: E731
    estimate = calculation["estimate"]
    upper = calculation["upper"]
    return (
        f"  {calculation['measure'].replace('_', ' ')} "
        + (f"~ {decimal(estimate)}" if estimate else "undefined (a zero count)")
        + f"; interval = [{decimal(calculation['lower'])}, "
        + (decimal(upper) if upper else "no finite bound")
        + f"] at level {calculation['level']['fraction']}; no formal certificate issued."
    )


def _result_value(
    index: int,
    request: RequestIR,
    source_id: str,
    status: str,
    details: dict,
    diagnostics: tuple[Diagnostic, ...],
) -> ExecutionResult:
    if request.operation in ("calculate", "simulate"):
        return CalculationResult(
            index,
            request.claim,
            source_id,
            status,
            details.get("calculation"),
            details.get("decision"),
            diagnostics,
            request.operation,
        )
    evidence = None
    if status in ("verified", "conditional"):
        evidence = Evidence(
            request.claim,
            details["certificate"],
            tuple(details["established_properties"]),
            tuple(details["required_assumptions"]),
            details["evidence_grade"],
            tuple(details.get("references", ())),
            None,
            tuple(
                details.get("assumptions")
                or [identify(text) for text in details["required_assumptions"]]
            ),
        )
    if status in ("cited", "declared"):
        evidence = Evidence(
            request.claim,
            None,
            tuple(details["established_properties"]),
            tuple(details["required_assumptions"]),
            details["evidence_grade"],
            tuple(details["references"]),
            details["method"],
            tuple(details["assumptions"]),
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
    operations: Collection[str] | None = None,
) -> dict:
    """Elaborate the entire file before any calculation, build, or certificate write.

    Each verified request has its own ordinary certificate. The run receipt is a
    source/IR provenance record, not an additional mathematical certificate.

    `operations` runs only the requests with those operations, such as
    ("calculate",) to recalculate without building proofs. The others are reported
    as not executed.
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
    def wanted(request) -> bool:
        return operations is None or request.operation in operations

    executable = any(
        not blockers and wanted(request)
        for request, blockers in zip(program.requests, obligations, strict=True)
    )
    directory = None
    if executable:
        if output is None:
            parent = project.resolve() / ".statclaim/programs"
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
        elif not wanted(request):
            result = inspect_request(request)
            status = "not_executed"
        else:
            result = _run_request(request, project, directory / f"request-{index:03d}", timeout)
            result = with_population(result, request.claim.subject)
            status = result["status"]
            if request.operation in ("calculate", "simulate"):
                done = "calculated" if request.operation == "calculate" else "simulated"
                status = done if result["decision"] is not None else "unresolved_obligation"
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
                "weakest_link": weakest_link(request.claim.subject),
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
    # A file is only as strong as its weakest part. A claim that went through is
    # counted by the weakest grade anywhere inside it, so a proved combination of
    # cited or declared tests does not make the file look proved.
    for request in report["requests"]:
        if request["status"] in STATUS_GRADES:
            statuses.append(STATUS_OF_GRADE[request["weakest_link"]["grade"]])
    report["status"] = next(
        (
            status
            for status in (
                "unresolved_obligation",
                "declared",
                "cited",
                "conditional",
                "verified",
                "simulated",
            )
            if status in statuses
        ),
        "calculated",
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


def _approximate_lines(details: dict) -> list[str]:
    """Approximate power of a cited test, with the formula and what it rests on."""
    calculation = details["calculation"]
    approximation = calculation.get("approximation", cited_planning.APPROXIMATE)
    lines = []
    observational = [
        f"{key} = {calculation[key]}"
        for key in ("exposed", "unexposed", "cases", "controls", "pairs", "events")
        if key in calculation
    ]
    if "covariates" in calculation:
        observational = [f"n = {calculation['total_sample_size']}"]
        observational.append(f"covariates = {calculation['covariates']}")
        if "degrees_of_freedom" in calculation:
            observational.append(f"degrees of freedom = {calculation['degrees_of_freedom']}")
        if "design_effect" in calculation:
            effective = float(calculation["effective_sample_size"]["decimal_approximation"])
            observational.append(
                f"design effect {calculation['design_effect']['fraction']}, so effectively "
                f"{effective:.1f}"
            )
    if observational and "power" in calculation and "n_control" not in calculation:
        # A cited observational test: power in the study's own units.
        lines += [
            "  " + "; ".join(observational),
            f"  power ~ {float(calculation['power']['decimal_approximation']):.4f} "
            f"({approximation}); "
            f"power target met = {str(calculation['power_target_met']).lower()}",
            f"  rejects when the estimate is {calculation['reject_when']} "
            f"{float(calculation['critical_estimate']['decimal_approximation']):.4g}",
            f"  level {calculation['alpha']['fraction']}; requested Type I bound "
            f"{calculation['maximum_typeI']['fraction']}; Type I target met = "
            f"{str(calculation['typeI_target_met']).lower()}",
        ]
    if "n_control" in calculation:
        lines.append(
            f"  arm sizes = ({calculation['n_control']}, {calculation['n_treatment']}); "
            f"total = {calculation['total_sample_size']}"
        )
        if "clusters_control" in calculation:
            effect = calculation.get("design_effect")
            lines.append(
                f"  clusters = ({calculation['clusters_control']}, "
                f"{calculation['clusters_treatment']}) of "
                f"({calculation['cluster_size_control']['fraction']}, "
                f"{calculation['cluster_size_treatment']['fraction']}) participants; "
                f"icc {calculation['icc']['fraction']}"
                + (f"; design effect {effect['fraction']}" if effect else "")
            )
        if "expected_events" in calculation:
            show = lambda key: float(calculation[key]["decimal_approximation"])  # noqa: E731
            lines.append(
                f"  expected events ~ {show('expected_events'):.2f}; probability of an event by "
                f"the analysis {show('event_probability_control'):.4f} (control), "
                f"{show('event_probability_treatment'):.4f} (treatment)"
            )
        lines += [
            f"  power ~ {float(calculation['power']['decimal_approximation']):.4f} "
            f"({approximation}); "
            f"power target met = {str(calculation['power_target_met']).lower()}",
            f"  rejects when the estimate is {calculation['reject_when']} "
            f"{float(calculation['critical_estimate']['decimal_approximation']):.4g}; "
            f"standard error ~ {float(calculation['standard_error']['decimal_approximation']):.4g}",
            f"  level {calculation['alpha']['fraction']}; requested Type I bound "
            f"{calculation['maximum_typeI']['fraction']}; Type I target met = "
            f"{str(calculation['typeI_target_met']).lower()}",
        ]
    if "candidates_evaluated" in calculation:
        lines.append(f"  candidates evaluated = {calculation['candidates_evaluated']}")
    if "power_ceiling" in calculation:
        lines.append(
            f"  power ceiling ~ {float(calculation['power_ceiling']['decimal_approximation']):.4f}"
            " as clusters grow without bound: more participants per cluster cannot reach the "
            "target; add clusters"
        )
    formula = details["formula"]
    lines.append(f"  Formula: {formula['title']} ({formula['key']}, version {formula['version']})")
    lines.append("  Assumptions:")
    lines.extend(
        f"    [{item['id']}] {item['text']} ({item['status']})" for item in details["assumptions"]
    )
    lines.append("  References:")
    lines.extend(f"    {reference}" for reference in details["references"])
    lines.append(f"  decision = {details['decision']}; no formal certificate issued.")
    return lines


def _type_one_label(calculation: dict) -> str:
    """At the null; for a design judged at several null scenarios, the worst of them."""
    if "null_scenarios" in calculation:
        return "worst Type I over the null scenarios"
    return "Type I at the null"


def _simulated_lines(details: dict) -> list[str]:
    """A simulated estimate: what was simulated, the numbers with intervals, and the basis."""
    calculation = details["calculation"]
    show = lambda record: f"{float(record['decimal_approximation']):.4f}"  # noqa: E731
    lines = [f"  {details['target_property']}"]
    if "power_lower" in calculation:
        lines.append(
            f"  arm sizes = ({calculation['n_control']}, {calculation['n_treatment']}); "
            f"total = {calculation['total_sample_size']}"
            if "n_control" in calculation
            else f"  n = {calculation['total_sample_size']}; covariates = "
            f"{calculation['covariates']}; degrees of freedom = "
            f"{calculation['degrees_of_freedom']}"
        )
        if "null_scenarios" in calculation:
            lines.append(
                f"  re-estimated after {calculation['interim_per_arm']} per arm, ending with "
                f"{calculation['initial_per_arm']} to {calculation['max_per_arm']} per arm; "
                "expected total ~ "
                f"{float(calculation['expected_sample_size']['decimal_approximation']):.1f}"
            )
            for null in calculation["null_scenarios"]:
                lines.append(
                    f"  Type I at sd {null['sd']['fraction']} ~ {show(null['typeI'])} (95% "
                    f"interval {show(null['typeI_lower'])} to {show(null['typeI_upper'])}); "
                    "expected total ~ "
                    f"{float(null['expected_sample_size']['decimal_approximation']):.1f}"
                )
        if "looks" in calculation:
            looks = calculation["looks"]
            lines.append(
                "  looks: "
                + ", ".join(
                    f"({look['n_control']}, {look['n_treatment']}) at {look['alpha']['fraction']}"
                    for look in looks
                )
                + "; stopping ~ "
                + ", ".join(show(look["stop"]) for look in looks)
                + " (under the null "
                + ", ".join(show(look["stop_null"]) for look in looks)
                + ")"
            )
            expected = calculation["expected_sample_size"]["decimal_approximation"]
            null = calculation["expected_sample_size_null"]["decimal_approximation"]
            lines.append(
                f"  expected total ~ {float(expected):.1f} (under the null ~ {float(null):.1f})"
            )
        if "clusters_control" in calculation:
            varied = calculation.get("cluster_size_cv")
            lines.append(
                f"  clusters = ({calculation['clusters_control']}, "
                f"{calculation['clusters_treatment']}) of mean size "
                f"({calculation['cluster_size_control']['fraction']}, "
                f"{calculation['cluster_size_treatment']['fraction']}); icc "
                f"{calculation['icc']['fraction']}"
                + (f"; sizes vary with CV {varied['fraction']}" if varied else "")
            )
        lines += [
            f"  power ~ {show(calculation['power'])} "
            f"(95% interval {show(calculation['power_lower'])} to "
            f"{show(calculation['power_upper'])}); power target met = "
            f"{str(calculation['power_target_met']).lower()}",
            f"  {_type_one_label(calculation)} ~ {show(calculation['typeI'])} (95% interval "
            f"{show(calculation['typeI_lower'])} to {show(calculation['typeI_upper'])}); "
            f"level {calculation['alpha']['fraction']}; Type I target met = "
            f"{str(calculation['typeI_target_met']).lower()}"
            + (
                f" (judged on the simulation: at most {calculation['maximum_typeI']['fraction']})"
                if calculation.get("typeI_judged")
                else ""
            ),
            f"  scenario: {calculation['scenario']}",
        ]
    if "candidates_evaluated" in calculation:
        lines.append(
            f"  candidates evaluated = {calculation['candidates_evaluated']}; "
            f"confirmation runs = {calculation['confirmations']}"
        )
    simulation = details["simulation"]
    lines.append(
        f"  Simulation: {simulation['title']} ({simulation['key']}, version "
        f"{simulation['version']}); {simulation['runs']:,} runs, seed {simulation['seed']}; "
        f"engine version {simulation['engine_version']}; {simulation['interval']} intervals"
    )
    lines.append("  Assumptions:")
    lines.extend(
        f"    [{item['id']}] {item['text']} ({item['status']})" for item in details["assumptions"]
    )
    lines.append("  References:")
    lines.extend(f"    {reference}" for reference in details["references"])
    lines.append(f"  decision = {details['decision']}; an estimate, not evidence.")
    return lines


def _group_lines(calculation: dict) -> list[str]:
    """Group sizes of an observational design, and what its planning point implies."""
    if "cases" in calculation:
        sizes = f"cases = {calculation['cases']}; controls = {calculation['controls']}"
        point = (
            f"exposed: {calculation['exposure_cases']['fraction']} of cases, "
            f"{calculation['exposure_controls']['fraction']} of controls"
        )
    else:
        sizes = f"exposed = {calculation['exposed']}; unexposed = {calculation['unexposed']}"
        point = (
            f"risk {calculation['risk_exposed']['fraction']} with exposure, "
            f"{calculation['risk_unexposed']['fraction']} without"
        )
    measures = [
        f"{name.replace('_', ' ')} {float(calculation[name]['decimal_approximation']):.4g}"
        for name in ("risk_ratio", "odds_ratio")
        if calculation.get(name) is not None
    ]
    if measures:
        point += f" ({', '.join(measures)})"
    return [f"  {sizes}; total = {calculation['total_sample_size']}", f"  planning point: {point}"]


def _precision_lines(details: dict) -> list[str]:
    """A planned interval's margin of error, and its assurance when asked."""
    calculation = details["calculation"]

    def show(record):
        return "unbounded" if record is None else f"{float(record['decimal_approximation']):.4g}"

    lines = []
    sizes = [
        f"{key.replace('_', ' ')} = {calculation[key]}"
        for key in (
            "n_control",
            "n_treatment",
            "unexposed",
            "exposed",
            "controls",
            "cases",
            "pairs",
            "events",
        )
        if key in calculation
    ]
    if not sizes and "total_sample_size" in calculation:
        sizes = [f"n = {calculation['total_sample_size']}"]
    if sizes:
        lines.append("  " + "; ".join(sizes))
    if "margin_achieved" in calculation:
        words = "relative margin of error" if calculation["relative"] else "margin of error"
        lines += [
            f"  {calculation['method']} {calculation['level']['fraction']} interval for the "
            f"{calculation['measure'].replace('_', ' ')} at the expected counts: "
            f"{show(calculation['lower'])} to {show(calculation['upper'])} around "
            f"{show(calculation['estimate'])}",
            f"  {words} {show(calculation['margin_achieved'])}; target "
            f"{calculation['target_margin']['fraction']}",
        ]
    if "assurance" in calculation:
        lines.append(
            f"  assurance {show(calculation['assurance'])}, the chance the interval is narrow "
            f"enough; required {calculation['minimum_assurance']['fraction']}"
        )
    lines.append(f"  precision target met = {str(calculation['precision_target_met']).lower()}")
    if "candidates_evaluated" in calculation:
        lines.append(f"  candidates evaluated = {calculation['candidates_evaluated']}")
    if "note" in calculation:
        lines.append(f"  note: {calculation['note']}")
    lines.append("  Assumptions:")
    lines.extend(f"    {item['text']}" for item in details.get("assumptions", []))
    lines.append(f"  decision = {details['decision']}; a calculation, not checked by Lean.")
    return lines


def _planning_lines(details: dict) -> list[str]:
    if details.get("verification_scope") == "precision":
        return _precision_lines(details)
    if details.get("verification_scope") == "cited_planning":
        return _approximate_lines(details)
    calculation = details["calculation"]
    lines = []
    if "n_control" in calculation:
        lines.append(
            f"  arm sizes = ({calculation['n_control']}, {calculation['n_treatment']}); "
            f"total = {calculation['total_sample_size']}"
        )
    if "cases" in calculation or "exposed" in calculation:
        lines.extend(_group_lines(calculation))
    if "exposed_share" in calculation:
        noun = "risk" if "risk_exposed" in calculation else "prevalence"
        measures = ", ".join(
            f"{name.replace('_', ' ')} {float(calculation[name]['decimal_approximation']):.4g}"
            for name in (f"{noun}_ratio", "odds_ratio")
            if calculation.get(name) is not None
        )
        lines += [
            f"  n = {calculation['total_sample_size']}; expected exposed ~ "
            f"{float(calculation['expected_exposed']['decimal_approximation']):.4g}",
            f"  planning point: {calculation['exposed_share']['fraction']} exposed; {noun} "
            f"{calculation[f'{noun}_exposed']['fraction']} with exposure, "
            f"{calculation[f'{noun}_unexposed']['fraction']} without"
            + (f" ({measures})" if measures else ""),
        ]
    if "pairs" in calculation:
        lines += [
            f"  pairs = {calculation['pairs']}; expected discordant pairs ~ "
            f"{float(calculation['expected_discordant_pairs']['decimal_approximation']):.4g}",
            f"  planning point: {calculation['discordant']['fraction']} of pairs discordant; "
            f"conditional odds ratio {calculation['odds_ratio']['fraction']} (the case is the "
            f"exposed one in {calculation['case_exposed_share']['fraction']} of them)",
        ]
    if "events" in calculation:
        lines += [
            f"  events = {calculation['events']}",
            f"  planning point: rate ratio {calculation['rate_ratio']['fraction']}; "
            f"{calculation['exposed_time_share']['fraction']} of person-time exposed, so "
            f"{calculation['exposed_event_share']['fraction']} of events among the exposed",
        ]
    if "critical_value" in calculation:
        lines.append(
            f"  n = {calculation['n']}; reject at {calculation['critical_value']} or more "
            f"responses; Type I at the null rate ~ {calculation['typeI']['decimal_approximation']}"
        )
    if "n_stage1" in calculation:
        if "continue_above" in calculation:
            lines.append(
                f"  continue above {calculation['continue_above']} responses in stage one; "
                f"reject above {calculation['reject_above']} in total "
                f"({calculation['criterion']} design; ranking is calculated, not certified)"
            )
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
    if "minimum_sample_size_claim" in calculation:
        lines.append(
            f"  candidates evaluated = {calculation['candidates_evaluated']}; "
            "smallest-in-range claim: "
            f"{calculation['minimum_sample_size_claim'].replace('_', ' ')}"
        )
    elif "candidates_evaluated" in calculation:
        lines.append(f"  candidates evaluated = {calculation['candidates_evaluated']}")
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
        lines.extend(_weakest_line(request) if "weakest_link" in request else [])
        if details["certificate_issued"]:
            evidence = request["value"]["evidence"]
            lines.append(
                f"  Evidence: {GRADES[evidence['grade']].label}; "
                f"guarantee: {SCOPES[evidence['scope']]}"
            )
            for claim in details["established_properties"]:
                lines.append(f"  {claim}")
            lines.append("  Assumptions:")
            lines.extend(f"    {assumption}" for assumption in details["required_assumptions"])
            if details.get("references"):
                lines.append("  References:")
                lines.extend(f"    {reference}" for reference in details["references"])
            lines.append(f"  Certificate: {details['certificate']['directory']}")
        elif request["status"] in ("cited", "declared"):
            evidence = request["value"]["evidence"]
            lines.append(
                f"  Evidence: {GRADES[evidence['grade']].label}; "
                f"guarantee: {SCOPES[evidence['scope']]}"
            )
            method = details["method"]
            lines.append(
                f"  Method: {method['title']} ({method['key']}, version {method['version']})"
            )
            lines.append(f"  {details['target_property']}")
            lines.append("  Assumptions:")
            lines.extend(
                f"    [{item['id']}] {item['text']} ({item['status']})"
                for item in evidence["assumptions"]
            )
            lines.append("  References:")
            lines.extend(f"    {reference}" for reference in details["references"])
        elif request["status"] in ("planned", "blocked"):
            lines.append(f"  {details['target_property']}")
            lines.append("  Assumptions:")
            lines.extend(f"    {assumption}" for assumption in details["required_assumptions"])
        elif request["status"] == "simulated":
            lines.extend(_simulated_lines(details))
        elif request["status"] == "calculated" and request["claim"] in ("meets", "sample_size"):
            lines.extend(_planning_lines(details))
        elif request["status"] == "calculated" and "measure" in details["calculation"]:
            lines.append(_effect_line(details["calculation"]))
        elif (
            request["status"] == "calculated"
            and "exposed_time" in details["calculation"]
            and ("p_value" in details["calculation"])
        ):
            calculation = details["calculation"]
            p_value = float(Fraction(calculation["p_value"]["fraction"]))
            lines.append(
                f"  {calculation['events']} events; p-value ~ {p_value:.4g}; "
                f"decision = {details['decision']}; no formal certificate issued."
            )
        elif request["status"] == "calculated" and "discordant_pairs" in details["calculation"]:
            calculation = details["calculation"]
            p_value = float(Fraction(calculation["p_value"]["fraction"]))
            lines.append(
                f"  {calculation['discordant_pairs']} discordant pairs; p-value ~ {p_value:.4g}; "
                f"decision = {details['decision']}; no formal certificate issued."
            )
        elif request["status"] == "calculated" and "exposed_cases" in details["calculation"]:
            calculation = details["calculation"]
            p_value = float(Fraction(calculation["p_value"]["fraction"]))
            lines.append(
                f"  p-value ~ {p_value:.4g} (exact: {calculation['p_value']['fraction']}); "
                f"decision = {details['decision']}; no formal certificate issued."
            )
        elif request["status"] == "calculated" and request["claim"] == "interval":
            calculation = details["calculation"]
            lines.append(
                (
                    f"  {calculation['responses']} responses out of {calculation['n']}; "
                    if "responses" in calculation
                    else f"  control {calculation['control_successes']} of "
                    f"{calculation['n_control']}, treatment "
                    f"{calculation['treatment_successes']} of {calculation['n_treatment']}; "
                )
                + f"estimate ~ {float(Fraction(calculation['estimate']['fraction'])):.4f}; "
                f"interval = [{calculation['lower']['decimal_approximation']}, "
                f"{calculation['upper']['decimal_approximation']}] at level "
                f"{calculation['level']['fraction']}; no formal certificate issued."
            )
        elif (
            request["status"] == "calculated"
            and "needed_treatment_successes" in details["calculation"]
        ):
            calculation = details["calculation"]
            lines.append(
                "  observed difference ~ "
                f"{calculation['observed_difference']['decimal_approximation']}; needs at least "
                f"{calculation['needed_treatment_successes']} treatment successes; "
                f"decision = {details['decision']}; no formal certificate issued."
            )
        elif request["status"] == "calculated" and "stage1_responses" in details["calculation"]:
            calculation = details["calculation"]
            second = calculation["stage2_responses"]
            lines.append(
                f"  stage one: {calculation['stage1_responses']} of {calculation['n_stage1']}; "
                + (
                    "stopped at the interim look; "
                    if second is None
                    else f"stage two: {second} of {calculation['n_stage2']}; "
                )
                + f"decision = {details['decision']}; no formal certificate issued."
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
    if any(request["status"] in STATUS_GRADES for request in report["requests"]):
        lines.append(SCOPE_NOTE)
    if report["status"] == "elaborated":
        lines.append("Structural checks passed; no Lean proof or certificate was produced.")
    if report.get("run_directory"):
        lines.append(f"Source snapshot and run report: {report['run_directory']}")
    return "\n".join(lines)
