"""Combine exact numerical results with explicit formal-verification status."""

from pathlib import Path

from statproof.design import Design, inspect_design
from statproof.family import FisherFamily, inspect_family
from statproof.fisher import FisherResult, fisher_exact
from statproof.planning import PowerPlan, TwoStagePlan, search_equal_arms
from statproof.verification import (
    DESIGN_ASSUMPTIONS,
    VerificationError,
    certify_design,
    certify_family,
    certify_planning,
    certify_policy,
    certify_result,
    digest,
)


def test_design(design: Design, *, control_successes: int, treatment_successes: int) -> dict:
    result = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
        alpha=design.alpha,
    )
    return _result_report(design, result)


def _result_report(design: Design, result: FisherResult) -> dict:
    report = inspect_design(design)
    report["verification_scope"] = "result"
    report["formal_reference"].update(
        theorem="StatProof.fisher_typeI_error_le_alpha",
        application_to_this_run="unresolved_implementation_correspondence",
    )
    report["outstanding_obligations"] = [
        "Check the exact p-value, table probability, and decision against the Lean definition.",
        "Bind the result and model guarantee to checked artifacts and the exact inputs.",
        *[item for item in report["outstanding_obligations"] if "Data-dependent" in item],
    ]
    report["calculation"] = result.to_dict()
    report["evidence"] = [
        {
            "kind": "exact_computation",
            "scope": "Conditional table probabilities, two-sided p-value, and threshold comparison",
            "implementation": "Python integer combinatorics and fractions.Fraction",
            "formally_verified_implementation": False,
        }
    ]
    if design.stopping == "fixed":
        report["decision"] = "reject_null" if result.reject_null else "do_not_reject_null"
        report["decision_scope"] = (
            "Decision of the specified fixed-sample test under the listed sampling assumptions. "
            "This is an exact computation, not a Lean verification certificate."
        )
    else:
        report["decision"] = None
        report["decision_scope"] = (
            "The fixed-margin p-value and its threshold comparison were computed, but no "
            "decision is endorsed for the data-dependent stopping procedure. "
            "Its Type I error guarantee needs separate justification."
        )
    return report


def verify_design(
    design: Design,
    *,
    control_successes: int,
    treatment_successes: int,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> dict:
    result = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
        alpha=design.alpha,
    )
    report = _result_report(design, result)
    if design.stopping != "fixed":
        report["verification"] = {
            "stage": "sampling_scope",
            "message": (
                "Data-dependent stopping needs a separate justification; no certificate issued."
            ),
        }
        return report
    try:
        certificate, bundle = certify_result(
            design,
            result,
            project=project,
            output=output,
            timeout=timeout,
        )
    except VerificationError as error:
        report["backend_invoked"] = error.stage != "project"
        report["verification"] = {
            "stage": error.stage,
            "message": str(error),
            "attempt_directory": str(error.bundle) if error.bundle else None,
        }
        return report
    return _verified_report(report, certificate, bundle, scope="result")


def verify_design_only(
    design: Design,
    *,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> dict:
    """Check a pre-data design guarantee; no numerical calculation is performed."""
    report = inspect_design(design)
    report["verification_scope"] = "design"
    report["required_assumptions"] = list(DESIGN_ASSUMPTIONS)
    report["formal_reference"]["theorem"] = "StatProof.Modules.Fisher.typeI_statement"
    report["formal_reference"]["application_to_this_run"] = "unresolved_design_verification"
    report["outstanding_obligations"] = [
        "Instantiate the declared analysis, discharge sampling compatibility, "
        "and check the uniform Type I error bound in Lean.",
    ]
    if design.stopping != "fixed":
        report["outstanding_obligations"] = [
            "Specify and justify the sampling law induced by data-dependent stopping.",
            "Establish compatibility or provide a suitable replacement error-bound theorem.",
        ]
        report["verification"] = {
            "stage": "sampling_scope",
            "message": "Data-dependent stopping needs separate justification. "
            "The fixed-sample theorem does not establish its guarantee; "
            "this is not evidence of inflated error.",
        }
        return report
    try:
        certificate, bundle = certify_design(
            design, project=project, output=output, timeout=timeout
        )
    except VerificationError as error:
        report["backend_invoked"] = error.stage != "project"
        report["verification"] = {
            "stage": error.stage,
            "message": str(error),
            "attempt_directory": str(error.bundle) if error.bundle else None,
        }
        return report
    return _verified_report(report, certificate, bundle, scope="design")


def _verified_report(report: dict, certificate: dict, bundle: Path, *, scope: str) -> dict:
    report.update(
        {
            "status": "verified",
            "certificate_issued": True,
            "backend_invoked": True,
            "verification_scope": scope,
            "established_properties": list(certificate["claims"]),
            "outstanding_obligations": [],
            "required_assumptions": certificate["assumptions"],
            "trusted_components": certificate["trusted_components"],
            "certificate": {
                "certificate_id": certificate["certificate_id"],
                "directory": str(bundle),
                "file": str(bundle / "certificate.json"),
                "sha256": digest((bundle / "certificate.json").read_bytes()),
            },
            "limitations": [
                "Real-world sampling assumptions are explicitly assumed.",
                "The certificate establishes only its named properties; "
                "power, coverage, and universal study validity are outside its scope.",
            ],
        }
    )
    if scope == "result":
        report["decision_scope"] = (
            "Lean-checked result and fixed-sample error bound under the listed assumptions."
        )
        report["limitations"].append(
            "This result was checked; the Python program is not universally verified."
        )
    else:
        report["limitations"].append(
            "No observations, p-values, or numerical results were checked."
        )
    report["formal_reference"].update(
        theorem=certificate["general_theorem"],
        checked_in_this_run=True,
        application_to_this_run=f"verified_{scope}_only",
    )
    report["evidence"].append(
        {
            "kind": "formal_proof",
            "scope": list(certificate["claims"]),
            "theorems": certificate["theorems"],
            "backend": certificate["environment"]["lean_version"],
            "input_sha256": certificate["input_sha256"],
            "certificate_id": certificate["certificate_id"],
        }
    )
    return report


def verify_family(
    family: FisherFamily, *, project: Path, output: Path | None = None, timeout: float = 120
) -> dict:
    report = inspect_family(family)
    if not family.supported or family.allocated_alpha > family.alpha:
        report["verification"] = {
            "stage": "allocation" if family.supported else "sampling_scope",
            "message": "The allocated alpha exceeds the requested familywise bound."
            if family.supported
            else "Data-dependent stopping needs separate justification; "
            "this is not evidence of inflated error.",
        }
        return report
    try:
        certificate, bundle = certify_family(
            family, project=project, output=output, timeout=timeout
        )
    except VerificationError as error:
        report["backend_invoked"] = error.stage != "project"
        report["verification"] = {
            "stage": error.stage,
            "message": str(error),
            "attempt_directory": str(error.bundle) if error.bundle else None,
        }
        return report
    return _verified_report(report, certificate, bundle, scope="family")


def planning_report(scope: str, target_property: str, assumptions: list[str]) -> dict:
    """A planning request before execution. This never issues a certificate."""
    return {
        "schema_version": 1,
        "status": "unresolved_obligation",
        "verification_scope": scope,
        "certificate_issued": False,
        "backend_invoked": False,
        "target_property": target_property,
        "required_assumptions": list(assumptions),
        "established_properties": [],
        "evidence": [],
        "calculation": None,
        "decision": None,
    }


def _approx(record: dict) -> str:
    return f"approximately {record['decimal_approximation']}"


def _unmet(report: dict, stage: str, code: str, message: str) -> dict:
    report["verification"] = {"stage": stage, "code": code, "message": message}
    return report


def _certified(report: dict, certify, plan, *, project: Path, output, timeout: float) -> dict:
    try:
        certificate, bundle = certify(plan, project=project, output=output, timeout=timeout)
    except VerificationError as error:
        report["backend_invoked"] = error.stage != "project"
        report["verification"] = {
            "stage": error.stage,
            "message": str(error),
            "attempt_directory": str(error.bundle) if error.bundle else None,
        }
        return report
    report.update(
        status="verified",
        certificate_issued=True,
        backend_invoked=True,
        established_properties=list(certificate["claims"]),
        required_assumptions=certificate["assumptions"],
        trusted_components=certificate["trusted_components"],
        certificate={
            "certificate_id": certificate["certificate_id"],
            "directory": str(bundle),
            "file": str(bundle / "certificate.json"),
            "sha256": digest((bundle / "certificate.json").read_bytes()),
        },
        limitations=[
            "Real-world sampling assumptions and planning inputs are explicitly assumed.",
            "Bounds are checked, not exact values; calculated values are display information.",
        ],
    )
    report["evidence"].append(
        {
            "kind": "formal_proof",
            "scope": list(certificate["claims"]),
            "theorems": certificate["theorems"],
            "backend": certificate["environment"]["lean_version"],
            "input_sha256": certificate["input_sha256"],
            "certificate_id": certificate["certificate_id"],
        }
    )
    return report


def run_power_plan(
    report: dict, plan: PowerPlan, *, verify: bool, project: Path, output, timeout: float
) -> dict:
    """Assess a fixed Fisher design; verify certifies only when every component is met."""
    calculation = plan.evaluate()
    report["calculation"] = calculation
    met = calculation["power_target_met"] and calculation["typeI_target_met"]
    report["decision"] = "target_met" if met else "target_not_met"
    report["components"] = {
        "typeI": "supported_by_theorem" if calculation["typeI_target_met"] else "not_established",
        "power": "met" if calculation["power_target_met"] else "not_met",
    }
    if not verify:
        return report
    if not calculation["typeI_target_met"]:
        return _unmet(
            report,
            "typeI_target",
            "typeI_target_not_established",
            f"The analysis's alpha {plan.design.alpha} exceeds the requested Type I bound "
            f"{plan.maximum_typeI}. The Fisher theorem bounds error by alpha only; "
            "this is not evidence that the actual error exceeds the request.",
        )
    if not calculation["power_target_met"]:
        return _unmet(
            report,
            "power_target",
            "power_target_not_met",
            f"Calculated power, {_approx(calculation['power'])}, is below the required "
            f"{plan.minimum_power} at the planning point. No evidence is issued for the "
            "combined planning claim. The Type I component is supported separately by the "
            "Fisher theorem. This says nothing about whether the null is true.",
        )
    return _certified(
        report, certify_planning, plan, project=project, output=output, timeout=timeout
    )


def run_sample_size(
    report: dict,
    alpha,
    target: tuple,
    bounds: tuple[int, int],
    *,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for a sufficient equal-arm size; minimality is never claimed."""
    p_control, p_treatment, minimum, maximum = target
    plan, evaluated = search_equal_arms(alpha, p_control, p_treatment, minimum, maximum, *bounds)
    search = {
        "min_per_arm": bounds[0],
        "max_per_arm": bounds[1],
        "candidates_evaluated": evaluated,
        "minimum_sample_size_claim": "not_requested",
    }
    if plan is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No equal-arm size from {bounds[0]} to {bounds[1]} meets the power target. "
                "Nothing is claimed about other designs or larger samples.",
            )
        return report
    report = run_power_plan(
        report, plan, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {**report["calculation"], **search}
    return report


def run_policy_plan(
    report: dict, plan: TwoStagePlan, *, verify: bool, project: Path, output, timeout: float
) -> dict:
    """Assess a complete two-stage policy at its declared null and alternative rates."""
    calculation = plan.evaluate()
    report["calculation"] = calculation
    met = calculation["power_target_met"] and calculation["typeI_target_met"]
    report["decision"] = "target_met" if met else "target_not_met"
    report["components"] = {
        "typeI": "met" if calculation["typeI_target_met"] else "not_met",
        "power": "met" if calculation["power_target_met"] else "not_met",
    }
    if not verify:
        return report
    if not calculation["typeI_target_met"]:
        return _unmet(
            report,
            "typeI_target",
            "typeI_target_not_met",
            f"The policy's calculated rejection probability at the null rate, "
            f"{_approx(calculation['typeI'])}, exceeds the requested {plan.maximum_typeI}. "
            "No evidence is issued.",
        )
    if not calculation["power_target_met"]:
        return _unmet(
            report,
            "power_target",
            "power_target_not_met",
            f"Calculated power, {_approx(calculation['power'])}, is below the required "
            f"{plan.minimum_power} at the alternative rate. No evidence is issued for the "
            "combined planning claim.",
        )
    return _certified(report, certify_policy, plan, project=project, output=output, timeout=timeout)
