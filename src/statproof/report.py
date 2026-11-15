"""Combine exact numerical results with explicit formal-verification status."""

from pathlib import Path

from statproof.design import Design, inspect_design
from statproof.family import FisherFamily, inspect_family
from statproof.fisher import FisherResult, fisher_exact
from statproof.verification import (
    DESIGN_ASSUMPTIONS,
    VerificationError,
    certify_design,
    certify_family,
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
