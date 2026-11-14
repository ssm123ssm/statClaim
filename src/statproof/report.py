"""Combine exact numerical results with explicit formal-verification status."""

from pathlib import Path

from statproof.design import Design, inspect_design
from statproof.fisher import FisherResult, fisher_exact
from statproof.verification import CLAIMS, VerificationError, certify_result, digest


def test_design(design: Design, *, control_successes: int, treatment_successes: int) -> dict:
    result = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
    )
    return _result_report(design, result)


def _result_report(design: Design, result: FisherResult) -> dict:
    report = inspect_design(design)
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
    report.update(
        {
            "status": "verified",
            "certificate_issued": True,
            "backend_invoked": True,
            "established_properties": list(CLAIMS),
            "outstanding_obligations": [],
            "required_assumptions": certificate["assumptions"],
            "trusted_components": certificate["trusted_components"],
            "certificate": {
                "certificate_id": certificate["certificate_id"],
                "directory": str(bundle),
                "file": str(bundle / "certificate.json"),
                "sha256": digest((bundle / "certificate.json").read_bytes()),
            },
            "decision_scope": (
                "Lean-checked result and fixed-sample error bound under the listed assumptions."
            ),
            "limitations": [
                "This result was checked; the Python program is not universally verified.",
                "The sampling assumptions and provenance of the supplied counts "
                "are explicitly assumed.",
            ],
        }
    )
    report["formal_reference"]["checked_in_this_run"] = True
    report["formal_reference"]["application_to_this_run"] = "verified_result_only"
    report["evidence"].append(
        {
            "kind": "formal_proof",
            "scope": list(CLAIMS),
            "theorems": certificate["theorems"],
            "backend": certificate["environment"]["lean_version"],
            "input_sha256": certificate["input_sha256"],
            "certificate_id": certificate["certificate_id"],
        }
    )
    return report
