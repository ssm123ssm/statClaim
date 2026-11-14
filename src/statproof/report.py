"""Combine exact numerical results with explicit formal-verification status."""

from statproof.design import Design, inspect_design
from statproof.fisher import fisher_exact


def test_design(design: Design, *, control_successes: int, treatment_successes: int) -> dict:
    result = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
    )
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
