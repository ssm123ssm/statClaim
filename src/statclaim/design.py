"""Parse the initial design vocabulary without claiming mathematical verification."""

from dataclasses import dataclass
from fractions import Fraction
from typing import Literal

from statclaim.fisher import ALPHA, ALTERNATIVES, test_id, validate_alpha


@dataclass(frozen=True)
class Design:
    n_control: int
    n_treatment: int
    stopping: Literal["fixed", "data_dependent"]
    alpha: Fraction = ALPHA
    alternative: str = "two_sided"

    def __post_init__(self) -> None:
        validate_alpha(self.alpha)
        if self.alternative not in ALTERNATIVES:
            raise ValueError("alternative must be 'two_sided' or 'greater'.")
        for name in ("n_control", "n_treatment"):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive integer.")
        if self.stopping not in ("fixed", "data_dependent"):
            raise ValueError("stopping must be 'fixed' or 'data_dependent'.")


def inspect_design(design: Design) -> dict:
    """Return a planning report. This function never issues a certificate."""
    obligations = [
        "Instantiate the declared model, sampling plan, null, and Fisher procedure in Lean.",
        "Discharge sampling compatibility and check the uniform Type I error bound.",
        "Bind the design claim to checked artifacts, inputs, and backend/module versions.",
    ]
    if design.stopping == "data_dependent":
        obligations.append(
            "Data-dependent stopping needs a separate justification: the "
            "fixed-sample theorem does not establish this procedure's guarantee. "
            "This is not evidence of inflated error."
        )
    return {
        "schema_version": 1,
        "module": "two_arm_binomial",
        "module_version": "0.2.0",
        "specified_test": test_id(design.alternative),
        "verification_scope": "design",
        "formal_reference": {
            "theorem": "StatClaim.Modules.Fisher.typeI_statement",
            "scope": (
                "The Lean-defined rejection event under the product of two binomial "
                "distributions with a common success probability in [0, 1]."
            ),
            "checked_in_this_run": False,
            "application_to_this_run": "unresolved_design_verification",
        },
        "status": "unresolved_obligation",
        "certificate_issued": False,
        "design": {
            "n_control": design.n_control,
            "n_treatment": design.n_treatment,
            "stopping": design.stopping,
        },
        "target_property": (
            f"Null rejection probability <= {design.alpha} for every common p in [0, 1]"
            if design.alternative == "two_sided"
            else f"Null rejection probability <= {design.alpha} whenever the treatment "
            "success probability is at most the control's"
        ),
        "analysis": {"alpha": str(design.alpha)},
        "planned_backend": "Lean 4 + Mathlib",
        "backend_invoked": False,
        "evidence": [],
        "established_properties": [],
        "required_assumptions": [
            "Two independent binomial samples.",
            "Positive sample sizes fixed before observing outcomes.",
            "The null hypothesis is equal success probabilities in the two arms."
            if design.alternative == "two_sided"
            else "The null hypothesis is that the treatment success probability is at most "
            "the control's.",
        ],
        "outstanding_obligations": obligations,
    }
