"""Parse the initial design vocabulary without claiming mathematical verification."""

import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from statproof.fisher import TEST_ID


@dataclass(frozen=True)
class Design:
    n_control: int
    n_treatment: int
    stopping: Literal["fixed", "data_dependent"]

    def __post_init__(self) -> None:
        for name in ("n_control", "n_treatment"):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive integer.")
        if self.stopping not in ("fixed", "data_dependent"):
            raise ValueError("stopping must be 'fixed' or 'data_dependent'.")


def load_design(path: Path) -> Design:
    with path.open("rb") as handle:
        data = tomllib.load(handle)
    if set(data) != {"design"} or not isinstance(data["design"], dict):
        raise ValueError("Expected exactly one [design] table.")
    fields = data["design"]
    expected = {"module", "n_control", "n_treatment", "stopping"}
    if set(fields) != expected:
        raise ValueError(f"[design] must contain exactly: {', '.join(sorted(expected))}.")
    if fields["module"] != "two_arm_binomial":
        raise ValueError("Only the two_arm_binomial module is recognized.")
    return Design(fields["n_control"], fields["n_treatment"], fields["stopping"])


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
        "module_version": "0.1.0",
        "specified_test": TEST_ID,
        "verification_scope": "design",
        "formal_reference": {
            "theorem": "StatProof.Modules.Fisher.typeI_statement",
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
        "target_property": "Null rejection probability <= 1/20 for every common p in [0, 1]",
        "planned_backend": "Lean 4 + Mathlib",
        "backend_invoked": False,
        "evidence": [],
        "established_properties": [],
        "required_assumptions": [
            "Two independent binomial samples.",
            "Positive sample sizes fixed before observing outcomes.",
            "The null hypothesis is equal success probabilities in the two arms.",
        ],
        "outstanding_obligations": obligations,
    }
