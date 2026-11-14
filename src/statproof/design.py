"""Parse the initial design vocabulary without claiming mathematical verification."""

import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Literal


@dataclass(frozen=True)
class Design:
    n_control: int
    n_treatment: int
    stopping: Literal["fixed", "data_dependent"]


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
    for name in ("n_control", "n_treatment"):
        if type(fields[name]) is not int or fields[name] <= 0:
            raise ValueError(f"{name} must be a positive integer.")
    if fields["stopping"] not in ("fixed", "data_dependent"):
        raise ValueError("stopping must be 'fixed' or 'data_dependent'.")
    return Design(fields["n_control"], fields["n_treatment"], fields["stopping"])


def inspect_design(design: Design) -> dict:
    """Return a planning report. This function never issues a certificate."""
    obligations = [
        "Specify the exact test and its rejection rule.",
        "Prove the null rejection probability is at most 1/20 in Lean.",
        "Validate the translation from declarations to the formal theorem and report.",
    ]
    if design.stopping == "data_dependent":
        obligations.append(
            "Data-dependent stopping needs a separate justification: the planned "
            "fixed-sample theorem would not establish this procedure's guarantee. "
            "This is not evidence of inflated error."
        )
    return {
        "schema_version": 1,
        "module": "two_arm_binomial",
        "module_version": "0.1.0",
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
