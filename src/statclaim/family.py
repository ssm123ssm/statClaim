"""Declarations for a family of Fisher analyses with explicit marginal contracts."""

from dataclasses import dataclass
from fractions import Fraction

from statclaim.design import Design
from statclaim.fisher import validate_alpha

MAX_ENDPOINTS = 20


@dataclass(frozen=True)
class Endpoint:
    name: str
    design: Design

    def __post_init__(self):
        if not isinstance(self.name, str) or not self.name.strip():
            raise ValueError("Each analysis needs a nonempty name.")
        if not isinstance(self.design, Design):
            raise ValueError("Each analysis needs a validated Design.")


@dataclass(frozen=True)
class FisherFamily:
    alpha: Fraction
    endpoints: tuple[Endpoint, ...]

    def __post_init__(self):
        validate_alpha(self.alpha)
        if not isinstance(self.endpoints, tuple) or not 2 <= len(self.endpoints) <= MAX_ENDPOINTS:
            raise ValueError(f"A Fisher family needs between 2 and {MAX_ENDPOINTS} analyses.")
        if not all(isinstance(endpoint, Endpoint) for endpoint in self.endpoints):
            raise ValueError("Invalid endpoint declaration.")
        if len({endpoint.name for endpoint in self.endpoints}) != len(self.endpoints):
            raise ValueError("Analysis names must be distinct.")

    @property
    def allocated_alpha(self) -> Fraction:
        return sum((endpoint.design.alpha for endpoint in self.endpoints), Fraction())

    @property
    def supported(self) -> bool:
        return all(
            e.design.stopping == "fixed" and e.design.alternative == "two_sided"
            for e in self.endpoints
        )


def inspect_family(family: FisherFamily) -> dict:
    obligations = [
        "Check each marginal Fisher guarantee and compose them with the Bonferroni theorem.",
        "Supply the declared marginal sampling laws in an actual application.",
    ]
    if family.allocated_alpha > family.alpha:
        obligations.append("The allocated alpha exceeds the requested familywise bound.")
    if not family.supported:
        obligations.append("Data-dependent stopping requires a separately justified sampling law.")
    return {
        "schema_version": 1,
        "status": "unresolved_obligation",
        "verification_scope": "family",
        "certificate_issued": False,
        "backend_invoked": False,
        "family": {
            "alpha": str(family.alpha),
            "allocated_alpha": str(family.allocated_alpha),
            "joint_law": "binomial_marginals",
            "analyses": [
                {
                    "name": e.name,
                    "n_control": e.design.n_control,
                    "n_treatment": e.design.n_treatment,
                    "stopping": e.design.stopping,
                    "alpha": str(e.design.alpha),
                }
                for e in family.endpoints
            ],
        },
        "target_property": "Strong familywise error: probability of any rejection of a true null "
        f"<= {family.alpha}, for every joint parameter configuration.",
        "required_assumptions": list(FAMILY_ASSUMPTIONS),
        "established_properties": [],
        "outstanding_obligations": obligations,
        "evidence": [],
        "formal_reference": {
            "theorem": "StatClaim.Modules.FisherFamilyN.strong_control",
            "checked_in_this_run": False,
            "application_to_this_run": "unresolved_family_verification",
        },
    }


FAMILY_ASSUMPTIONS = [
    "Each outcome's two arms follow the declared independent-binomial marginal model.",
    "Positive sample sizes, the analyses and the alpha allocation are fixed before outcomes.",
    "The joint sampling law is a probability law with those binomial marginals; "
    "dependence between outcomes is unrestricted.",
    "Each endpoint null is equality of its arm probabilities; the bound counts rejections "
    "only of nulls that are true, including mixed true/false configurations.",
]
