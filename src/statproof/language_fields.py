"""The public field schema shared by elaboration, runtime, and editor tooling.

Only explicitly listed fields are exposed. Optional receivers propagate absence;
their fields remain optional, so they cannot be mistaken for checked evidence.
"""

from dataclasses import dataclass
from fractions import Fraction

from statproof.language import (
    AnalysisIR,
    CalculationResultIR,
    ClaimIR,
    FamilyIR,
    FieldIR,
    HypothesisIR,
    LocatedValue,
    ModelIR,
    ObservationIR,
    PlanIR,
    ValueType,
    VerificationResultIR,
    fail,
)
from statproof.language_syntax import Diagnostic, Span
from statproof.language_values import (
    CalculationDetails,
    CalculationResult,
    CertificateReference,
    Evidence,
    VerificationResult,
)


@dataclass(frozen=True)
class FieldSpec:
    kind: str | type
    optional: bool = False
    attribute: str | None = None
    description: str = ""


SCHEMAS = {
    ModelIR: {"n_control": FieldSpec(int), "n_treatment": FieldSpec(int)},
    PlanIR: {"model": FieldSpec(ModelIR), "stopping": FieldSpec(str)},
    HypothesisIR: {"model": FieldSpec(ModelIR)},
    AnalysisIR: {
        "design": FieldSpec(PlanIR, attribute="plan"),
        "null": FieldSpec(HypothesisIR, attribute="hypothesis"),
        "alpha": FieldSpec(Fraction, description="Exact declared significance level."),
    },
    FamilyIR: {
        "analyses": FieldSpec("list"),
        "alpha": FieldSpec(Fraction),
        "joint_law": FieldSpec(str),
    },
    ObservationIR: {
        "analysis": FieldSpec(AnalysisIR),
        "control_successes": FieldSpec(int),
        "treatment_successes": FieldSpec(int),
    },
    ClaimIR: {"kind": FieldSpec(str), "subject": FieldSpec(object)},
    Evidence: {
        "claim": FieldSpec(ClaimIR),
        "certificate": FieldSpec(CertificateReference),
        "established_properties": FieldSpec("list"),
        "required_assumptions": FieldSpec("list"),
    },
    CertificateReference: {
        name: FieldSpec(str) for name in ("certificate_id", "file", "directory", "sha256")
    },
    CalculationDetails: {
        "p_value": FieldSpec(Fraction),
        "alpha": FieldSpec(Fraction),
        "observed_table_probability": FieldSpec(Fraction),
        "p_value_le_alpha": FieldSpec(bool),
        "test": FieldSpec(str),
        "test_version": FieldSpec(str),
    },
    Diagnostic: {"code": FieldSpec(str), "message": FieldSpec(str), "severity": FieldSpec(str)},
}
COMMON_RESULT = {
    "request_id": FieldSpec(int),
    "claim": FieldSpec(ClaimIR),
    "source_sha256": FieldSpec(str),
    "status": FieldSpec(str, description="Execution status, not a boolean proof of a proposition."),
    "diagnostics": FieldSpec("list"),
}
VERIFICATION_FIELDS = {
    **COMMON_RESULT,
    "evidence": FieldSpec(
        Evidence,
        optional=True,
        description="Checked evidence only after successful verification. "
        "Absent on unmet requirements or backend errors; unevaluated during compilation. "
        "Optional field access propagates absence.",
    ),
}
CALCULATION_FIELDS = {
    **COMMON_RESULT,
    "calculation": FieldSpec(CalculationDetails, optional=True),
    "decision": FieldSpec(str, optional=True),
}
for kind in (VerificationResultIR, VerificationResult):
    SCHEMAS[kind] = VERIFICATION_FIELDS
for kind in (CalculationResultIR, CalculationResult):
    SCHEMAS[kind] = CALCULATION_FIELDS


def fields_for(value: object) -> dict[str, FieldSpec]:
    kind = value.value_type.kind if isinstance(value, FieldIR) else type(value)
    fields = SCHEMAS.get(kind, {})
    if isinstance(value, ClaimIR):
        return {**fields, "subject": FieldSpec(type(value.subject))}
    return fields


def read_field(value: object, name: str, span: Span) -> object:
    """Read only the published schema; never arbitrary Python attributes."""
    spec = fields_for(value).get(name)
    if spec is None:
        fail("unknown_field", f"{type(value).__name__} has no public field {name!r}.", span)
    if isinstance(value, Evidence) and name == "certificate":
        return CertificateReference(**dict(value.certificate))
    if isinstance(value, CalculationResult) and name == "calculation":
        return CalculationDetails(value.calculation) if value.calculation is not None else None
    if isinstance(value, FamilyIR) and name == "analyses":
        return tuple(LocatedValue(analysis, span, label) for label, analysis in value.analyses)
    return getattr(value, spec.attribute or name)


def project(value: object, name: str, span: Span, requests) -> object:
    spec = fields_for(value).get(name)
    if spec is None:
        kind = (
            value.value_type.label
            if isinstance(value, FieldIR)
            else type(value).__name__.removesuffix("IR")
        )
        available = ", ".join(fields_for(value)) or "none"
        fail(
            "unknown_field",
            f"{kind} has no public field {name!r}. Available fields: {available}.",
            span,
        )
    if isinstance(value, (VerificationResultIR, CalculationResultIR)) and name == "claim":
        return requests[value.request_id - 1].claim
    if isinstance(value, (FieldIR, VerificationResultIR, CalculationResultIR)):
        optional = spec.optional or (isinstance(value, FieldIR) and value.value_type.optional)
        return FieldIR(value, name, ValueType(spec.kind, optional), span)
    return read_field(value, name, span)
