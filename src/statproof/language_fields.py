"""The public field schema shared by elaboration, runtime, and editor tooling.

Only explicitly listed fields are exposed. Optional receivers propagate absence;
their fields remain optional, so they cannot be mistaken for checked evidence.
"""

from dataclasses import dataclass
from fractions import Fraction

from statproof.language import (
    AnalysisIR,
    CalculationResultIR,
    CandidatesIR,
    CandidateSpaceIR,
    ClaimIR,
    FamilyIR,
    FeasibilityIR,
    FieldIR,
    HypothesisIR,
    IntervalIR,
    LocatedValue,
    ModelIR,
    ObservationIR,
    OneArmCandidatesIR,
    OneArmModelIR,
    OneSampleAnalysisIR,
    OneSampleObservationIR,
    PlanIR,
    PlannableIR,
    PlanningPointIR,
    PowerTargetIR,
    PriorIR,
    RateIR,
    RatesIR,
    RuleIR,
    SizingIR,
    TwoStageAnalysisIR,
    TwoStageCandidatesIR,
    TwoStageModelIR,
    TwoStageObservationIR,
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
    IntervalDetails,
    OneSampleDetails,
    OneSampleResultDetails,
    PlanningDetails,
    PolicyDetails,
    StageResultDetails,
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
    HypothesisIR: {
        "model": FieldSpec(ModelIR),
        "predicate": FieldSpec(str),
        "value": FieldSpec(Fraction),
        "statement": FieldSpec(str),
    },
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
    RatesIR: {"p_control": FieldSpec(Fraction), "p_treatment": FieldSpec(Fraction)},
    RateIR: {"value": FieldSpec(Fraction)},
    PowerTargetIR: {
        "at": FieldSpec(PlanningPointIR),
        "minimum": FieldSpec(Fraction, description="Required power at the planning point."),
        "maximum_typeI": FieldSpec(Fraction, description="Requested Type I error bound."),
    },
    FeasibilityIR: {"analysis": FieldSpec(PlannableIR), "target": FieldSpec(PowerTargetIR)},
    CandidatesIR: {
        "analysis": FieldSpec(AnalysisIR),
        "min_per_arm": FieldSpec(int),
        "max_per_arm": FieldSpec(int),
        "ratio": FieldSpec(int, description="Treated participants per control."),
    },
    SizingIR: {"candidates": FieldSpec(CandidateSpaceIR), "target": FieldSpec(PowerTargetIR)},
    OneArmModelIR: {"n": FieldSpec(int)},
    OneSampleAnalysisIR: {
        "model": FieldSpec(OneArmModelIR),
        "null_rate": FieldSpec(Fraction),
        "alpha": FieldSpec(Fraction),
    },
    OneSampleObservationIR: {
        "analysis": FieldSpec(OneSampleAnalysisIR),
        "responses": FieldSpec(int),
    },
    OneSampleResultDetails: {
        "n": FieldSpec(int),
        "responses": FieldSpec(int),
        "critical_value": FieldSpec(int),
        "p_value": FieldSpec(Fraction, description="Exact one-sided p-value."),
        "alpha": FieldSpec(Fraction),
        "reject_null": FieldSpec(bool),
        "test": FieldSpec(str),
    },
    IntervalIR: {
        "model": FieldSpec(OneArmModelIR),
        "responses": FieldSpec(int),
        "level": FieldSpec(Fraction),
    },
    IntervalDetails: {
        "n": FieldSpec(int),
        "responses": FieldSpec(int),
        "level": FieldSpec(Fraction),
        "estimate": FieldSpec(Fraction),
        "lower": FieldSpec(Fraction, description="Lower endpoint, rounded down."),
        "upper": FieldSpec(Fraction, description="Upper endpoint, rounded up."),
        "method": FieldSpec(str),
    },
    OneArmCandidatesIR: {
        "analysis": FieldSpec(OneSampleAnalysisIR),
        "min_n": FieldSpec(int),
        "max_n": FieldSpec(int),
    },
    OneSampleDetails: {
        "n": FieldSpec(int, optional=True),
        "critical_value": FieldSpec(
            int, optional=True, description="Smallest response count that rejects."
        ),
        "typeI": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "power": FieldSpec(Fraction, optional=True),
        "power_target_met": FieldSpec(bool),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    TwoStageModelIR: {"n_stage1": FieldSpec(int), "n_stage2": FieldSpec(int)},
    PriorIR: {"a": FieldSpec(int), "b": FieldSpec(int)},
    RuleIR: {"kind": FieldSpec(str)},
    TwoStageAnalysisIR: {
        "design": FieldSpec(TwoStageModelIR),
        "rule": FieldSpec(RuleIR),
        "null_rate": FieldSpec(Fraction),
    },
    PlanningDetails: {
        "n_control": FieldSpec(int, optional=True),
        "n_treatment": FieldSpec(int, optional=True),
        "total_sample_size": FieldSpec(int, optional=True),
        "power": FieldSpec(
            Fraction, optional=True, description="Exact calculated power; not checked evidence."
        ),
        "power_target_met": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, optional=True),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
        "minimum_sample_size_claim": FieldSpec(str, optional=True),
    },
    TwoStageObservationIR: {
        "analysis": FieldSpec(TwoStageAnalysisIR),
        "stage1_responses": FieldSpec(int),
        "stage2_responses": FieldSpec(int, optional=True),
    },
    StageResultDetails: {
        "n_stage1": FieldSpec(int),
        "n_stage2": FieldSpec(int),
        "stage1_responses": FieldSpec(int),
        "stage2_responses": FieldSpec(int, optional=True),
        "continued": FieldSpec(bool),
        "reject_null": FieldSpec(bool),
        "typeI_bound": FieldSpec(Fraction, description="Checked bound on the design's error."),
    },
    TwoStageCandidatesIR: {
        "null_rate": FieldSpec(Fraction),
        "max_total": FieldSpec(int),
        "criterion": FieldSpec(str),
    },
    PolicyDetails: {
        "n_stage1": FieldSpec(int, optional=True),
        "n_stage2": FieldSpec(int, optional=True),
        "continue_above": FieldSpec(int, optional=True),
        "reject_above": FieldSpec(int, optional=True),
        "maximum_sample_size": FieldSpec(int, optional=True),
        "typeI": FieldSpec(
            Fraction, optional=True, description="Exact rejection probability at the null rate."
        ),
        "typeI_target_met": FieldSpec(bool, optional=True),
        "power": FieldSpec(Fraction, optional=True),
        "power_target_met": FieldSpec(bool),
        "expected_sample_size_null": FieldSpec(Fraction, optional=True),
        "expected_sample_size_alternative": FieldSpec(Fraction, optional=True),
        "early_stop_probability_null": FieldSpec(Fraction, optional=True),
        "criterion": FieldSpec(str, optional=True),
        "candidates_evaluated": FieldSpec(int, optional=True),
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


def details_kind(claim: ClaimIR) -> type:
    """The calculation record published for this claim's kind."""
    if isinstance(claim.subject, TwoStageObservationIR):
        return StageResultDetails
    if isinstance(claim.subject, IntervalIR):
        return IntervalDetails
    if isinstance(claim.subject, OneSampleObservationIR):
        return OneSampleResultDetails
    if claim.kind not in ("meets", "sample_size"):
        return CalculationDetails
    subject = claim.subject
    analysis = (
        subject.analysis if isinstance(subject, FeasibilityIR) else subject.candidates.analysis
    )
    if isinstance(analysis, OneSampleAnalysisIR):
        return OneSampleDetails
    if isinstance(analysis, TwoStageAnalysisIR):
        return PolicyDetails
    return PlanningDetails


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
        if value.calculation is None:
            return None
        return details_kind(value.claim)(value.calculation)
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
    if isinstance(value, CalculationResultIR) and name == "calculation":
        kind = details_kind(requests[value.request_id - 1].claim)
        return FieldIR(value, name, ValueType(kind, True), span)
    if isinstance(value, (FieldIR, VerificationResultIR, CalculationResultIR)):
        optional = spec.optional or (isinstance(value, FieldIR) and value.value_type.optional)
        return FieldIR(value, name, ValueType(spec.kind, optional), span)
    return read_field(value, name, span)
