"""Immutable execution values, separate from typed slots in the compiler plan."""

from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction
from types import MappingProxyType

from statclaim.language import (
    CalculationResultIR,
    ClaimIR,
    FieldIR,
    LocatedValue,
    ValueType,
    VerificationResultIR,
    normalize,
)
from statclaim.language_syntax import Diagnostic
from statclaim.methods.core import GRADES, Guarantee


def freeze(value: object) -> object:
    if isinstance(value, Mapping):
        return MappingProxyType({key: freeze(item) for key, item in value.items()})
    if isinstance(value, (list, tuple)):
        return tuple(freeze(item) for item in value)
    return value


def thaw(value: object) -> object:
    if isinstance(value, Mapping):
        return {key: thaw(item) for key, item in value.items()}
    if isinstance(value, tuple):
        return [thaw(item) for item in value]
    return value


@dataclass(frozen=True)
class CertificateReference:
    certificate_id: str
    directory: str
    file: str
    sha256: str

    def to_dict(self):
        return {
            name: getattr(self, name) for name in ("certificate_id", "directory", "file", "sha256")
        }


@dataclass(frozen=True)
class CalculationDetails:
    record: Mapping

    def __post_init__(self):
        object.__setattr__(self, "record", freeze(self.record))

    @property
    def p_value(self):
        return Fraction(self.record["p_value"]["fraction"])

    @property
    def alpha(self):
        return Fraction(self.record["alpha"]["fraction"])

    @property
    def observed_table_probability(self):
        return Fraction(self.record["observed_table_probability"]["fraction"])

    @property
    def p_value_le_alpha(self):
        return self.record["p_value_le_alpha"]

    @property
    def test(self):
        return self.record["test"]

    @property
    def test_version(self):
        return self.record["test_version"]

    def to_dict(self):
        return thaw(self.record)


@dataclass(frozen=True)
class PlanningDetails:
    """Calculated planning components. Fractions are exact; absent values are None."""

    record: Mapping

    def __post_init__(self):
        object.__setattr__(self, "record", freeze(self.record))

    def __getattr__(self, name: str):
        value = self.record.get(name)
        if isinstance(value, Mapping) and "fraction" in value:
            return Fraction(value["fraction"])
        return value

    def to_dict(self):
        return thaw(self.record)


class SimulationDetails(PlanningDetails):
    """Power and Type I error estimated by simulation, with 95% intervals. Not evidence."""


class OneSampleDetails(PlanningDetails):
    """Calculated critical value, error and power of a one-sample test."""


class OneSampleResultDetails(PlanningDetails):
    """Calculated p-value and decision for an observed one-sample count."""


class IntervalDetails(PlanningDetails):
    """Calculated exact confidence interval for a response rate."""


class StageResultDetails(PlanningDetails):
    """Calculated decision for observed two-stage counts."""


class DifferenceDetails(PlanningDetails):
    """Calculated interval for a difference of two proportions."""


class AssociationResultDetails(PlanningDetails):
    """Calculated p-value and decision of Fisher's test for an observed 2x2 table."""


class MatchedResultDetails(PlanningDetails):
    """Calculated p-value and decision of McNemar's test for observed matched pairs."""


class RateResultDetails(PlanningDetails):
    """Calculated p-value and decision of the exact rate test for observed events."""


class EffectIntervalDetails(PlanningDetails):
    """Calculated interval for an odds, risk or prevalence ratio or difference."""


class MarginDetails(PlanningDetails):
    """Calculated critical value, power and decision of an exact difference test."""


class PolicyDetails(PlanningDetails):
    """Calculated operating characteristics of a complete two-stage policy."""


class ApproximatePowerDetails(PlanningDetails):
    """Approximate power of a cited test from a normal formula. Never a bound."""


class PrecisionDetails(PlanningDetails):
    """The margin of error of a planned interval, and its assurance. A calculation."""


class AssociationPowerDetails(PlanningDetails):
    """Calculated exact power of Fisher's test of association, with the group sizes."""


class MatchedPowerDetails(PlanningDetails):
    """Calculated exact power of McNemar's test for a number of pairs."""


class RatePowerDetails(PlanningDetails):
    """Calculated exact power of the rate test given a number of events."""


@dataclass(frozen=True)
class PendingField:
    request_id: int
    path: tuple[str, ...]
    value_type: ValueType

    def to_dict(self):
        return {
            "type": "DeferredValue",
            "request_id": self.request_id,
            "field": ".".join(self.path),
            "value_type": self.value_type.label,
            "status": "not_executed",
        }


@dataclass(frozen=True)
class Evidence:
    """A checked claim and certificate reference, with explicit assumptions.

    Source binding is application provenance; certificates bind mathematical
    inputs and generated Lean statements, not the original source spelling.
    """

    claim: ClaimIR
    certificate: Mapping | None
    established_properties: tuple[str, ...]
    required_assumptions: tuple[str, ...]
    grade: str
    references: tuple[str, ...] = ()
    # Set for cited evidence: the method with its version, and its assumptions by id.
    method: Mapping | None = None
    assumptions: tuple[Mapping, ...] = ()

    def __post_init__(self):
        if self.grade not in GRADES:
            raise ValueError(f"Unknown evidence grade {self.grade!r}.")
        if (self.grade in ("proved", "conditional")) != (self.certificate is not None):
            raise ValueError("Exactly the evidence checked by Lean carries a certificate.")
        object.__setattr__(self, "certificate", freeze(self.certificate))
        object.__setattr__(self, "method", freeze(self.method))
        object.__setattr__(self, "assumptions", freeze(self.assumptions))

    @property
    def sources(self) -> tuple[str, ...]:
        """Where the guarantee's statement comes from."""
        return GRADES[self.grade].sources

    @property
    def machine_checked(self) -> str:
        """How far a machine checked it: the guarantee, the composition or the contract."""
        return GRADES[self.grade].machine_checked

    def to_dict(self) -> dict:
        return {
            "type": "Evidence",
            "grade": self.grade,
            "sources": list(self.sources),
            "machine_checked": self.machine_checked,
            "scope": self.claim.scope,
            "guarantee": self.claim.guarantee.to_dict() if self.claim.guarantee else None,
            "method": thaw(self.method),
            "assumptions": thaw(self.assumptions),
            "claim": normalize(self.claim),
            "certificate": thaw(self.certificate),
            "established_properties": list(self.established_properties),
            "required_assumptions": list(self.required_assumptions),
            "references": list(self.references),
        }


# The one evidence grade each successful status may carry. A status never
# overstates its evidence: only a full Lean proof is called verified.
STATUS_GRADES = {
    "verified": "proved",
    "conditional": "conditional",
    "cited": "cited",
    "declared": "declared",
}


@dataclass(frozen=True)
class VerificationResult:
    request_id: int
    claim: ClaimIR
    source_sha256: str
    status: str
    evidence: Evidence | None = None
    diagnostics: tuple[Diagnostic, ...] = ()

    def __post_init__(self):
        if (self.status in STATUS_GRADES) != (self.evidence is not None):
            raise ValueError("Only a successful verification result carries checked evidence.")
        if self.evidence is not None and STATUS_GRADES[self.status] != self.evidence.grade:
            raise ValueError("A verified result needs evidence checked by Lean.")
        if self.evidence is not None and self.evidence.claim != self.claim:
            raise ValueError("Evidence must establish the verification result's claim.")

    def to_dict(self) -> dict:
        return {
            "type": "VerificationResult",
            "request_id": self.request_id,
            "claim": normalize(self.claim),
            "source_sha256": self.source_sha256,
            "status": self.status,
            "evidence": self.evidence.to_dict() if self.evidence else None,
            "diagnostics": [d.to_dict() for d in self.diagnostics],
        }


@dataclass(frozen=True)
class CalculationResult:
    request_id: int
    claim: ClaimIR
    source_sha256: str
    status: str
    calculation: Mapping | None = None
    decision: str | None = None
    diagnostics: tuple[Diagnostic, ...] = ()
    # calculate or simulate: which request made it, and so what its calculation holds.
    operation: str = "calculate"

    def __post_init__(self):
        object.__setattr__(self, "calculation", freeze(self.calculation))

    def to_dict(self) -> dict:
        return {
            "type": "CalculationResult",
            "request_id": self.request_id,
            "claim": normalize(self.claim),
            "source_sha256": self.source_sha256,
            "status": self.status,
            "calculation": thaw(self.calculation),
            "decision": self.decision,
            "diagnostics": [d.to_dict() for d in self.diagnostics],
            **({"operation": self.operation} if self.operation != "calculate" else {}),
        }


type ExecutionResult = VerificationResult | CalculationResult


def resolve(value: object, results: Mapping[int, ExecutionResult]) -> object:
    """Resolve aliases and nested lists without ever executing an operation."""
    if isinstance(value, (VerificationResultIR, CalculationResultIR)):
        return results[value.request_id]
    if isinstance(value, FieldIR):
        from statclaim.language_fields import read_field

        subject = resolve(value.subject, results)
        if isinstance(subject, PendingField):
            return PendingField(subject.request_id, (*subject.path, value.name), value.value_type)
        if (
            isinstance(subject, (VerificationResult, CalculationResult))
            and subject.status == "not_executed"
        ):
            return PendingField(subject.request_id, (value.name,), value.value_type)
        if subject is None and value.value_type.optional:
            return None
        return read_field(subject, value.name, value.span)
    if isinstance(value, tuple):
        return tuple(
            resolve(item.value if isinstance(item, LocatedValue) else item, results)
            for item in value
        )
    return value


def serialize(value: object) -> object:
    if isinstance(
        value,
        (
            VerificationResult,
            CalculationResult,
            Evidence,
            CertificateReference,
            CalculationDetails,
            PlanningDetails,
            PendingField,
            Diagnostic,
            Guarantee,
        ),
    ):
        return value.to_dict()
    if isinstance(value, tuple):
        return [serialize(item.value if isinstance(item, LocatedValue) else item) for item in value]
    return normalize(value)
