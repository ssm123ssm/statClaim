"""Immutable execution values, separate from typed slots in the compiler plan."""

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType

from statproof.language import (
    CalculationResultIR,
    ClaimIR,
    LocatedValue,
    VerificationResultIR,
    normalize,
)
from statproof.language_syntax import Diagnostic


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
class Evidence:
    """A checked claim and certificate reference, with explicit assumptions.

    Source binding is application provenance; certificates bind mathematical
    inputs and generated Lean statements, not the original source spelling.
    """

    claim: ClaimIR
    certificate: Mapping
    established_properties: tuple[str, ...]
    required_assumptions: tuple[str, ...]

    def __post_init__(self):
        object.__setattr__(self, "certificate", freeze(self.certificate))

    def to_dict(self) -> dict:
        return {
            "type": "Evidence",
            "claim": normalize(self.claim),
            "certificate": thaw(self.certificate),
            "established_properties": list(self.established_properties),
            "required_assumptions": list(self.required_assumptions),
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
        if (self.status == "verified") != (self.evidence is not None):
            raise ValueError("Only a successful verification result carries checked evidence.")
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
        }


type ExecutionResult = VerificationResult | CalculationResult


def resolve(value: object, results: Mapping[int, ExecutionResult]) -> object:
    """Resolve aliases and nested lists without ever executing an operation."""
    if isinstance(value, (VerificationResultIR, CalculationResultIR)):
        return results[value.request_id]
    if isinstance(value, tuple):
        return tuple(resolve(item.value, results) for item in value)
    return value


def serialize(value: object) -> object:
    if isinstance(value, (VerificationResult, CalculationResult)):
        return value.to_dict()
    if isinstance(value, tuple):
        return [serialize(item.value if isinstance(item, LocatedValue) else item) for item in value]
    return normalize(value)
