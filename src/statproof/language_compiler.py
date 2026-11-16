"""Backend-free compilation of statistical source into a typed execution plan.

Compilation checks syntax, types, and known theorem requirements. A plan is not
a proof, and an unmet requirement does not refute the requested claim.
"""

from dataclasses import dataclass

from statproof.language import (
    AnalysisIR,
    FamilyIR,
    FeasibilityIR,
    IntervalIR,
    ObservationIR,
    OneSampleObservationIR,
    ProgramIR,
    RequestIR,
    TwoStageObservationIR,
    elaborate,
)
from statproof.language_syntax import Diagnostic, Source, Span


@dataclass(frozen=True)
class Compilation:
    program: ProgramIR
    diagnostics: tuple[Diagnostic, ...]
    request_diagnostics: tuple[tuple[Diagnostic, ...], ...]
    # Why each passing contract passed. Kept with the plan; never shown unasked.
    derivations: tuple = ()

    @property
    def status(self) -> str:
        if any(d.severity == "error" for d in self.diagnostics):
            return "invalid"
        return "unresolved_obligation" if self.diagnostics else "elaborated"


def _origin(program: ProgramIR, value: object, fallback: Span, field: str | None = None) -> Span:
    # Follow object identity rather than a claim's display name: aliases retain
    # the original constructor's argument location, without equating endpoints.
    bindings = [b for b in program.bindings if b.value is value]
    for binding in bindings:
        fields = dict(binding.argument_sources)
        if field in fields:
            return fields[field]
    return bindings[0].span if bindings else fallback


def requirements(program: ProgramIR, request: RequestIR) -> tuple[Diagnostic, ...]:
    """Inspect supported contracts without numerical evaluation or Lean."""
    subject, name = request.claim.subject, request.claim.name
    diagnostics = []
    if request.claim.kind in ("meets", "sample_size"):
        analysis = (
            subject.analysis if isinstance(subject, FeasibilityIR) else subject.candidates.analysis
        )
        if not isinstance(analysis, AnalysisIR):
            return ()
        if analysis.plan.stopping != "fixed":
            diagnostics.append(
                Diagnostic(
                    "sampling_scope",
                    f"{name}: planning for this analysis uses the fixed-sample law. "
                    "Data-dependent stopping needs a complete policy with its own "
                    "operating characteristics. This is not evidence of inflated error.",
                    _origin(program, analysis.plan, request.span),
                    "obligation",
                )
            )
        if request.operation == "verify" and analysis.alpha > subject.target.maximum_typeI:
            diagnostics.append(
                Diagnostic(
                    "typeI_target_not_established",
                    f"{name}: alpha {analysis.alpha} exceeds the requested Type I bound "
                    f"{subject.target.maximum_typeI}. The Fisher theorem bounds error by alpha "
                    "only; this is not evidence that the actual error exceeds the request.",
                    _origin(program, subject.target, request.span, "maximum_typeI"),
                    "obligation",
                )
            )
        return tuple(diagnostics)
    if isinstance(subject, (OneSampleObservationIR, TwoStageObservationIR, IntervalIR)):
        return ()
    if isinstance(subject, FamilyIR):
        family = subject.lower()
        if family.allocated_alpha > family.alpha:
            diagnostics.append(
                Diagnostic(
                    "allocation",
                    f"{name}: allocated alpha {family.allocated_alpha} "
                    f"exceeds the requested family bound {family.alpha}. No Bonferroni certificate "
                    "can be supplied from this allocation; "
                    "this does not prove excessive actual error.",
                    _origin(program, subject, request.span, "alpha"),
                    "obligation",
                )
            )
        analyses = [analysis for _, analysis in subject.analyses]
    else:
        analyses = [subject.analysis if isinstance(subject, ObservationIR) else subject]
    if request.operation == "verify":
        seen_plans: set[int] = set()
        for analysis in analyses:
            assert isinstance(analysis, AnalysisIR)
            if analysis.plan.stopping != "fixed" and id(analysis.plan) not in seen_plans:
                seen_plans.add(id(analysis.plan))
                diagnostics.append(
                    Diagnostic(
                        "sampling_scope",
                        f"{name}: data-dependent stopping needs a justified sampling law before "
                        "the fixed-sample guarantee can be used. "
                        "This is not evidence of inflated error.",
                        _origin(program, analysis.plan, request.span),
                        "obligation",
                    )
                )
    return tuple(diagnostics)


def compile_source(source: Source) -> Compilation:
    """Build a plan only; never execute verify/calculate or write artifacts."""
    program, errors = elaborate(source)
    obligations = tuple(
        requirements(program, request) if not errors else () for request in program.requests
    )
    diagnostics = [*errors, *(d for group in obligations for d in group)]
    diagnostics.sort(key=lambda d: (d.span.line, d.span.column))
    from statproof.derivations import derive_program

    return Compilation(program, tuple(diagnostics), obligations, derive_program(program))
