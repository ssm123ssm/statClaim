"""Backend-free compilation of statistical source into a typed execution plan.

Compilation checks syntax, types, and known theorem requirements. A plan is not
a proof, and an unmet requirement does not refute the requested claim.
"""

from dataclasses import dataclass

from statclaim.language import (
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationResultIR,
    CitedAnalysisIR,
    ComposedFamilyIR,
    DifferenceIntervalIR,
    EffectIntervalIR,
    FamilyIR,
    FeasibilityIR,
    IntervalIR,
    ObservationIR,
    OneSampleObservationIR,
    ProgramIR,
    RandomisationAnalysisIR,
    RequestIR,
    TwoStageObservationIR,
    elaborate,
)
from statclaim.language_syntax import Diagnostic, Source, Span


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


def _combination_requirements(program, request, name, family, seen: set[int]) -> list:
    """Open requirements of a combination and of any design with looks inside it."""
    diagnostics = []
    composition = family.lower()
    if composition.rules.splits and not composition.fits:
        diagnostics.append(
            Diagnostic(
                "allocation",
                f"{name}: the {composition.rules.part} levels sum to {composition.allocated}, "
                f"above the overall level {family.alpha}. No bound follows from this "
                "allocation; this does not prove excessive actual error.",
                _origin(program, family, request.span, "alpha"),
                "obligation",
            )
        )
    for member, analysis in family.analyses:
        if isinstance(analysis, ComposedFamilyIR):
            diagnostics += _combination_requirements(program, request, member, analysis, seen)
        elif analysis.plan.stopping != "fixed" and id(analysis.plan) not in seen:
            seen.add(id(analysis.plan))
            diagnostics.append(
                Diagnostic(
                    "sampling_scope",
                    f"{name}: {member} uses data-dependent stopping, which its own "
                    "guarantee does not cover. Declare planned looks with alpha_spending "
                    "instead. This is not evidence of inflated error.",
                    _origin(program, analysis.plan, request.span),
                    "obligation",
                )
            )
    return diagnostics


def requirements(program: ProgramIR, request: RequestIR) -> tuple[Diagnostic, ...]:
    """Inspect supported contracts without numerical evaluation or Lean."""
    subject, name = request.claim.subject, request.claim.name
    diagnostics = []
    if request.claim.kind in ("meets", "sample_size"):
        analysis = (
            subject.analysis if isinstance(subject, FeasibilityIR) else subject.candidates.analysis
        )
        if not isinstance(analysis, (AnalysisIR, CitedAnalysisIR)):
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
        if (
            isinstance(analysis, AnalysisIR)
            and request.operation == "verify"
            and analysis.alpha > subject.target.maximum_typeI
        ):
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
    if isinstance(
        subject,
        (
            OneSampleObservationIR,
            TwoStageObservationIR,
            IntervalIR,
            DifferenceIntervalIR,
            EffectIntervalIR,
        ),
    ):
        return ()
    if isinstance(subject, AssociationResultIR):
        subject = subject.analysis
    if isinstance(subject, CitedAnalysisIR):
        if request.operation != "verify" or subject.plan.stopping == "fixed":
            return ()
        return (
            Diagnostic(
                "sampling_scope",
                f"{name}: the cited guarantee assumes arm sizes fixed in advance and a single "
                "analysis. Data-dependent stopping is outside it and needs a design with its "
                "own guarantee. This is not evidence of inflated error.",
                _origin(program, subject.plan, request.span),
                "obligation",
            ),
        )
    if isinstance(subject, AssociationAnalysisIR):
        if request.operation != "verify" or subject.plan.stopping == "fixed":
            return ()
        return (
            Diagnostic(
                "sampling_scope",
                f"{name}: Fisher's test of association assumes the study's size was fixed in "
                "advance. Data-dependent stopping needs a design with its own guarantee. This "
                "is not evidence of inflated error.",
                _origin(program, subject.plan, request.span),
                "obligation",
            ),
        )
    if isinstance(subject, RandomisationAnalysisIR):
        if request.operation != "verify" or subject.plan.stopping == "fixed":
            return ()
        return (
            Diagnostic(
                "sampling_scope",
                f"{name}: the randomisation test counts the splits of a fixed set of units. "
                "Data-dependent stopping changes which units are analysed and needs a design "
                "with its own guarantee. This is not evidence of inflated error.",
                _origin(program, subject.plan, request.span),
                "obligation",
            ),
        )
    if isinstance(subject, ComposedFamilyIR):
        return tuple(_combination_requirements(program, request, name, subject, set()))
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
    from statclaim.derivations import derive_program

    return Compilation(program, tuple(diagnostics), obligations, derive_program(program))
