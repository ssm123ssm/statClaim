"""Typed statistical objects and module-driven elaboration of .stat files.

No Python or Lean source in a user file is executed. Module builders lower the
supported objects to the same validated requests as the TOML and Lean routes.
"""

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from typing import Literal as Choice

from statproof.design import Design
from statproof.family import MAX_ENDPOINTS, Endpoint, FisherFamily
from statproof.fisher import validate_alpha
from statproof.language_contracts import FISHER_CONTRACT, HypothesisContract
from statproof.language_syntax import (
    Call,
    Diagnostic,
    Expression,
    FieldAccess,
    LanguageError,
    ListExpr,
    Literal,
    Reference,
    Source,
    Span,
    Statement,
    parse,
)
from statproof.planning import (
    MAX_ONE_ARM,
    MAX_PER_ARM,
    MAX_STAGE,
    OneSamplePlan,
    PowerPlan,
    TwoStagePlan,
    TwoStageRule,
)

LANGUAGE_VERSION = "0.6.0"


class PlannableIR:
    """An analysis that planning targets can be assessed against."""


class CandidateSpaceIR:
    """A finite set of candidate designs for a sample-size search."""


class PlanningPointIR:
    """A parameter point used for planning; never a replacement for the null."""


@dataclass(frozen=True)
class ModelIR:
    n_control: int
    n_treatment: int


@dataclass(frozen=True)
class PlanIR:
    model: ModelIR
    stopping: Choice["fixed", "data_dependent"]


@dataclass(frozen=True)
class HypothesisIR:
    model: ModelIR
    predicate: Choice[
        "equal_proportions", "proportion_difference", "proportion_difference_at_most"
    ] = "equal_proportions"
    value: Fraction = Fraction(0)

    def __post_init__(self):
        if self.predicate not in (
            "equal_proportions",
            "proportion_difference",
            "proportion_difference_at_most",
        ):
            raise ValueError("Unsupported hypothesis predicate.")
        if not isinstance(self.value, Fraction) or not -1 <= self.value <= 1:
            raise ValueError("A hypothesis value must be an exact Fraction in [-1, 1].")
        if self.predicate == "equal_proportions" and self.value != 0:
            raise ValueError("Equal proportions require zero difference.")

    @property
    def statement(self) -> str:
        if self.predicate == "equal_proportions":
            return "p_treatment = p_control"
        operator = "=" if self.predicate == "proportion_difference" else "<="
        return f"p_treatment - p_control {operator} {self.value}"


@dataclass(frozen=True)
class AnalysisIR(PlannableIR):
    plan: PlanIR
    hypothesis: HypothesisIR
    alpha: Fraction

    def __post_init__(self):
        if not FISHER_CONTRACT.accepts(self.plan, self.hypothesis):
            raise ValueError("A Fisher analysis requires its design's equal-proportions null.")

    def lower(self) -> Design:
        return Design(
            self.plan.model.n_control, self.plan.model.n_treatment, self.plan.stopping, self.alpha
        )


@dataclass(frozen=True)
class FamilyIR:
    analyses: tuple[tuple[str, AnalysisIR], ...]
    alpha: Fraction
    joint_law: str

    def lower(self) -> FisherFamily:
        return FisherFamily(
            self.alpha, tuple(Endpoint(name, analysis.lower()) for name, analysis in self.analyses)
        )


@dataclass(frozen=True)
class ObservationIR:
    analysis: AnalysisIR
    control_successes: int
    treatment_successes: int


@dataclass(frozen=True)
class RatesIR(PlanningPointIR):
    p_control: Fraction
    p_treatment: Fraction


@dataclass(frozen=True)
class RateIR(PlanningPointIR):
    value: Fraction


@dataclass(frozen=True)
class PowerTargetIR:
    at: PlanningPointIR
    minimum: Fraction
    maximum_typeI: Fraction


@dataclass(frozen=True)
class TwoStageModelIR:
    n_stage1: int
    n_stage2: int


@dataclass(frozen=True)
class PriorIR:
    a: int
    b: int


@dataclass(frozen=True)
class RuleIR:
    rule: TwoStageRule

    @property
    def kind(self) -> str:
        return self.rule.kind


@dataclass(frozen=True)
class TwoStageAnalysisIR(PlannableIR):
    design: TwoStageModelIR
    rule: RuleIR
    null_rate: Fraction


@dataclass(frozen=True)
class OneArmModelIR:
    n: int


@dataclass(frozen=True)
class OneSampleAnalysisIR(PlannableIR):
    """One-sided exact binomial test of a response rate at or below null_rate."""

    model: OneArmModelIR
    null_rate: Fraction
    alpha: Fraction

    def plan(self, target: "PowerTargetIR", n: int | None = None) -> OneSamplePlan:
        return OneSamplePlan(
            self.model.n if n is None else n,
            self.null_rate,
            self.alpha,
            target.at.value,
            target.minimum,
            target.maximum_typeI,
        )


@dataclass(frozen=True)
class FeasibilityIR:
    """One analysis assessed against one target."""

    analysis: PlannableIR
    target: PowerTargetIR

    def lower(self) -> PowerPlan | TwoStagePlan | OneSamplePlan:
        target = self.target
        if isinstance(self.analysis, OneSampleAnalysisIR):
            return self.analysis.plan(target)
        if isinstance(self.analysis, TwoStageAnalysisIR):
            analysis = self.analysis
            return TwoStagePlan(
                analysis.design.n_stage1,
                analysis.design.n_stage2,
                analysis.rule.rule,
                analysis.null_rate,
                target.at.value,
                target.minimum,
                target.maximum_typeI,
            )
        return PowerPlan(
            self.analysis.lower(),
            target.at.p_control,
            target.at.p_treatment,
            target.minimum,
            target.maximum_typeI,
        )


@dataclass(frozen=True)
class CandidatesIR(CandidateSpaceIR):
    """Equal-arm designs sharing the analysis's test, null form, alpha and sampling."""

    analysis: AnalysisIR
    min_per_arm: int
    max_per_arm: int


@dataclass(frozen=True)
class OneArmCandidatesIR(CandidateSpaceIR):
    """Sample sizes for a one-sample test, keeping its null rate and alpha."""

    analysis: OneSampleAnalysisIR
    min_n: int
    max_n: int


@dataclass(frozen=True)
class SizingIR:
    candidates: "CandidatesIR | OneArmCandidatesIR"
    target: PowerTargetIR
    minimal: bool = False


@dataclass(frozen=True)
class ClaimIR:
    kind: Choice["typeI", "familywise", "result", "meets", "sample_size"]
    subject: AnalysisIR | FamilyIR | ObservationIR | FeasibilityIR | SizingIR
    name: str


@dataclass(frozen=True)
class LocatedValue:
    value: object
    span: Span
    name: str | None = None
    definition_span: Span | None = None


@dataclass(frozen=True)
class BindingIR:
    name: str
    value: object
    span: Span
    dependencies: tuple[str, ...]
    argument_sources: tuple[tuple[str, Span], ...]


@dataclass(frozen=True)
class RequestIR:
    operation: Choice["verify", "calculate"]
    claim: ClaimIR
    span: Span


@dataclass(frozen=True)
class VerificationResultIR:
    """A typed result slot, never evidence that verification has executed."""

    request_id: int


@dataclass(frozen=True)
class CalculationResultIR:
    request_id: int


@dataclass(frozen=True)
class ValueType:
    kind: str | type
    optional: bool = False

    @property
    def label(self) -> str:
        name = (
            self.kind
            if isinstance(self.kind, str)
            else {
                str: "string",
                int: "integer",
                Fraction: "exact number",
                bool: "boolean",
                PlanIR: "StudyDesign",
                PlannableIR: "Analysis",
                CandidateSpaceIR: "Candidates",
                PlanningPointIR: "PlanningPoint",
                TwoStageAnalysisIR: "TwoStageAnalysis",
                OneSampleAnalysisIR: "OneSampleAnalysis",
                OneArmModelIR: "OneArmModel",
                OneArmCandidatesIR: "OneArmCandidates",
            }.get(self.kind, self.kind.__name__.removesuffix("IR"))
        )
        return f"Option[{name}]" if self.optional else name


@dataclass(frozen=True)
class FieldIR:
    subject: object
    name: str
    value_type: ValueType
    span: Span


def is_deferred(value: object) -> bool:
    if isinstance(value, FieldIR):
        return True
    return isinstance(value, tuple) and any(
        is_deferred(item.value if isinstance(item, LocatedValue) else item) for item in value
    )


@dataclass(frozen=True)
class ProgramIR:
    modules: tuple[str, ...]
    bindings: tuple[BindingIR, ...]
    requests: tuple[RequestIR, ...]

    def to_dict(self) -> dict:
        return {
            "language_version": LANGUAGE_VERSION,
            "modules": list(self.modules),
            "bindings": [
                {
                    "name": b.name,
                    "type": b.value.value_type.label
                    if isinstance(b.value, FieldIR)
                    else type(b.value).__name__,
                    "value": normalize(b.value),
                    "source": b.span.to_dict(),
                    "dependencies": list(b.dependencies),
                    "argument_sources": {name: span.to_dict() for name, span in b.argument_sources},
                }
                for b in self.bindings
            ],
            "requests": [
                {
                    "request_id": index,
                    "operation": r.operation,
                    "claim": normalize(r.claim),
                    "source": r.span.to_dict(),
                }
                for index, r in enumerate(self.requests, 1)
            ],
        }


def normalize(value: object) -> object:
    """Serialize semantic objects, without implying a proof or executing a backend."""
    match value:
        case Fraction():
            return str(value)
        case ModelIR(n_control=nc, n_treatment=nt):
            return {"module": "two_arm_binomial", "n_control": nc, "n_treatment": nt}
        case PlanIR(model=model, stopping=stopping):
            return {"model": normalize(model), "stopping": stopping}
        case HypothesisIR(model=model, predicate=predicate, value=bound):
            result = {"predicate": predicate, "model": normalize(model)}
            if predicate != "equal_proportions":
                result["value"] = str(bound)
            return result
        case AnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "fisher",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
        case FamilyIR(analyses=analyses, alpha=alpha, joint_law=law):
            return {
                "method": "bonferroni",
                "alpha": str(alpha),
                "joint_law": law,
                "analyses": [
                    {"name": name, "analysis": normalize(analysis)} for name, analysis in analyses
                ],
            }
        case ObservationIR(
            analysis=analysis, control_successes=control, treatment_successes=treatment
        ):
            return {
                "analysis": normalize(analysis),
                "control_successes": control,
                "treatment_successes": treatment,
            }
        case RatesIR(p_control=control, p_treatment=treatment):
            return {"p_control": str(control), "p_treatment": str(treatment)}
        case RateIR(value=rate):
            return {"response_rate": str(rate)}
        case PowerTargetIR(at=point, minimum=minimum, maximum_typeI=maximum):
            return {
                "at": normalize(point),
                "minimum_power": str(minimum),
                "maximum_typeI": str(maximum),
            }
        case TwoStageModelIR(n_stage1=first, n_stage2=second):
            return {"module": "two_stage_binomial", "n_stage1": first, "n_stage2": second}
        case PriorIR(a=a, b=b):
            return {"distribution": "beta", "a": a, "b": b}
        case RuleIR(rule=rule):
            return rule.to_dict()
        case TwoStageAnalysisIR(design=design, rule=rule, null_rate=rate):
            return {
                "test": "two_stage",
                "design": normalize(design),
                "rule": normalize(rule),
                "null_rate": str(rate),
            }
        case OneArmModelIR(n=n):
            return {"module": "one_arm_binomial", "n": n}
        case OneSampleAnalysisIR(model=model, null_rate=rate, alpha=alpha):
            return {
                "test": "binomial_exact_one_sided",
                "model": normalize(model),
                "null_rate": str(rate),
                "alpha": str(alpha),
            }
        case OneArmCandidatesIR(analysis=analysis, min_n=low, max_n=high):
            return {"analysis": normalize(analysis), "min_n": low, "max_n": high}
        case FeasibilityIR(analysis=analysis, target=target):
            return {"analysis": normalize(analysis), "target": normalize(target)}
        case CandidatesIR(analysis=analysis, min_per_arm=low, max_per_arm=high):
            return {
                "analysis": normalize(analysis),
                "allocation": "equal_arms",
                "min_per_arm": low,
                "max_per_arm": high,
            }
        case SizingIR(candidates=candidates, target=target, minimal=minimal):
            return {
                "candidates": normalize(candidates),
                "target": normalize(target),
                "claim": "smallest_in_range" if minimal else "sufficient",
            }
        case ClaimIR(kind=kind, subject=subject, name=name):
            return {"kind": kind, "subject_name": name, "subject": normalize(subject)}
        case VerificationResultIR(request_id=index) | CalculationResultIR(request_id=index):
            return {"request_id": index}
        case FieldIR(subject=subject, name=name, value_type=value_type):
            return {"field": name, "subject": normalize(subject), "value_type": value_type.label}
        case tuple():
            return [normalize(item.value) for item in value]
        case _:
            return value


@dataclass(frozen=True)
class Parameter:
    name: str
    kind: str | type


@dataclass(frozen=True)
class Constructor:
    name: str
    parameters: tuple[Parameter, ...]
    result: str
    build: Callable[[dict[str, LocatedValue], Span], object]
    hypothesis_contract: HypothesisContract | None = None
    documentation: str = ""

    @property
    def signature(self) -> str:
        return f"{self.name}({', '.join(p.name for p in self.parameters)}) -> {self.result}"


@dataclass(frozen=True)
class Module:
    name: str
    constructors: tuple[Constructor, ...]


def fail(code: str, message: str, span: Span) -> None:
    raise LanguageError(Diagnostic(code, message, span))


def _model(arguments: dict[str, LocatedValue], span: Span) -> ModelIR:
    for name, argument in arguments.items():
        if argument.value <= 0:
            fail("domain", f"{name} must be a positive integer.", argument.span)
    return ModelIR(arguments["n_control"].value, arguments["n_treatment"].value)


def _fisher(arguments: dict[str, LocatedValue], span: Span) -> AnalysisIR:
    plan, hypothesis = arguments["design"].value, arguments["null"].value
    return AnalysisIR(plan, hypothesis, arguments["alpha"].value)


def _difference(predicate: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> HypothesisIR:
        bound = arguments["value"]
        if not -1 <= bound.value <= 1:
            fail("domain", "A proportion-difference value must lie in [-1, 1].", bound.span)
        # This alias is backed by proportionDifference_zero_iff in the Lean model.
        canonical = (
            "equal_proportions"
            if predicate == "proportion_difference" and bound.value == 0
            else predicate
        )
        return HypothesisIR(arguments["model"].value, canonical, bound.value)

    return build


def _family(arguments: dict[str, LocatedValue], span: Span) -> FamilyIR:
    items = arguments["analyses"].value
    if not 2 <= len(items) <= MAX_ENDPOINTS:
        fail(
            "family_size",
            f"A Bonferroni family needs between 2 and {MAX_ENDPOINTS} analyses.",
            arguments["analyses"].span,
        )
    analyses = []
    for item in items:
        if not isinstance(item.value, AnalysisIR) or item.name is None:
            fail("type", "Each family member must be a named Fisher analysis.", item.span)
        analyses.append((item.name, item.value))
    if len({name for name, _ in analyses}) != len(analyses):
        fail(
            "duplicate_analysis",
            "Family members must have distinct names.",
            arguments["analyses"].span,
        )
    law = arguments["joint_law"]
    if law.value != "binomial_marginals":
        fail(
            "sampling_contract",
            'The supported joint contract is "binomial_marginals"; '
            "dependence between outcomes is unrestricted.",
            law.span,
        )
    return FamilyIR(tuple(analyses), arguments["alpha"].value, law.value)


def _observe(arguments: dict[str, LocatedValue], span: Span) -> ObservationIR:
    analysis = arguments["analysis"].value
    for name, size in (
        ("control_successes", analysis.plan.model.n_control),
        ("treatment_successes", analysis.plan.model.n_treatment),
    ):
        argument = arguments[name]
        if not 0 <= argument.value <= size:
            fail("domain", f"{name} must be between 0 and {size} for this analysis.", argument.span)
    return ObservationIR(
        analysis, arguments["control_successes"].value, arguments["treatment_successes"].value
    )


def _claim(kind: str, argument: str) -> Callable:
    return lambda args, span: ClaimIR(
        kind, args[argument].value, args[argument].name or "<expression>"
    )


def _constructor(
    name: str,
    parameters: tuple[tuple[str, str | type], ...],
    result: str,
    build: Callable,
    *,
    hypothesis_contract: HypothesisContract | None = None,
    documentation: str = "",
) -> Constructor:
    return Constructor(
        name,
        tuple(Parameter(*p) for p in parameters),
        result,
        build,
        hypothesis_contract,
        documentation,
    )


def _calculation(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    claim = arguments["claim"]
    if claim.value.kind not in ("result", "meets", "sample_size"):
        fail(
            "type",
            "Only result(observation) and planning claims are numerical calculations. "
            "Use verify(claim) for design guarantees.",
            claim.span,
        )
    return claim.value


def _probability(argument: LocatedValue, name: str, *, positive: bool = False) -> Fraction:
    low_ok = argument.value > 0 if positive else argument.value >= 0
    if not (low_ok and argument.value <= 1):
        bounds = "(0, 1]" if positive else "[0, 1]"
        fail("domain", f"{name} must lie in {bounds}.", argument.span)
    return argument.value


def _rates(arguments: dict[str, LocatedValue], span: Span) -> RatesIR:
    return RatesIR(
        _probability(arguments["p_control"], "p_control"),
        _probability(arguments["p_treatment"], "p_treatment"),
    )


def _power_target(arguments: dict[str, LocatedValue], span: Span) -> PowerTargetIR:
    return PowerTargetIR(
        arguments["at"].value,
        _probability(arguments["minimum"], "minimum", positive=True),
        arguments["maximum_typeI"].value,
    )


def _check_point(analysis: PlannableIR, target: LocatedValue) -> None:
    """The planning point must belong to the analysis's parameter space, outside its null."""
    point = target.value.at
    if isinstance(analysis, (TwoStageAnalysisIR, OneSampleAnalysisIR)):
        if not isinstance(point, RateIR):
            fail(
                "planning_point",
                "A single-arm analysis has one response rate. "
                "Declare the target at response_rate(value=...).",
                target.span,
            )
        if isinstance(analysis, TwoStageAnalysisIR) and analysis.rule.kind == "posterior":
            null = f"response rate = {analysis.null_rate}"
            outside = point.value != analysis.null_rate
        else:
            null = f"response rate <= {analysis.null_rate}"
            outside = point.value > analysis.null_rate
    else:
        if not isinstance(point, RatesIR):
            fail(
                "planning_point",
                "A two-arm analysis needs both rates. "
                "Declare the target at binomial_rates(p_control=..., p_treatment=...).",
                target.span,
            )
        null, outside = "p_treatment = p_control", point.p_control != point.p_treatment
    if not outside:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({null}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _meets(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis = arguments["analysis"]
    _check_point(analysis.value, arguments["target"])
    return ClaimIR(
        "meets",
        FeasibilityIR(analysis.value, arguments["target"].value),
        analysis.name or "<expression>",
    )


def _candidates(arguments: dict[str, LocatedValue], span: Span) -> CandidatesIR:
    low, high = arguments["min_per_arm"], arguments["max_per_arm"]
    if low.value < 1:
        fail("domain", "min_per_arm must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_per_arm must be at least min_per_arm.", high.span)
    if high.value > MAX_PER_ARM:
        fail("domain", f"max_per_arm is currently limited to {MAX_PER_ARM}.", high.span)
    return CandidatesIR(arguments["analysis"].value, low.value, high.value)


def _one_arm(arguments: dict[str, LocatedValue], span: Span) -> OneArmModelIR:
    n = arguments["n"]
    if not 1 <= n.value <= MAX_ONE_ARM:
        fail("domain", f"n must be between 1 and {MAX_ONE_ARM}.", n.span)
    return OneArmModelIR(n.value)


def _binomial_test(arguments: dict[str, LocatedValue], span: Span) -> OneSampleAnalysisIR:
    rate = arguments["null_rate"]
    if not 0 < rate.value < 1:
        fail("domain", "null_rate must lie strictly between 0 and 1.", rate.span)
    return OneSampleAnalysisIR(arguments["model"].value, rate.value, arguments["alpha"].value)


def _one_arm_candidates(arguments: dict[str, LocatedValue], span: Span) -> OneArmCandidatesIR:
    low, high = arguments["min_n"], arguments["max_n"]
    if low.value < 1:
        fail("domain", "min_n must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_n must be at least min_n.", high.span)
    if high.value > MAX_ONE_ARM:
        fail("domain", f"max_n is currently limited to {MAX_ONE_ARM}.", high.span)
    return OneArmCandidatesIR(arguments["analysis"].value, low.value, high.value)


def _sizing(minimal: bool) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        candidates = arguments["candidates"]
        _check_point(candidates.value.analysis, arguments["target"])
        return ClaimIR(
            "sample_size",
            SizingIR(candidates.value, arguments["target"].value, minimal),
            candidates.name or "<expression>",
        )

    return build


def _two_stage_model(arguments: dict[str, LocatedValue], span: Span) -> TwoStageModelIR:
    for name, argument in arguments.items():
        if not 1 <= argument.value <= MAX_STAGE:
            fail("domain", f"{name} must be between 1 and {MAX_STAGE}.", argument.span)
    return TwoStageModelIR(arguments["n_stage1"].value, arguments["n_stage2"].value)


def _threshold_rule(arguments: dict[str, LocatedValue], span: Span) -> RuleIR:
    for name, argument in arguments.items():
        if argument.value < 0:
            fail("domain", f"{name} must be a nonnegative integer.", argument.span)
    return RuleIR(
        TwoStageRule(
            "threshold", arguments["continue_above"].value, arguments["reject_above"].value
        )
    )


def _prior(arguments: dict[str, LocatedValue], span: Span) -> PriorIR:
    for name, argument in arguments.items():
        if argument.value < 1:
            fail(
                "domain",
                f"{name} must be a positive integer; "
                "the exact posterior rule currently supports integer Beta parameters.",
                argument.span,
            )
    return PriorIR(arguments["a"].value, arguments["b"].value)


def _posterior_rule(arguments: dict[str, LocatedValue], span: Span) -> RuleIR:
    reference = arguments["reference"]
    if not 0 < reference.value < 1:
        fail("domain", "reference must lie strictly between 0 and 1.", reference.span)
    prior = arguments["prior"].value
    return RuleIR(
        TwoStageRule(
            "posterior",
            prior_a=prior.a,
            prior_b=prior.b,
            reference=reference.value,
            continue_at_least=arguments["continue_at_least"].value,
            success_at_least=arguments["success_at_least"].value,
        )
    )


def _two_stage_test(arguments: dict[str, LocatedValue], span: Span) -> TwoStageAnalysisIR:
    return TwoStageAnalysisIR(
        arguments["design"].value,
        arguments["rule"].value,
        _probability(arguments["null_rate"], "null_rate"),
    )


# Always available, with the same argument checking as module constructors.
# Their builders validate claims only; evaluate records execution slots below.
OPERATIONS = {
    "verify": _constructor(
        "verify",
        (("claim", ClaimIR),),
        "VerificationResult",
        lambda args, span: args["claim"].value,
    ),
    "calculate": _constructor(
        "calculate", (("claim", ClaimIR),), "CalculationResult", _calculation
    ),
}


# Extending this registry adds vocabulary and typed builders; parsing is unchanged.
MODULES = {
    module.name: module
    for module in (
        Module(
            "models.two_arm_binomial",
            (
                _constructor(
                    "two_arm_binomial",
                    (("n_control", "integer"), ("n_treatment", "integer")),
                    "Model",
                    _model,
                ),
                _constructor(
                    "equal_proportions",
                    (("model", ModelIR),),
                    "Hypothesis",
                    lambda args, span: HypothesisIR(args["model"].value),
                    documentation="Null: p_treatment = p_control. This declares a restriction "
                    "under which a guarantee is requested, not that the null is true.",
                ),
                _constructor(
                    "proportion_difference",
                    (("model", ModelIR), ("value", "number")),
                    "Hypothesis",
                    _difference("proportion_difference"),
                    documentation="Null: p_treatment - p_control = value. The difference is "
                    "absolute, not a relative percentage; value is exact and lies in [-1, 1]. "
                    "A zero difference is the equal-proportions null.",
                ),
                _constructor(
                    "proportion_difference_at_most",
                    (("model", ModelIR), ("value", "number")),
                    "Hypothesis",
                    _difference("proportion_difference_at_most"),
                    documentation="Null: p_treatment - p_control <= value. This is an inequality "
                    "null, including when value=0; it is not the equality null supported by "
                    "the current two-sided Fisher analysis.",
                ),
            ),
        ),
        Module(
            "sampling",
            (
                _constructor(
                    "fixed",
                    (("model", ModelIR),),
                    "StudyDesign",
                    lambda args, span: PlanIR(args["model"].value, "fixed"),
                ),
                _constructor(
                    "adaptive",
                    (("model", ModelIR),),
                    "StudyDesign",
                    lambda args, span: PlanIR(args["model"].value, "data_dependent"),
                ),
            ),
        ),
        Module(
            "tests.fisher",
            (
                _constructor(
                    "fisher",
                    (("design", PlanIR), ("null", HypothesisIR), ("alpha", "level")),
                    "Analysis",
                    _fisher,
                    hypothesis_contract=FISHER_CONTRACT,
                    documentation=FISHER_CONTRACT.guidance,
                ),
                _constructor(
                    "observe",
                    (
                        ("analysis", AnalysisIR),
                        ("control_successes", "integer"),
                        ("treatment_successes", "integer"),
                    ),
                    "Observation",
                    _observe,
                ),
                _constructor(
                    "typeI", (("analysis", AnalysisIR),), "TypeIClaim", _claim("typeI", "analysis")
                ),
                _constructor(
                    "result",
                    (("observation", ObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                ),
            ),
        ),
        Module(
            "multiplicity.bonferroni",
            (
                _constructor(
                    "bonferroni",
                    (("analyses", "list"), ("alpha", "level"), ("joint_law", "string")),
                    "Family",
                    _family,
                ),
                _constructor(
                    "familywise",
                    (("family", FamilyIR),),
                    "FamilywiseClaim",
                    _claim("familywise", "family"),
                ),
            ),
        ),
        Module(
            "planning",
            (
                _constructor(
                    "binomial_rates",
                    (("p_control", "number"), ("p_treatment", "number")),
                    "Rates",
                    _rates,
                    documentation="A planning point: one success probability per arm. "
                    "It is an input for power, not the null and not an established fact.",
                ),
                _constructor(
                    "power_target",
                    (("at", PlanningPointIR), ("minimum", "number"), ("maximum_typeI", "level")),
                    "PowerTarget",
                    _power_target,
                    documentation="Require power of at least minimum at one planning point, "
                    "and a Type I error bound of at most maximum_typeI under the null. "
                    "Power at this point is not a guarantee for other alternatives.",
                ),
                _constructor(
                    "meets",
                    (("analysis", PlannableIR), ("target", PowerTargetIR)),
                    "PlanningClaim",
                    _meets,
                    documentation="Claim that this analysis meets every component of the "
                    "target. calculate computes the components; verify must establish all.",
                ),
                _constructor(
                    "equal_arm_sizes",
                    (
                        ("analysis", AnalysisIR),
                        ("min_per_arm", "integer"),
                        ("max_per_arm", "integer"),
                    ),
                    "Candidates",
                    _candidates,
                    documentation="A finite design space: equal arm sizes within inclusive "
                    "bounds, keeping the analysis's sampling, null form, test and alpha.",
                ),
                _constructor(
                    "sample_sizes",
                    (("analysis", OneSampleAnalysisIR), ("min_n", "integer"), ("max_n", "integer")),
                    "OneArmCandidates",
                    _one_arm_candidates,
                    documentation="A finite design space: sample sizes within inclusive "
                    "bounds for a one-sample test, keeping its null rate and alpha.",
                ),
                _constructor(
                    "response_rate",
                    (("value", "number"),),
                    "Rate",
                    lambda args, span: RateIR(_probability(args["value"], "value")),
                    documentation="A planning point for a single-arm design.",
                ),
                _constructor(
                    "sample_size",
                    (("candidates", CandidateSpaceIR), ("target", PowerTargetIR)),
                    "PlanningClaim",
                    _sizing(False),
                    documentation="Claim that some candidate meets the target. The search is "
                    "ascending; a sufficient size is not claimed to be the smallest possible.",
                ),
                _constructor(
                    "smallest_sample_size",
                    (("candidates", CandidateSpaceIR), ("target", PowerTargetIR)),
                    "PlanningClaim",
                    _sizing(True),
                    documentation="Claim that a candidate meets the target and that no smaller "
                    "candidate in the declared range does. Nothing is claimed outside the range.",
                ),
            ),
        ),
        Module(
            "designs.two_stage",
            (
                _constructor(
                    "two_stage_binomial",
                    (("n_stage1", "integer"), ("n_stage2", "integer")),
                    "TwoStageModel",
                    _two_stage_model,
                    documentation="One arm, two stages, one response rate. Stage two is "
                    "observed only if the interim rule continues.",
                ),
                _constructor(
                    "threshold_rule",
                    (("continue_above", "integer"), ("reject_above", "integer")),
                    "Rule",
                    _threshold_rule,
                    documentation="Continue when stage-one responses exceed continue_above; "
                    "reject the null when total responses exceed reject_above.",
                ),
                _constructor(
                    "beta_prior",
                    (("a", "integer"), ("b", "integer")),
                    "Prior",
                    _prior,
                    documentation="Beta(a, b) prior on the response rate, positive integers.",
                ),
                _constructor(
                    "posterior_rule",
                    (
                        ("prior", PriorIR),
                        ("reference", "number"),
                        ("continue_at_least", "level"),
                        ("success_at_least", "level"),
                    ),
                    "Rule",
                    _posterior_rule,
                    documentation="Continue, and finally declare success, when the posterior "
                    "probability that the response rate exceeds reference reaches the given "
                    "level. A posterior threshold does not by itself bound Type I error.",
                ),
                _constructor(
                    "two_stage_test",
                    (("design", TwoStageModelIR), ("rule", RuleIR), ("null_rate", "number")),
                    "TwoStageAnalysis",
                    _two_stage_test,
                    documentation="The complete policy: stages, interim stop, final decision "
                    "and the null response rate it tests.",
                ),
            ),
        ),
        Module(
            "tests.binomial",
            (
                _constructor(
                    "one_arm_binomial",
                    (("n", "integer"),),
                    "OneArmModel",
                    _one_arm,
                    documentation="One arm with n independent binary responses.",
                ),
                _constructor(
                    "binomial_test",
                    (("model", OneArmModelIR), ("null_rate", "number"), ("alpha", "level")),
                    "OneSampleAnalysis",
                    _binomial_test,
                    documentation="One-sided exact binomial test. Null: response rate <= "
                    "null_rate. Rejects at the smallest response count whose upper tail "
                    "probability at null_rate is at most alpha.",
                ),
            ),
        ),
    )
}


def module_catalog() -> list[dict]:
    return [
        {
            "module": module.name,
            "constructors": [c.signature for c in module.constructors],
            "contracts": {
                c.name: c.hypothesis_contract.to_dict()
                for c in module.constructors
                if c.hypothesis_contract
            },
        }
        for module in MODULES.values()
    ]


def _typed(argument: LocatedValue, kind: str | type, name: str) -> LocatedValue:
    value = argument.value
    if isinstance(value, FieldIR):
        actual = value.value_type
        valid = not actual.optional and (
            actual.kind in (int, Fraction)
            if kind in ("level", "number")
            else actual.kind is int
            if kind == "integer"
            else actual.kind is str
            if kind == "string"
            else actual.kind == "list"
            if kind == "list"
            else isinstance(actual.kind, type) and issubclass(actual.kind, kind)
        )
        if not valid:
            expected = kind if isinstance(kind, str) else kind.__name__.removesuffix("IR")
            fail("type", f"{name} expects {expected}; received {actual.label}.", argument.span)
        return argument
    if kind == "level":
        if type(value) is int:
            value = Fraction(value)
        try:
            validate_alpha(value)
        except ValueError as error:
            fail("domain", f"{name}: {error}", argument.span)
        return LocatedValue(value, argument.span, argument.name)
    if kind == "number":
        if type(value) is int:
            value = Fraction(value)
        if not isinstance(value, Fraction):
            fail("type", f"{name} expects an exact number.", argument.span)
        return LocatedValue(value, argument.span, argument.name, argument.definition_span)
    valid = (
        (type(value) is int)
        if kind == "integer"
        else isinstance(value, str)
        if kind == "string"
        else isinstance(value, tuple)
        if kind == "list"
        else isinstance(value, kind)
    )
    if not valid:
        expected = kind if isinstance(kind, str) else kind.__name__.removesuffix("IR")
        fail(
            "type",
            f"{name} expects {expected}; received {type(value).__name__.removesuffix('IR')}.",
            argument.span,
        )
    return argument


class Elaborator:
    def __init__(self):
        self.symbols: dict[str, BindingIR] = {}
        self.constructors: dict[str, Constructor] = dict(OPERATIONS)
        self.modules: list[str] = []
        self.requests: list[RequestIR] = []
        self.invalid: set[str] = set()

    def evaluate(self, expression: Expression) -> LocatedValue:
        match expression:
            case Literal(value=value, span=span):
                return LocatedValue(value, span)
            case Reference(name=name, span=span):
                if name in self.invalid:
                    fail("dependency", f"{name!r} depends on an invalid declaration.", span)
                if name not in self.symbols:
                    fail("unknown_name", f"Unknown name {name!r}. Declare it before use.", span)
                binding = self.symbols[name]
                origin = next(
                    (
                        b.span
                        for b in self.symbols.values()
                        if b.value is binding.value and b.argument_sources
                    ),
                    binding.span,
                )
                return LocatedValue(binding.value, span, name, origin)
            case ListExpr(items=items, span=span):
                return LocatedValue(tuple(self.evaluate(item) for item in items), span)
            case FieldAccess(subject=subject, name=name, name_span=name_span):
                from statproof.language_fields import project

                value = project(self.evaluate(subject).value, name, name_span, self.requests)
                origin = next(
                    (
                        b.span
                        for b in self.symbols.values()
                        if b.value is value and b.argument_sources
                    ),
                    None,
                )
                return LocatedValue(value, expression.span, definition_span=origin)
            case Call(name=name, arguments=arguments, span=span):
                if name not in self.constructors:
                    owner = next(
                        (
                            m.name
                            for m in MODULES.values()
                            if any(c.name == name for c in m.constructors)
                        ),
                        None,
                    )
                    hint = f" Add 'use {owner}' before this declaration." if owner else ""
                    fail("unknown_constructor", f"Unknown constructor {name!r}.{hint}", span)
                constructor = self.constructors[name]
                fields = {}
                for index, argument in enumerate(arguments):
                    if argument.name is None and index >= len(constructor.parameters):
                        fail(
                            "arguments",
                            f"Too many arguments. Expected {constructor.signature}.",
                            argument.span,
                        )
                    key = argument.name or constructor.parameters[index].name
                    parameter = next((p for p in constructor.parameters if p.name == key), None)
                    if parameter is None or key in fields:
                        fail(
                            "arguments",
                            f"Unknown or repeated argument {key!r}. "
                            f"Expected {constructor.signature}.",
                            argument.span,
                        )
                    fields[key] = _typed(self.evaluate(argument.value), parameter.kind, key)
                missing = [p.name for p in constructor.parameters if p.name not in fields]
                if missing:
                    fail(
                        "arguments",
                        f"Missing {', '.join(missing)}. Expected {constructor.signature}.",
                        span,
                    )
                for key, argument in fields.items():
                    if is_deferred(argument.value):
                        fail(
                            "runtime_dependency",
                            f"{key} depends on execution. "
                            "Statistical constructors require inputs known during compilation; "
                            "bind or inspect this runtime field instead.",
                            argument.span,
                        )
                if constructor.hypothesis_contract:
                    constructor.hypothesis_contract.check(name, fields)
                value = constructor.build(fields, span)
                if name in OPERATIONS:
                    self.requests.append(RequestIR(name, value, span))
                    result_type = VerificationResultIR if name == "verify" else CalculationResultIR
                    value = result_type(len(self.requests))
                return LocatedValue(value, span)
        raise AssertionError("Unrecognized syntax node")

    def statement(self, statement: Statement) -> None:
        if statement.kind == "use":
            if statement.name not in MODULES:
                fail(
                    "unknown_module",
                    f"Unknown module {statement.name!r}. "
                    "Run 'statproof modules' to list available modules.",
                    statement.span,
                )
            if statement.name not in self.modules:
                module = MODULES[statement.name]
                for constructor in module.constructors:
                    if constructor.name in self.constructors:
                        fail(
                            "module_conflict",
                            f"Constructor {constructor.name!r} is already loaded.",
                            statement.span,
                        )
                    self.constructors[constructor.name] = constructor
                self.modules.append(statement.name)
            return
        if statement.kind == "let" and (
            statement.name in self.symbols or statement.name in self.invalid
        ):
            fail(
                "redefinition",
                f"{statement.name!r} is already declared. Bindings are immutable.",
                statement.span,
            )
        if statement.kind == "let" and statement.name in OPERATIONS:
            fail("reserved_name", f"{statement.name!r} names a built-in operation.", statement.span)
        value = self.evaluate(statement.expression).value
        if statement.kind == "let":
            fields = ()
            if isinstance(statement.expression, Call):
                constructor = self.constructors[statement.expression.name]
                fields = tuple(
                    (argument.name or constructor.parameters[index].name, argument.value.span)
                    for index, argument in enumerate(statement.expression.arguments)
                )
            self.symbols[statement.name] = BindingIR(
                statement.name,
                value,
                statement.span,
                tuple(references(statement.expression)),
                fields,
            )
        elif not isinstance(value, (VerificationResultIR, CalculationResultIR)):
            fail(
                "type",
                "Only verify(claim) and calculate(claim) may be used as statements. "
                "Use 'let' to name other objects.",
                statement.expression.span,
            )


def references(expression: Expression) -> list[str]:
    match expression:
        case Reference(name=name):
            return [name]
        case FieldAccess(subject=subject):
            return references(subject)
        case Call(arguments=arguments):
            return list(
                dict.fromkeys(name for argument in arguments for name in references(argument.value))
            )
        case ListExpr(items=items):
            return list(dict.fromkeys(name for item in items for name in references(item)))
        case _:
            return []


def elaborate(source: Source) -> tuple[ProgramIR, list[Diagnostic]]:
    statements, diagnostics = parse(source)
    elaborator = Elaborator()
    for statement in statements:
        request_count = len(elaborator.requests)
        try:
            elaborator.statement(statement)
        except LanguageError as error:
            del elaborator.requests[request_count:]
            diagnostics.append(error.diagnostic)
            if statement.kind == "let" and statement.name not in elaborator.symbols:
                elaborator.invalid.add(statement.name)
        except RecursionError:
            del elaborator.requests[request_count:]
            diagnostics.append(
                Diagnostic("depth", "Expression nesting is too deep.", statement.span)
            )
    program = ProgramIR(
        tuple(elaborator.modules), tuple(elaborator.symbols.values()), tuple(elaborator.requests)
    )
    return program, sorted(diagnostics, key=lambda d: (d.span.line, d.span.column))
