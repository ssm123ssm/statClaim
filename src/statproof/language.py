"""Typed statistical objects and module-driven elaboration of .stat files.

No Python or Lean source in a user file is executed. Module builders lower the
supported objects to the same validated requests as the TOML and Lean routes.
"""

from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction
from typing import Literal as Choice

from statproof.design import Design
from statproof.family import Endpoint, FisherFamily
from statproof.fisher import validate_alpha
from statproof.language_syntax import (
    Call,
    Diagnostic,
    Expression,
    LanguageError,
    ListExpr,
    Literal,
    Reference,
    Source,
    Span,
    Statement,
    parse,
)


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


@dataclass(frozen=True)
class AnalysisIR:
    plan: PlanIR
    hypothesis: HypothesisIR
    alpha: Fraction

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
class ClaimIR:
    kind: Choice["typeI", "familywise", "result"]
    subject: AnalysisIR | FamilyIR | ObservationIR
    name: str


@dataclass(frozen=True)
class LocatedValue:
    value: object
    span: Span
    name: str | None = None


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
class ProgramIR:
    modules: tuple[str, ...]
    bindings: tuple[BindingIR, ...]
    requests: tuple[RequestIR, ...]

    def to_dict(self) -> dict:
        return {
            "language_version": "0.1.0",
            "modules": list(self.modules),
            "bindings": [
                {
                    "name": b.name,
                    "type": type(b.value).__name__,
                    "value": normalize(b.value),
                    "source": b.span.to_dict(),
                    "dependencies": list(b.dependencies),
                    "argument_sources": {name: span.to_dict() for name, span in b.argument_sources},
                }
                for b in self.bindings
            ],
            "requests": [
                {"operation": r.operation, "claim": normalize(r.claim), "source": r.span.to_dict()}
                for r in self.requests
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
        case HypothesisIR(model=model):
            return {"predicate": "equal_proportions", "model": normalize(model)}
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
        case ClaimIR(kind=kind, subject=subject, name=name):
            return {"kind": kind, "subject_name": name, "subject": normalize(subject)}
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
    if plan.model != hypothesis.model:
        fail(
            "model_mismatch",
            "The null hypothesis belongs to a different model. "
            "Declare equal_proportions for this design's model.",
            arguments["null"].span,
        )
    return AnalysisIR(plan, hypothesis, arguments["alpha"].value)


def _family(arguments: dict[str, LocatedValue], span: Span) -> FamilyIR:
    items = arguments["analyses"].value
    if len(items) != 2:
        fail(
            "family_size",
            "The Fisher-family adapter currently requires exactly two analyses.",
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
    name: str, parameters: tuple[tuple[str, str | type], ...], result: str, build: Callable
) -> Constructor:
    return Constructor(name, tuple(Parameter(*p) for p in parameters), result, build)


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
    )
}


def module_catalog() -> list[dict]:
    return [
        {"module": module.name, "constructors": [c.signature for c in module.constructors]}
        for module in MODULES.values()
    ]


def _typed(argument: LocatedValue, kind: str | type, name: str) -> LocatedValue:
    value = argument.value
    if kind == "level":
        if type(value) is int:
            value = Fraction(value)
        try:
            validate_alpha(value)
        except ValueError as error:
            fail("domain", f"{name}: {error}", argument.span)
        return LocatedValue(value, argument.span, argument.name)
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
        self.constructors: dict[str, Constructor] = {}
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
                return LocatedValue(self.symbols[name].value, span, name)
            case ListExpr(items=items, span=span):
                return LocatedValue(tuple(self.evaluate(item) for item in items), span)
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
                return LocatedValue(constructor.build(fields, span), span)
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
        elif not isinstance(value, ClaimIR):
            fail(
                "type",
                "Verification and calculation require a claim such as typeI(analysis), "
                "familywise(family), or result(observation).",
                statement.expression.span,
            )
        elif statement.kind == "calculate" and value.kind != "result":
            fail(
                "type",
                "Only result(observation) is a numerical calculation. "
                "Use 'verify' for design guarantees.",
                statement.expression.span,
            )
        else:
            self.requests.append(RequestIR(statement.kind, value, statement.span))


def references(expression: Expression) -> list[str]:
    match expression:
        case Reference(name=name):
            return [name]
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
        try:
            elaborator.statement(statement)
        except LanguageError as error:
            diagnostics.append(error.diagnostic)
            if statement.kind == "let" and statement.name not in elaborator.symbols:
                elaborator.invalid.add(statement.name)
        except RecursionError:
            diagnostics.append(
                Diagnostic("depth", "Expression nesting is too deep.", statement.span)
            )
    program = ProgramIR(
        tuple(elaborator.modules), tuple(elaborator.symbols.values()), tuple(elaborator.requests)
    )
    return program, sorted(diagnostics, key=lambda d: (d.span.line, d.span.column))
