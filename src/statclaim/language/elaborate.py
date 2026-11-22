"""Elaboration: from a parsed program to typed objects and requests."""

from fractions import Fraction

from statclaim.fisher import validate_alpha
from statclaim.language.core import (
    Constructor,
    LocatedValue,
    fail,
)
from statclaim.language.ir import (
    AssociationNullIR,
    BindingIR,
    CalculationResultIR,
    FieldIR,
    ObservationalStudyIR,
    ProgramIR,
    RequestIR,
    VerificationResultIR,
    is_deferred,
)
from statclaim.language.operations import (
    simulation_settings,
)
from statclaim.language.registry import (
    MODULES,
    OPERATIONS,
)
from statclaim.language_syntax import (
    Call,
    Diagnostic,
    Expression,
    FieldAccess,
    LanguageError,
    ListExpr,
    Literal,
    Reference,
    Source,
    Statement,
    parse,
)


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
            f"{name} expects {expected}; received {type(value).__name__.removesuffix('IR')}."
            + _observational_hint(value),
            argument.span,
        )
    return argument


def _observational_hint(value: object) -> str:
    """Observational values in a trial's place: say which vocabulary fits them."""
    if isinstance(value, AssociationNullIR):
        return (
            " no_association is the null of an observational study; test it with "
            "fisher_exact from tests.association. This input belongs to a randomised trial."
        )
    if isinstance(value, ObservationalStudyIR):
        return (
            " An observational study takes no_association(model=...) as its null and "
            "fisher_exact from tests.association as its test; nulls and tests of randomised "
            "arms do not apply, because exposure was not assigned."
        )
    return ""


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
                from statclaim.language_fields import project

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
                for parameter in constructor.parameters:
                    if parameter.optional and parameter.name not in fields:
                        fields[parameter.name] = LocatedValue(None, span)
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
                    settings = simulation_settings(fields) if name == "simulate" else None
                    self.requests.append(RequestIR(name, value, span, settings))
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
                    "Run 'statclaim modules' to list available modules.",
                    statement.span,
                )
            if statement.name not in self.modules:
                module = MODULES[statement.name]
                for constructor in module.constructors:
                    if self.constructors.get(constructor.name) is constructor:
                        continue
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
