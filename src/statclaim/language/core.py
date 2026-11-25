"""The language's building blocks: parameters, constructors, modules and errors."""

from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, NoReturn

from statclaim.language_contracts import (
    HypothesisContract,
)
from statclaim.language_syntax import (
    Diagnostic,
    Span,
    refuse,
)

LANGUAGE_VERSION = "0.43.0"


@dataclass(frozen=True)
class LocatedValue:
    value: Any  # any typed value: a number, a model, an analysis, a claim
    span: Span
    name: str | None = None
    definition_span: Span | None = None


@dataclass(frozen=True)
class Parameter:
    name: str
    kind: str | type
    # An optional argument may be left out; its builder then receives None.
    optional: bool = False


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
        names = ", ".join(f"[{p.name}]" if p.optional else p.name for p in self.parameters)
        return f"{self.name}({names}) -> {self.result}"


@dataclass(frozen=True)
class Module:
    name: str
    constructors: tuple[Constructor, ...]


def fail(code: str, message: str, span: Span) -> NoReturn:
    refuse(Diagnostic(code, message, span))
    # Reached only while this check is deferred (`language_syntax.DEFERRED`): the caller
    # goes on building its value, so Lean can be asked to decide the check instead.
    return  # type: ignore[misc]


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
