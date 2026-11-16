"""Source-preserving syntax for the small statistical file language.

The parser knows declarations, calls, references, lists, and exact literals.
Statistical constructors and claim meanings belong to the module registry.
"""

import bisect
import json
import re
from dataclasses import asdict, dataclass
from fractions import Fraction
from functools import cached_property


@dataclass(frozen=True)
class Span:
    path: str
    line: int
    column: int
    end_line: int
    end_column: int

    def to_dict(self) -> dict:
        return asdict(self)


@dataclass(frozen=True)
class Source:
    text: str
    path: str = "<input>"

    @cached_property
    def line_starts(self) -> list[int]:
        return [0, *(match.end() for match in re.finditer("\n", self.text))]

    def span(self, start: int, end: int) -> Span:
        starts = self.line_starts
        first = bisect.bisect_right(starts, start) - 1
        last = bisect.bisect_right(starts, end) - 1
        return Span(
            self.path, first + 1, start - starts[first] + 1, last + 1, end - starts[last] + 1
        )


@dataclass(frozen=True)
class RelatedLocation:
    message: str
    span: Span

    def to_dict(self) -> dict:
        return {"message": self.message, "source": self.span.to_dict()}


@dataclass(frozen=True)
class Diagnostic:
    code: str
    message: str
    span: Span
    severity: str = "error"
    related: tuple[RelatedLocation, ...] = ()

    def to_dict(self) -> dict:
        result = {
            "code": self.code,
            "message": self.message,
            "severity": self.severity,
            "source": self.span.to_dict(),
        }
        if self.related:
            result["related"] = [item.to_dict() for item in self.related]
        return result

    def format(self, source: Source) -> str:
        location = f"{self.span.path}:{self.span.line}:{self.span.column}"
        lines = source.text.splitlines()
        line = lines[self.span.line - 1] if self.span.line <= len(lines) else ""
        width = (
            max(1, self.span.end_column - self.span.column)
            if (self.span.line == self.span.end_line)
            else 1
        )
        return (
            f"{location}: {self.severity} [{self.code}]: {self.message}\n"
            f"  {line}\n  {' ' * (self.span.column - 1)}{'^' * width}"
        )


class LanguageError(Exception):
    def __init__(self, diagnostic: Diagnostic):
        super().__init__(diagnostic.message)
        self.diagnostic = diagnostic


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    span: Span


@dataclass(frozen=True)
class Literal:
    value: int | Fraction | str
    span: Span


@dataclass(frozen=True)
class Reference:
    name: str
    span: Span


@dataclass(frozen=True)
class ListExpr:
    items: tuple["Expression", ...]
    span: Span


@dataclass(frozen=True)
class Argument:
    name: str | None
    value: "Expression"
    span: Span


@dataclass(frozen=True)
class Call:
    name: str
    arguments: tuple[Argument, ...]
    span: Span


@dataclass(frozen=True)
class FieldAccess:
    subject: "Expression"
    name: str
    name_span: Span
    span: Span


type Expression = Literal | Reference | ListExpr | Call | FieldAccess


@dataclass(frozen=True)
class Statement:
    kind: str
    name: str | None
    expression: Expression | None
    span: Span


_TOKEN = re.compile(
    r"(?P<SPACE>[ \t\r]+)|(?P<COMMENT>\#[^\n]*)|(?P<NEWLINE>\n)|"
    r'(?P<STRING>"(?:[^"\\\n]|\\[^\n])*")|(?P<NUMBER>-?\d+(?:\.\d+)?)|'
    r"(?P<NAME>[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)|"
    r"(?P<PUNCT>[()\[\],=/.])"
)


def tokenize(
    source: Source, *, include_trivia: bool = False
) -> tuple[list[Token], list[Diagnostic]]:
    tokens, diagnostics = [], []
    offset = 0
    while offset < len(source.text):
        match = _TOKEN.match(source.text, offset)
        if not match:
            diagnostics.append(
                Diagnostic(
                    "syntax",
                    f"Unexpected character {source.text[offset]!r}.",
                    source.span(offset, offset + 1),
                )
            )
            offset += 1
            continue
        kind, text = match.lastgroup, match.group()
        if include_trivia or kind not in ("SPACE", "COMMENT"):
            tokens.append(
                Token(text if kind == "PUNCT" else kind, text, source.span(offset, match.end()))
            )
        offset = match.end()
    tokens.append(Token("EOF", "", source.span(offset, offset)))
    return tokens, diagnostics


class Parser:
    def __init__(self, tokens: list[Token]):
        self.tokens, self.position = tokens, 0

    @property
    def current(self) -> Token:
        return self.tokens[self.position]

    def take(self, kind: str, message: str | None = None) -> Token:
        token = self.current
        if token.kind != kind:
            raise LanguageError(Diagnostic("syntax", message or f"Expected {kind!r}.", token.span))
        self.position += kind != "EOF"
        return token

    def newlines(self) -> None:
        while self.current.kind == "NEWLINE":
            self.position += 1

    def expression(self) -> Expression:
        value = self.atom()
        while self.current.kind == ".":
            self.take(".")
            name = self.take("NAME", "Expected a field name after '.'.")
            value = self.fields(value, name)
        return value

    @staticmethod
    def fields(value: Expression, token: Token) -> Expression:
        column = token.span.column
        for name in token.text.split("."):
            span = Span(
                token.span.path, token.span.line, column, token.span.end_line, column + len(name)
            )
            value = FieldAccess(value, name, span, Parser.join(value.span, span))
            column += len(name) + 1
        return value

    def atom(self) -> Expression:
        token = self.current
        if token.kind == "NUMBER":
            self.take("NUMBER")
            value = Fraction(token.text) if "." in token.text else int(token.text)
            end = token.span
            if self.current.kind == "/":
                self.take("/")
                denominator = self.take("NUMBER", "Expected an integer denominator after '/'.")
                if "." in token.text or "." in denominator.text:
                    raise LanguageError(
                        Diagnostic(
                            "number",
                            "A rational needs integer numerator and denominator.",
                            token.span,
                        )
                    )
                try:
                    value = Fraction(value, int(denominator.text))
                except ZeroDivisionError as error:
                    raise LanguageError(
                        Diagnostic("number", "A denominator cannot be zero.", denominator.span)
                    ) from error
                end = denominator.span
            return Literal(value, self.join(token.span, end))
        if token.kind == "STRING":
            self.take("STRING")
            try:
                return Literal(json.loads(token.text), token.span)
            except ValueError as error:
                raise LanguageError(
                    Diagnostic("string", "Invalid string escape.", token.span)
                ) from error
        if token.kind == "[":
            self.take("[")
            items = []
            self.newlines()
            while self.current.kind != "]":
                items.append(self.expression())
                self.newlines()
                if self.current.kind != ",":
                    break
                self.take(",")
                self.newlines()
            end = self.take("]", "Expected ']' to finish the list.")
            return ListExpr(tuple(items), self.join(token.span, end.span))
        if token.kind == "NAME":
            self.take("NAME")
            if self.current.kind != "(":
                first, _, rest = token.text.partition(".")
                span = Span(
                    token.span.path,
                    token.span.line,
                    token.span.column,
                    token.span.line,
                    token.span.column + len(first),
                )
                value = Reference(first, span)
                if rest:
                    tail_span = Span(
                        token.span.path,
                        token.span.line,
                        span.end_column + 1,
                        token.span.end_line,
                        token.span.end_column,
                    )
                    value = self.fields(value, Token("NAME", rest, tail_span))
                return value
            self.take("(")
            arguments = []
            named = False
            self.newlines()
            while self.current.kind != ")":
                start = self.current.span
                name = None
                if self.current.kind == "NAME" and self.tokens[self.position + 1].kind == "=":
                    name = self.take("NAME").text
                    self.take("=")
                    named = True
                elif named:
                    raise LanguageError(
                        Diagnostic(
                            "syntax", "Positional arguments must precede named arguments.", start
                        )
                    )
                value = self.expression()
                arguments.append(Argument(name, value, self.join(start, value.span)))
                self.newlines()
                if self.current.kind != ",":
                    break
                self.take(",")
                self.newlines()
            end = self.take(")", "Expected ')' to finish the call.")
            return Call(token.text, tuple(arguments), self.join(token.span, end.span))
        raise LanguageError(
            Diagnostic("syntax", "Expected a name, call, exact number, or list.", token.span)
        )

    @staticmethod
    def join(first: Span, last: Span) -> Span:
        return Span(first.path, first.line, first.column, last.end_line, last.end_column)

    def statement(self) -> Statement:
        start = self.take("NAME", "Expected 'use', 'let', or an operation call.")
        if start.text == "use":
            module = self.take("NAME", "Expected a module name after 'use'.")
            return Statement("use", module.text, None, self.join(start.span, module.span))
        if start.text == "let":
            identifier = self.take("NAME", "Expected a binding name after 'let'.")
            if "." in identifier.text:
                raise LanguageError(
                    Diagnostic("name", "Binding names cannot contain dots.", identifier.span)
                )
            self.take("=", "Expected '=' after the binding name.")
            value = self.expression()
            return Statement("let", identifier.text, value, self.join(start.span, value.span))
        # Preserve the original command spelling as sugar for an ordinary call.
        if start.text in ("verify", "calculate") and self.current.kind != "(":
            value = self.expression()
            span = self.join(start.span, value.span)
            call = Call(start.text, (Argument(None, value, value.span),), span)
            return Statement("expression", None, call, span)
        self.position -= 1
        value = self.expression()
        if not isinstance(value, Call):
            raise LanguageError(
                Diagnostic("syntax", "Expected an operation call or a declaration.", value.span)
            )
        return Statement("expression", None, value, value.span)


def parse(source: Source) -> tuple[list[Statement], list[Diagnostic]]:
    tokens, diagnostics = tokenize(source)
    parser = Parser(tokens)
    statements = []
    while parser.current.kind != "EOF":
        parser.newlines()
        if parser.current.kind == "EOF":
            break
        try:
            statement = parser.statement()
            if parser.current.kind not in ("NEWLINE", "EOF"):
                raise LanguageError(
                    Diagnostic(
                        "syntax", "Expected a newline after the statement.", parser.current.span
                    )
                )
            statements.append(statement)
        except LanguageError as error:
            diagnostics.append(error.diagnostic)
            while parser.current.kind not in ("NEWLINE", "EOF"):
                parser.position += 1
        except (ValueError, RecursionError) as error:
            diagnostics.append(
                Diagnostic(
                    "syntax",
                    f"Invalid or excessively nested expression: {error}",
                    parser.current.span,
                )
            )
            while parser.current.kind not in ("NEWLINE", "EOF"):
                parser.position += 1
    return statements, diagnostics
