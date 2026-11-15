"""Backend-free editor features over the statistical parser and module schemas."""

import bisect
import re
from dataclasses import dataclass, field
from fractions import Fraction

from statproof.language import (
    MODULES,
    OPERATIONS,
    ClaimIR,
    Elaborator,
    FieldIR,
    HypothesisIR,
    LocatedValue,
    RequestIR,
    ValueType,
    _typed,
)
from statproof.language_compiler import Compilation, compile_source
from statproof.language_fields import fields_for
from statproof.language_inspection import inspect_program, inspect_request
from statproof.language_syntax import LanguageError, Parser, Source, Span, Token, tokenize


@dataclass
class TextMap:
    source: Source

    def offset(self, position: dict) -> int:
        line = max(0, position["line"])
        starts, text = self.source.line_starts, self.source.text
        if line >= len(starts):
            return len(text)
        start = starts[line]
        end = starts[line + 1] if line + 1 < len(starts) else len(text)
        content = text[start:end].rstrip("\r\n")
        units = max(0, position["character"])
        used = 0
        for index, char in enumerate(content):
            width = len(char.encode("utf-16-le")) // 2
            if used + width > units:
                return start + index
            used += width
        return start + len(content)

    def position(self, offset: int) -> dict:
        offset = max(0, min(offset, len(self.source.text)))
        line = bisect.bisect_right(self.source.line_starts, offset) - 1
        prefix = self.source.text[self.source.line_starts[line] : offset].rstrip("\r\n")
        return {"line": line, "character": len(prefix.encode("utf-16-le")) // 2}

    def bounds(self, span: Span) -> tuple[int, int]:
        starts = self.source.line_starts
        return (
            starts[span.line - 1] + span.column - 1,
            starts[span.end_line - 1] + span.end_column - 1,
        )

    def range(self, span: Span) -> dict:
        start, end = self.bounds(span)
        return {"start": self.position(start), "end": self.position(end)}


def type_name(kind: str | type) -> str:
    if isinstance(kind, str):
        return kind
    return {"PlanIR": "StudyDesign", "Fraction": "exact number", "PlannableIR": "Analysis"}.get(
        kind.__name__, kind.__name__.removesuffix("IR")
    )


def signature(constructor) -> str:
    arguments = ", ".join(f"{p.name}: {type_name(p.kind)}" for p in constructor.parameters)
    return f"{constructor.name}({arguments}) -> {constructor.result}"


def claim_markdown(claim: ClaimIR) -> str:
    report = inspect_request(RequestIR("verify", claim, Span("<hover>", 1, 1, 1, 1)))
    description = report["target_property"]
    assumptions = "\n".join(f"- {item}" for item in report["required_assumptions"])
    return (
        f"{description}\n\nRequired assumptions:\n{assumptions}\n\n"
        "Declaring a claim is not a proof."
    )


MEANINGS = {
    "typeI": (
        "Uniform Type I error bound at the analysis's alpha under its null; "
        "does not assert the null is true."
    ),
    "familywise": (
        "Strong familywise error bound under the family's marginal-law contracts; "
        "dependence between outcomes is unrestricted."
    ),
    "result": "Claim about the exact observed result and the analysis's scoped error guarantee.",
    "verify": (
        "Plans a Lean verification returning a VerificationResult. "
        "Runs only on an explicit check, never while editing. "
        "An unsuccessful attempt does not disprove a claim."
    ),
    "calculate": (
        "Plans an exact numerical calculation returning a CalculationResult, "
        "without formal evidence. Runs only on an explicit check."
    ),
}


@dataclass
class CallContext:
    opener: str
    name: str | None
    arguments: list[list[Token]] = field(default_factory=lambda: [[]])


def call_context(tokens: list[Token]) -> list[CallContext]:
    """Track unfinished delimiters using the existing lexer, not a second grammar."""
    stack = []
    previous = None
    for token in tokens:
        if token.kind in ("NEWLINE", "EOF", "SPACE", "COMMENT"):
            continue
        if token.kind in ("(", "["):
            if stack:
                stack[-1].arguments[-1].append(token)
            name = previous.text if previous and previous.kind == "NAME" else None
            stack.append(CallContext(token.kind, name))
        elif token.kind in (")", "]"):
            expected = "(" if token.kind == ")" else "["
            if stack and stack[-1].opener == expected:
                stack.pop()
            if stack:
                stack[-1].arguments[-1].append(token)
        elif stack:
            if token.kind == ",":
                stack[-1].arguments.append([])
            else:
                stack[-1].arguments[-1].append(token)
        previous = token
    return stack


@dataclass
class Document:
    uri: str
    version: int
    text: str
    source: Source = field(init=False)
    mapping: TextMap = field(init=False)
    compilation: Compilation = field(init=False)
    tokens: list[Token] = field(init=False)

    def __post_init__(self):
        self.source = Source(self.text, self.uri)
        self.mapping = TextMap(self.source)
        self.compilation = compile_source(self.source)
        self.tokens = tokenize(self.source, include_trivia=True)[0]

    def diagnostics(self) -> list[dict]:
        return [
            {
                "range": self.mapping.range(d.span),
                "severity": 1 if d.severity == "error" else 2,
                "code": d.code,
                "source": "statproof" if d.severity == "error" else "statproof requirements",
                "message": d.message,
                **(
                    {
                        "relatedInformation": [
                            {
                                "location": {
                                    "uri": self.uri,
                                    "range": self.mapping.range(item.span),
                                },
                                "message": item.message,
                            }
                            for item in d.related
                        ]
                    }
                    if d.related
                    else {}
                ),
            }
            for d in self.compilation.diagnostics
        ]

    def token_at(self, offset: int) -> Token | None:
        for token in self.tokens:
            start, end = self.mapping.bounds(token.span)
            if start <= offset < end or (
                offset == end and token.kind in ("NAME", "COMMENT", "STRING")
            ):
                return token
        return None

    def scope(self, offset: int):
        # Parse the prefix with the same compiler. An unfinished current
        # declaration cannot introduce a binding or leak later imports.
        program = compile_source(Source(self.text[:offset], self.uri)).program
        constructors = dict(OPERATIONS)
        for name in program.modules:
            constructors.update((c.name, c) for c in MODULES[name].constructors)
        return program.bindings, constructors

    def evaluate_text(self, text: str, offset: int):
        program = compile_source(Source(self.text[:offset], self.uri)).program
        elaborator = Elaborator()
        elaborator.symbols = {b.name: b for b in program.bindings}
        elaborator.requests = list(program.requests)
        for module in program.modules:
            elaborator.constructors.update((c.name, c) for c in MODULES[module].constructors)
        parser = Parser(tokenize(Source(text, self.uri))[0])
        expression = parser.expression()
        parser.take("EOF")
        return elaborator.evaluate(expression).value

    def receiver_before(self, dot: int):
        tokens = tokenize(Source(self.text[:dot], self.uri))[0]
        for token in reversed(tokens[-256:]):
            if token.kind not in ("NAME", "(", "[", "NUMBER", "STRING"):
                continue
            start = self.mapping.bounds(token.span)[0]
            try:
                return self.evaluate_text(self.text[start:dot], start)
            except (LanguageError, RecursionError):
                continue
        return None

    def inspection(self) -> dict:
        claims = inspect_program(self.compilation)
        for claim in claims:
            claim["range"] = self.mapping.range(Span(**claim["source"]))
            for requirement in claim["requirements"]:
                requirement["range"] = self.mapping.range(Span(**requirement["source"]))
        return {
            "uri": self.uri,
            "version": self.version,
            "status": self.compilation.status,
            "claims": claims,
            "diagnostics": self.diagnostics(),
        }

    def explain(self, position: dict | None = None) -> dict:
        """Checked derivations, for the declaration at the position or the whole file.

        Returned only on request. Passing contracts never produce notifications.
        """
        from statproof.contract_reports import explain, explanation_markdown

        name = None
        if position is not None:
            offset = self.mapping.offset(position)
            token = self.token_at(offset)
            binding = self.binding_at(token) if token and token.kind == "NAME" else None
            named = {derivation.name for derivation in self.compilation.derivations}
            if binding is not None and binding.name in named:
                name = binding.name
            else:
                for candidate in self.compilation.program.bindings:
                    start, end = self.mapping.bounds(candidate.span)
                    if start <= offset <= end and candidate.name in named:
                        name = candidate.name
        contracts = explain(self.compilation, name)
        for entry in contracts:
            entry["range"] = self.mapping.range(Span(**entry["source"]))
        markdown = "\n\n".join(explanation_markdown(entry) for entry in contracts) or (
            "No contract has been validated in this file. "
            "Declarations that fail a contract are reported as diagnostics."
        )
        return {
            "uri": self.uri,
            "version": self.version,
            "contracts": contracts,
            "markdown": markdown,
        }

    def completion(self, position: dict) -> dict:
        offset = self.mapping.offset(position)
        token = self.token_at(offset)
        if token and token.kind in ("COMMENT", "STRING"):
            return {"isIncomplete": False, "items": []}
        prefix_match = re.search(r"[A-Za-z_][A-Za-z_0-9.]*$", self.text[:offset])
        prefix = prefix_match.group() if prefix_match else ""
        start = offset - len(prefix)
        end = offset
        if token and token.kind == "NAME":
            end = max(end, self.mapping.bounds(token.span)[1])
        edit_range = {"start": self.mapping.position(start), "end": self.mapping.position(end)}
        line_start = self.source.line_starts[position["line"]]
        before = self.text[line_start:start].strip()

        def item(label, kind, detail, insert=None, documentation=None):
            result = {
                "label": label,
                "kind": kind,
                "detail": detail,
                "textEdit": {"range": edit_range, "newText": insert or label},
            }
            if documentation:
                result["documentation"] = {"kind": "markdown", "value": documentation}
            return result

        if before == "use":
            return {
                "isIncomplete": False,
                "items": [
                    item(name, 9, "StatProof module") for name in MODULES if name.startswith(prefix)
                ],
            }
        dot = self.text.rfind(".", start, offset)
        if dot < 0 and start > 0 and self.text[start - 1] == ".":
            dot = start - 1
        if dot >= 0:
            receiver = self.receiver_before(dot)
            field_prefix = self.text[dot + 1 : offset]
            edit_range["start"] = self.mapping.position(dot + 1)
            suffix = re.match(r"[A-Za-z_0-9]*", self.text[offset:]).group()
            edit_range["end"] = self.mapping.position(offset + len(suffix))
            optional = isinstance(receiver, FieldIR) and receiver.value_type.optional
            return {
                "isIncomplete": False,
                "items": [
                    item(
                        name,
                        5,
                        ValueType(spec.kind, spec.optional or optional).label,
                        documentation=spec.description,
                    )
                    for name, spec in fields_for(receiver).items()
                    if name.startswith(field_prefix)
                ],
            }
        bindings, constructors = self.scope(start)
        tokens = tokenize(Source(self.text[:start], self.uri))[0]
        stack = call_context(tokens)
        expected = None
        fields = []
        if stack and stack[-1].opener == "(" and stack[-1].name in constructors:
            context = stack[-1]
            constructor = constructors[context.name]
            current = context.arguments[-1]
            used = set()
            for index, argument in enumerate(context.arguments[:-1]):
                if len(argument) >= 2 and argument[1].kind == "=":
                    used.add(argument[0].text)
                elif index < len(constructor.parameters):
                    used.add(constructor.parameters[index].name)
            if len(current) >= 2 and current[0].kind == "NAME" and current[1].kind == "=":
                parameter = next(
                    (p for p in constructor.parameters if p.name == current[0].text), None
                )
            else:
                parameter = next((p for p in constructor.parameters if p.name not in used), None)
                if not current:
                    fields = [
                        item(
                            p.name,
                            5,
                            f"{p.name}: {type_name(p.kind)}",
                            p.name if self.text[end:].lstrip().startswith("=") else p.name + "=",
                        )
                        for p in constructor.parameters
                        if p.name not in used
                    ]
            expected = parameter.kind if parameter else None
        # Legacy command spelling also has a claim argument.
        elif re.search(r"\b(?:verify|calculate)\s+$", self.text[:start]):
            expected = ClaimIR
        items = fields
        for binding in bindings:
            if expected is not None:
                try:
                    _typed(LocatedValue(binding.value, binding.span), expected, binding.name)
                except LanguageError:
                    continue
            kind = (
                binding.value.value_type.label
                if isinstance(binding.value, FieldIR)
                else type_name(type(binding.value))
            )
            items.append(item(binding.name, 6, kind))
        for constructor in constructors.values():
            # Schemas use a more specific display type for claim constructors.
            result_type = constructor.result
            if expected is not None and not (
                result_type == type_name(expected)
                or (expected is ClaimIR and result_type.endswith("Claim"))
            ):
                continue
            items.append(
                item(
                    constructor.name,
                    3,
                    signature(constructor),
                    documentation=constructor.documentation or MEANINGS.get(constructor.name),
                )
            )
        if not stack and not before:
            items.extend(item(name, 14, "StatProof declaration") for name in ("use", "let"))
        return {"isIncomplete": False, "items": [i for i in items if i["label"].startswith(prefix)]}

    def binding_at(self, token: Token):
        offset = self.mapping.bounds(token.span)[0]
        significant = [t for t in self.tokens if t.kind not in ("SPACE", "COMMENT", "NEWLINE")]
        index = significant.index(token)
        following = significant[index + 1] if index + 1 < len(significant) else None
        previous = significant[index - 1] if index else None
        # Argument labels and constructor calls are not references to values,
        # even if a binding happens to use the same spelling.
        if following and (
            following.kind == "("
            or (following.kind == "=" and (not previous or previous.text != "let"))
        ):
            return None
        for binding in self.compilation.program.bindings:
            if (
                binding.name == token.text.split(".")[0]
                and self.mapping.bounds(binding.span)[0] <= offset
            ):
                return binding
        return None

    def definition(self, position: dict):
        token = self.token_at(self.mapping.offset(position))
        if not token or token.kind != "NAME":
            return None
        binding = self.binding_at(token)
        if binding is None:
            return None
        declaration_start = self.mapping.bounds(binding.span)[0]
        tokens = [
            t
            for t in self.tokens
            if self.mapping.bounds(t.span)[0] >= declaration_start
            and t.kind not in ("SPACE", "COMMENT", "NEWLINE")
        ]
        name = tokens[1]
        return {"uri": self.uri, "range": self.mapping.range(name.span)}

    def hover(self, position: dict):
        offset = self.mapping.offset(position)
        token = self.token_at(offset)
        if not token or token.kind != "NAME":
            return None
        start = self.mapping.bounds(token.span)[0]
        field_start = start
        for name in token.text.split("."):
            field_end = field_start + len(name)
            if field_start <= offset <= field_end:
                if field_start > start or (field_start and self.text[field_start - 1] == "."):
                    receiver = self.receiver_before(field_start - 1)
                    spec = fields_for(receiver).get(name)
                    if spec:
                        optional = spec.optional or (
                            isinstance(receiver, FieldIR) and receiver.value_type.optional
                        )
                        text = f"```stat\n{name}: {ValueType(spec.kind, optional).label}\n```"
                        if spec.description:
                            text += "\n\n" + spec.description
                        if isinstance(receiver, (FieldIR,)) or optional:
                            text += "\n\nRuntime fields remain unevaluated while editing."
                        return {
                            "contents": {"kind": "markdown", "value": text},
                            "range": self.mapping.range(self.source.span(field_start, field_end)),
                        }
                break
            field_start = field_end + 1
        binding = self.binding_at(token)
        if binding:
            kind = (
                binding.value.value_type.label
                if isinstance(binding.value, FieldIR)
                else type_name(type(binding.value))
            )
            if isinstance(binding.value, (int, Fraction)):
                kind += f" = {binding.value}"
            text = f"```stat\n{binding.name}: {kind}\n```"
            if isinstance(binding.value, ClaimIR):
                text += "\n\n" + claim_markdown(binding.value)
            if isinstance(binding.value, HypothesisIR):
                text += f"\n\nDeclared null: `{binding.value.statement}`.\n\n"
                text += (
                    "This describes a parameter restriction; "
                    "it does not assert that the null is true."
                )
            if kind in ("VerificationResult", "CalculationResult"):
                text += "\n\nPlanned result only. Editor analysis does not execute this operation."
        else:
            _, constructors = self.scope(self.mapping.bounds(token.span)[0])
            constructor = constructors.get(token.text)
            if constructor is None:
                return None
            text = f"```stat\n{signature(constructor)}\n```"
            if constructor.hypothesis_contract:
                text += f"\n\nSupported null: `{constructor.hypothesis_contract.expected}`."
            if constructor.documentation:
                text += "\n\n" + constructor.documentation
            elif token.text in MEANINGS:
                text += "\n\n" + MEANINGS[token.text]
        return {
            "contents": {"kind": "markdown", "value": text},
            "range": self.mapping.range(token.span),
        }
