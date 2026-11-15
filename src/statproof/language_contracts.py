"""Declarative analysis contracts checked by the common elaborator."""

from dataclasses import dataclass

from statproof.language_syntax import Diagnostic, LanguageError, RelatedLocation


@dataclass(frozen=True)
class HypothesisContract:
    supported_predicates: tuple[str, ...]
    expected: str
    guidance: str
    design_argument: str = "design"
    null_argument: str = "null"

    def accepts(self, design, hypothesis) -> bool:
        return (
            design.model == hypothesis.model and hypothesis.predicate in self.supported_predicates
        )

    def check(self, name: str, arguments: dict) -> None:
        design = arguments[self.design_argument].value
        argument = arguments[self.null_argument]
        null = argument.value
        related = (
            ()
            if argument.definition_span is None
            else (RelatedLocation(f"Declared null: {null.statement}", argument.definition_span),)
        )
        if design.model != null.model:
            message = (
                f"{name}: the null belongs to a different model. "
                f"The analysis design has arm sizes ({design.model.n_control}, "
                f"{design.model.n_treatment}), while the null's model has "
                f"({null.model.n_control}, {null.model.n_treatment}). "
                "Declare the intended null for the design's model. "
                "Matching a null form alone does not make different models compatible."
            )
            raise LanguageError(
                Diagnostic("model_mismatch", message, argument.span, related=related)
            )
        if null.predicate not in self.supported_predicates:
            message = (
                f"{name}: hypothesis contract mismatch.\n"
                f"Declared null: {null.statement}.\n"
                f"Supported null: {self.expected}.\n{self.guidance}\n"
                "This is a limitation of the supported analysis/proof contract, "
                "not a proof that your null is false."
            )
            raise LanguageError(
                Diagnostic("hypothesis_mismatch", message, argument.span, related=related)
            )

    def to_dict(self) -> dict:
        return {
            "supported_predicates": list(self.supported_predicates),
            "expected_null": self.expected,
            "guidance": self.guidance,
            "same_model_required": True,
        }


FISHER_CONTRACT = HypothesisContract(
    ("equal_proportions",),
    "p_treatment = p_control (equal arm success probabilities)",
    "The current Fisher analysis and its checked guarantee support equality only. "
    "Keep your declared null if it expresses the intended question and choose or implement "
    "an analysis whose contract supports it. Use equal_proportions(model=...) only if "
    "equality is the intended null; replacing the null changes the statistical question.",
)
