"""Declarative analysis contracts checked by the common elaborator."""

from dataclasses import dataclass

from statclaim.language_syntax import Diagnostic, LanguageError, RelatedLocation


@dataclass(frozen=True)
class HypothesisContract:
    supported_predicates: tuple[str, ...]
    expected: str
    guidance: str
    design_argument: str = "design"
    null_argument: str = "null"
    # When set, the null's value must equal this; other values are a different question.
    required_value: object = None
    # Bump when the supported nulls change.
    version: int = 1

    def accepts(self, design, hypothesis) -> bool:
        return (
            design.model == hypothesis.model
            and hypothesis.predicate in self.supported_predicates
            and (self.required_value is None or hypothesis.value == self.required_value)
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
        if type(design.model) is not type(null.model):
            message = (
                f"{name}: the design and the null use different outcome models. "
                "Declare the design and the null over the same model."
            )
            raise LanguageError(
                Diagnostic("model_mismatch", message, argument.span, related=related)
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
        if null.predicate not in self.supported_predicates or (
            self.required_value is not None and null.value != self.required_value
        ):
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
            "version": self.version,
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

ONE_SIDED_FISHER_CONTRACT = HypothesisContract(
    ("proportion_difference_at_most",),
    "p_treatment - p_control <= 0 (the treatment is no better than the control)",
    "The one-sided Fisher analysis tests whether the treatment's success probability exceeds "
    "the control's. Its null is proportion_difference_at_most(model=..., value=0). A nonzero "
    "margin is a different question and needs an analysis that supports it. Use "
    "equal_proportions with fisher(...) for a two-sided question.",
    required_value=0,
)

MARGIN_CONTRACT = HypothesisContract(
    ("proportion_difference_at_most",),
    "p_treatment - p_control <= margin, for a margin strictly between -1 and 1",
    "The exact difference test rejects when the treatment's observed success proportion "
    "exceeds the control's by enough. Its null is "
    "proportion_difference_at_most(model=..., value=margin). A negative margin is a "
    "non-inferiority question; zero is superiority.",
)

EQUAL_MEANS_CONTRACT = HypothesisContract(
    ("equal_means",),
    "mean_treatment = mean_control",
    "The two-sided test asks whether the arm means differ. Its null is equal_means(model=...). "
    "For a one-sided or non-inferiority question, use the one-sided test with "
    "mean_difference_at_most(model=..., value=...).",
)

MEAN_DIFFERENCE_CONTRACT = HypothesisContract(
    ("mean_difference_at_most",),
    "mean_treatment - mean_control <= value",
    "The one-sided test rejects when the treatment mean exceeds the control mean by enough. "
    "Its null is mean_difference_at_most(model=..., value=...): zero for superiority, a "
    "negative value for non-inferiority. Use equal_means with the two-sided test for a "
    "two-sided question.",
)
