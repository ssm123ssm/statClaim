"""Declarative analysis contracts checked by the common elaborator."""

from dataclasses import dataclass

from statclaim.language_syntax import Diagnostic, RelatedLocation, refuse


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
        if getattr(design.model, "observational", False):
            # Exposure was not assigned, so no test of randomised arms applies.
            kind = design.model.design.replace("_", "-")
            return refuse(
                Diagnostic(
                    "observational_design",
                    f"{name} relies on randomised arms, but this is an observational {kind} "
                    "study: exposure was not assigned. Use fisher_exact from tests.association "
                    "to test association.",
                    arguments[self.design_argument].span,
                )
            )
        if type(design.model) is not type(null.model) or getattr(
            design.model, "outcome", None
        ) != getattr(null.model, "outcome", None):
            message = (
                f"{name}: the design and the null use different outcome models. "
                "Declare the design and the null over the same model."
            )
            return refuse(Diagnostic("model_mismatch", message, argument.span, related=related))
        if design.model != null.model:
            sizes = (design.model.n_control, design.model.n_treatment)
            other = (null.model.n_control, null.model.n_treatment)
            difference = (
                f"The analysis design has arm sizes {sizes}, while the null's model has {other}. "
                if sizes != other
                else "The two models have the same arm sizes but differ in their assignment "
                "or outcome. "
            )
            message = (
                f"{name}: the null belongs to a different model. {difference}"
                "Declare the intended null for the design's model. "
                "Matching a null form alone does not make different models compatible."
            )
            return refuse(Diagnostic("model_mismatch", message, argument.span, related=related))
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
            return refuse(
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

RANDOMISATION_CONTRACT = HypothesisContract(
    ("no_effect",),
    "treatment changes no participant's outcome (the sharp null)",
    "The randomisation test supports only the sharp null no_effect(model=...). It does not "
    "test equal means or proportions: when effects differ between participants, its error "
    "under those nulls is not guaranteed. Keep your null if it states your question, and "
    "choose a test that supports it.",
)
