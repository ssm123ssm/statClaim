"""Typed statistical objects and module-driven elaboration of .stat files.

No Python or Lean source in a user file is executed. Module builders lower the
supported objects to the same validated requests as the TOML and Lean routes.
"""

from collections.abc import Callable
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Literal as Choice

from statclaim.composition import MODES, Component, Composition
from statclaim.design import Design
from statclaim.family import MAX_ENDPOINTS, Endpoint, FisherFamily
from statclaim.fisher import validate_alpha
from statclaim.language_contracts import (
    FISHER_CONTRACT,
    MARGIN_CONTRACT,
    ONE_SIDED_FISHER_CONTRACT,
    RANDOMISATION_CONTRACT,
    HypothesisContract,
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
    Span,
    Statement,
    parse,
)
from statclaim.methods import METHOD_MODULES, NULL_FORMS, OUTCOMES, SHARP_NULL, methods_for
from statclaim.methods.assumptions import (
    ACCOUNTS_FOR,
    CONTRADICTED_BY,
    DECLARED_VALID,
    HIGHER_IS_BETTER,
    LOWER_IS_BETTER,
)
from statclaim.methods.core import SCOPES, Assumption, CitedMethod, Guarantee
from statclaim.planning import (
    CRITERIA,
    MAX_CITED_ARM,
    MAX_MARGIN_ARM,
    MAX_ONE_ARM,
    MAX_PER_ARM,
    MAX_RATIO,
    MAX_SEARCH_TOTAL,
    MAX_STAGE,
    BinomialInterval,
    DifferenceInterval,
    MarginTest,
    OneSamplePlan,
    OneSampleResult,
    PowerPlan,
    TwoStagePlan,
    TwoStageResult,
    TwoStageRule,
)
from statclaim.randomisation import (
    MAX_DRAWS,
    MAX_UNITS,
    SCHEMES,
    RandomisationTest,
    count_splits,
    groups_of,
    splits_needed,
)

LANGUAGE_VERSION = "0.13.0"


class PlannableIR:
    """An analysis that planning targets can be assessed against."""


class TwoArmTestIR(PlannableIR):
    """A two-arm analysis whose arm sizes a planning search can vary."""


class CandidateSpaceIR:
    """A finite set of candidate designs for a sample-size search."""


class PlanningPointIR:
    """A parameter point used for planning; never a replacement for the null."""


class StudyModelIR:
    """A sampling model that a study design can be declared over."""


class LevelTestIR:
    """An analysis that a Type I error claim can be requested for."""


class NullIR:
    """A null hypothesis about any kind of two-arm model."""


@dataclass(frozen=True)
class AssignmentIR:
    """How participants reach the two arms: the arm sizes, whether whole clusters, such
    as clinics, were assigned instead of single participants, and how the assignment was
    randomised when the file says so.

    Later design declarations, such as strata, belong here.
    """

    n_control: int
    n_treatment: int
    # Numbers of clusters per arm when clusters were randomised; None when participants were.
    clusters_control: int | None = None
    clusters_treatment: int | None = None
    # A key of randomisation.SCHEMES when declared. Only a randomisation test reads it.
    randomisation: str | None = None
    # For stratified or blocked randomisation: (control, treatment) randomised units per
    # stratum, and the block size. Units are clusters when clusters were randomised.
    strata: tuple[tuple[int, int], ...] = ()
    block_size: int | None = None

    @property
    def clustered(self) -> bool:
        return self.clusters_control is not None

    @property
    def randomised_units(self) -> tuple[str, int, int]:
        """What was randomised: the kind of unit, how many, and how many were treated."""
        if self.clustered:
            return (
                "cluster",
                self.clusters_control + self.clusters_treatment,
                self.clusters_treatment,
            )
        return ("participant", self.n_control + self.n_treatment, self.n_treatment)

    @property
    def groups(self) -> tuple[tuple[int, int], ...]:
        """The groups randomised independently, as (units, treated), when declared."""
        _, units, treated = self.randomised_units
        return groups_of(units, treated, self.randomisation, self.strata, self.block_size)


@dataclass(frozen=True)
class StratumIR:
    """One stratum of a stratified assignment: randomised units per arm."""

    control: int
    treatment: int


@dataclass(frozen=True)
class OutcomeIR:
    """What is measured on each participant: its kind, which direction is better, and how
    many times it is measured."""

    kind: str  # a key of OUTCOMES
    # "higher" or "lower": which direction of the outcome is better, when declared.
    better: str | None = None
    measurements: int = 1


@dataclass(frozen=True)
class TwoArmModelIR(StudyModelIR):
    """Two arms, built from an assignment and an outcome. No distribution is fixed."""

    assignment: AssignmentIR
    measured: OutcomeIR

    @property
    def n_control(self) -> int:
        return self.assignment.n_control

    @property
    def n_treatment(self) -> int:
        return self.assignment.n_treatment

    @property
    def better(self) -> str | None:
        return self.measured.better

    @property
    def outcome(self) -> str:
        return self.measured.kind

    @property
    def features(self) -> tuple[str, ...]:
        """Declared design features that can contradict a test's assumptions."""
        return (
            *(("repeated_measures",) if self.measured.measurements > 1 else ()),
            *(("clusters",) if self.assignment.clustered else ()),
        )


@dataclass(frozen=True)
class ModelIR(TwoArmModelIR):
    """Two arms with a yes-or-no outcome: the Lean-backed binomial model."""

    def __post_init__(self):
        if self.measured.kind != "binary":
            raise ValueError("The binomial model needs a binary outcome.")


@dataclass(frozen=True)
class OutcomeModelIR(TwoArmModelIR):
    """Two arms with an outcome of a registered kind other than binary."""

    def __post_init__(self):
        if self.measured.kind == "binary":
            raise ValueError("A binary outcome gives the binomial model.")


def two_arm_model(assignment: AssignmentIR, measured: OutcomeIR) -> TwoArmModelIR:
    """The same pieces always give the same model, however a file spells them."""
    kind = ModelIR if measured.kind == "binary" else OutcomeModelIR
    return kind(assignment, measured)


@dataclass(frozen=True)
class OutcomeNullIR(NullIR):
    """A null hypothesis in one of the forms registered for the model's outcome."""

    model: OutcomeModelIR
    predicate: str
    value: Fraction = Fraction(0)

    @property
    def statement(self) -> str:
        return NULL_FORMS[self.predicate][1].state(self.value)


@dataclass(frozen=True)
class SharpNullIR(NullIR):
    """The sharp null on any two-arm model: treatment changes no participant's outcome.

    It is not a restriction on means or proportions, and only a randomisation test takes it.
    """

    model: TwoArmModelIR
    predicate: str = SHARP_NULL.key
    value: Fraction = Fraction(0)

    @property
    def statement(self) -> str:
        return SHARP_NULL.statement


@dataclass(frozen=True)
class PlanIR:
    model: StudyModelIR
    stopping: Choice["fixed", "data_dependent"]


@dataclass(frozen=True)
class HypothesisIR(NullIR):
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
class AnalysisIR(TwoArmTestIR, LevelTestIR):
    plan: PlanIR
    hypothesis: HypothesisIR
    alpha: Fraction
    alternative: str = "two_sided"

    @property
    def contract(self) -> HypothesisContract:
        return {
            "two_sided": FISHER_CONTRACT,
            "greater": ONE_SIDED_FISHER_CONTRACT,
            "margin": MARGIN_CONTRACT,
        }[self.alternative]

    def __post_init__(self):
        if not self.contract.accepts(self.plan, self.hypothesis):
            raise ValueError(
                "A Fisher analysis requires its design's equal-proportions null."
                if self.alternative == "two_sided"
                else "This analysis requires a null of the form p_treatment - p_control <= value."
            )

    def margin_test(self, target=None, observed=None, sizes=None) -> MarginTest:
        """The exact difference test, optionally with a planning target or observed counts."""
        model = self.plan.model
        n_control, n_treatment = sizes or (model.n_control, model.n_treatment)
        rates = (None, None, None, None)
        if target is not None:
            rates = (
                target.at.p_control,
                target.at.p_treatment,
                target.minimum,
                target.maximum_typeI,
            )
        return MarginTest(
            n_control, n_treatment, self.hypothesis.value, self.alpha, *rates, observed
        )

    def lower(self) -> Design:
        return Design(
            self.plan.model.n_control,
            self.plan.model.n_treatment,
            self.plan.stopping,
            self.alpha,
            self.alternative,
        )


@dataclass(frozen=True)
class CitedAnalysisIR(TwoArmTestIR, LevelTestIR):
    """An analysis whose guarantee is cited from the literature, not proved in Lean.

    Its power, when its method has a formula, is an approximate calculation only.
    """

    plan: PlanIR
    hypothesis: NullIR
    alpha: Fraction
    method: CitedMethod

    @property
    def guarantee(self) -> Guarantee:
        return self.method.guarantee(self.alpha, self.hypothesis.statement)

    @property
    def assumptions(self) -> tuple[Assumption, ...]:
        """The method's assumptions, the direction of benefit when the file leaves it out,
        and for a declared test, what it must do for the declared design."""
        vouched = (
            tuple(ACCOUNTS_FOR[feature] for feature in self.plan.model.features)
            if self.method.grade == "declared"
            else ()
        )
        return (*self.method.assumptions, *direction_assumptions(self.hypothesis), *vouched)


def direction_assumptions(null: "NullIR") -> tuple[Assumption, ...]:
    """A one-sided null takes a side. If the model does not declare it, it is assumed."""
    favours = NULL_FORMS[null.predicate][1].favours if null.predicate in NULL_FORMS else None
    if favours is None or null.model.better is not None:
        return ()
    return (HIGHER_IS_BETTER if favours == "higher" else LOWER_IS_BETTER,)


@dataclass(frozen=True)
class RandomisationAnalysisIR(LevelTestIR):
    """A randomisation test of the sharp null. Its level follows from the declared
    randomisation alone, and Lean proves it for every statistic fixed in advance."""

    plan: PlanIR
    hypothesis: SharpNullIR
    alpha: Fraction
    # Assignments drawn at random for a Monte Carlo p-value; None counts every one.
    draws: int | None = None

    @property
    def guarantee(self) -> Guarantee:
        return Guarantee(
            "type_I_error", "at_most", self.alpha, self.hypothesis.statement, "finite_sample"
        )

    def lower(self) -> RandomisationTest:
        model = self.plan.model
        unit, units, treated = model.assignment.randomised_units
        return RandomisationTest(
            units,
            treated,
            self.alpha,
            unit,
            OUTCOMES[model.outcome].constructor,
            model.n_control,
            model.n_treatment,
            model.assignment.randomisation,
            model.assignment.strata,
            model.assignment.block_size,
            self.draws,
        )


class FamilyLikeIR:
    """Several analyses under one familywise error bound."""


@dataclass(frozen=True)
class ComposedFamilyIR(FamilyLikeIR):
    """Several analyses combined under one error bound, by one of composition.MODES.

    The members' own bounds are assumed. A member may be a single analysis or
    another combination: a design with looks, a family, a sequence or a graph.
    """

    analyses: tuple[tuple[str, object], ...]
    alpha: Fraction
    mode: str = "family"
    # For a graph only: each test's starting share of the level, and for each test
    # the shares of its level passed to the others when it is rejected.
    weights: tuple[Fraction, ...] = ()
    transitions: tuple[tuple[Fraction, ...], ...] = ()

    def lower(self) -> Composition:
        return Composition(
            self.alpha,
            tuple(_component(name, analysis) for name, analysis in self.analyses),
            self.mode,
        )


@dataclass(frozen=True)
class SequentialIR(ComposedFamilyIR, LevelTestIR):
    """One question tested at several looks, with the error level split across them."""

    mode: str = "sequential"


def _component(name: str, analysis: LevelTestIR) -> Component:
    if isinstance(analysis, SequentialIR):
        # A design with interim looks counts as one test of its null at its overall level.
        inner = analysis.lower()
        return Component(
            name,
            analysis.alpha,
            inner.scope,
            "conditional",
            inner.rules.contract,
            inner.components[0].null,
        )
    if isinstance(analysis, ComposedFamilyIR):
        # A family, sequence or graph counts as one member with a familywise bound.
        inner = analysis.lower()
        rules = inner.rules
        basis = rules.contract + (f" version {rules.version}" if rules.grade == "cited" else "")
        return Component(
            name,
            analysis.alpha,
            inner.scope,
            rules.grade,
            basis,
            inner.guarantee.null,
            "familywise_error",
        )
    if isinstance(analysis, CitedAnalysisIR):
        method = analysis.method
        return Component(
            name,
            analysis.alpha,
            method.scope,
            method.grade,
            f"declared by the author: {method.title}"
            if method.grade == "declared"
            else f"{method.module}/{method.key} version {method.version}",
            analysis.hypothesis.statement,
        )
    return Component(
        name,
        analysis.alpha,
        "finite_sample",
        "proved",
        EXACT_CONTRACT_IDS[analysis.alternative],
        analysis.hypothesis.statement,
    )


# The contract behind each exact two-arm analysis, by its alternative.
EXACT_CONTRACT_IDS = {
    "two_sided": "tests.fisher/fisher",
    "greater": "tests.fisher/fisher_one_sided",
    "margin": "tests.difference/difference_test",
}


@dataclass(frozen=True)
class FamilyIR(FamilyLikeIR):
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
class MeanDifferenceIR(PlanningPointIR):
    """A true mean difference, treatment minus control, and one participant's SD."""

    value: Fraction
    sd: Fraction


@dataclass(frozen=True)
class HazardRatioIR(PlanningPointIR):
    """A true hazard ratio, treatment over control, and the expected number of events."""

    value: Fraction
    events: int


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
class OneSampleObservationIR:
    analysis: OneSampleAnalysisIR
    responses: int

    def lower(self) -> OneSampleResult:
        analysis = self.analysis
        return OneSampleResult(analysis.model.n, analysis.null_rate, analysis.alpha, self.responses)


@dataclass(frozen=True)
class IntervalIR:
    model: OneArmModelIR
    responses: int
    level: Fraction

    def lower(self) -> BinomialInterval:
        return BinomialInterval(self.model.n, self.responses, self.level)


@dataclass(frozen=True)
class TwoStageObservationIR:
    analysis: TwoStageAnalysisIR
    stage1_responses: int
    stage2_responses: int | None

    def lower(self) -> TwoStageResult:
        analysis = self.analysis
        return TwoStageResult(
            analysis.design.n_stage1,
            analysis.design.n_stage2,
            analysis.rule.rule,
            analysis.null_rate,
            self.stage1_responses,
            self.stage2_responses,
        )


@dataclass(frozen=True)
class DifferenceIntervalIR:
    model: ModelIR
    control_successes: int
    treatment_successes: int
    level: Fraction

    def lower(self) -> DifferenceInterval:
        return DifferenceInterval(
            self.model.n_control,
            self.model.n_treatment,
            self.control_successes,
            self.treatment_successes,
            self.level,
        )


@dataclass(frozen=True)
class FeasibilityIR:
    """One analysis assessed against one target."""

    analysis: PlannableIR
    target: PowerTargetIR

    def lower(self) -> PowerPlan | TwoStagePlan | OneSamplePlan | MarginTest:
        target = self.target
        if isinstance(self.analysis, AnalysisIR) and self.analysis.alternative == "margin":
            return self.analysis.margin_test(target)
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

    analysis: "AnalysisIR | CitedAnalysisIR"
    min_per_arm: int
    max_per_arm: int
    ratio: int = 1


@dataclass(frozen=True)
class OneArmCandidatesIR(CandidateSpaceIR):
    """Sample sizes for a one-sample test, keeping its null rate and alpha."""

    analysis: OneSampleAnalysisIR
    min_n: int
    max_n: int


@dataclass(frozen=True)
class TwoStageCandidatesIR(CandidateSpaceIR):
    """Count-threshold two-stage designs up to a maximum total sample size."""

    null_rate: Fraction
    max_total: int
    criterion: str

    @property
    def analysis(self) -> TwoStageAnalysisIR:
        """The shared shape of every candidate; sizes and thresholds are searched."""
        return TwoStageAnalysisIR(
            TwoStageModelIR(1, 1), RuleIR(TwoStageRule("threshold")), self.null_rate
        )


@dataclass(frozen=True)
class SizingIR:
    candidates: CandidateSpaceIR
    target: PowerTargetIR
    minimal: bool = False


@dataclass(frozen=True)
class ClaimIR:
    kind: Choice["typeI", "familywise", "result", "meets", "sample_size", "interval"]
    subject: object
    name: str

    @property
    def guarantee(self) -> Guarantee | None:
        """The error-rate statement this claim asks for, when it is a single bound."""
        subject = self.subject
        if isinstance(subject, (CitedAnalysisIR, RandomisationAnalysisIR)):
            return subject.guarantee
        if isinstance(subject, ComposedFamilyIR):
            return subject.lower().guarantee
        if self.kind == "typeI" and isinstance(subject, AnalysisIR):
            return Guarantee(
                "type_I_error",
                "at_most",
                subject.alpha,
                subject.hypothesis.statement,
                "finite_sample",
            )
        if self.kind == "familywise":
            return Guarantee(
                "familywise_error",
                "at_most",
                subject.alpha,
                "any subset of the member nulls is true",
                "finite_sample",
            )
        return None

    @property
    def scope(self) -> str:
        """finite_sample or asymptotic. Every Lean-backed claim is a finite-sample one."""
        return self.guarantee.scope if self.guarantee else "finite_sample"


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
                TwoArmTestIR: "Analysis",
                LevelTestIR: "Analysis",
                NullIR: "Hypothesis",
                FamilyLikeIR: "Family",
                SequentialIR: "Sequential",
                StudyModelIR: "Model",
                CandidateSpaceIR: "Candidates",
                PlanningPointIR: "PlanningPoint",
                TwoStageAnalysisIR: "TwoStageAnalysis",
                TwoStageCandidatesIR: "TwoStageCandidates",
                TwoStageObservationIR: "TwoStageObservation",
                OneSampleAnalysisIR: "OneSampleAnalysis",
                OneArmModelIR: "OneArmModel",
                DifferenceIntervalIR: "DifferenceInterval",
                OneSampleObservationIR: "OneSampleObservation",
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
        case TwoArmModelIR(assignment=assignment, measured=measured):
            # Only what a file declared beyond the arm sizes is written, so a model keeps
            # the same record however it is spelled and whatever was added later.
            return {
                "module": OUTCOMES[measured.kind].constructor,
                **normalize(assignment),
                **{key: value for key, value in normalize(measured).items() if key != "outcome"},
            }
        case AssignmentIR(n_control=nc, n_treatment=nt, clusters_control=cc):
            result = {"n_control": nc, "n_treatment": nt}
            if cc is not None:
                result.update(clusters_control=cc, clusters_treatment=value.clusters_treatment)
            if value.randomisation is not None:
                result["randomisation"] = value.randomisation
            if value.strata:
                result["strata"] = [list(stratum) for stratum in value.strata]
            if value.block_size is not None:
                result["block_size"] = value.block_size
            return result
        case StratumIR(control=control, treatment=treatment):
            return {"control": control, "treatment": treatment}
        case OutcomeIR(kind=kind, better=better, measurements=measurements):
            return {
                "outcome": kind,
                **({"better": better} if better else {}),
                **({"measurements": measurements} if measurements > 1 else {}),
            }
        case OutcomeNullIR(model=model, predicate=predicate, value=bound):
            result = {"predicate": predicate, "model": normalize(model)}
            if NULL_FORMS[predicate][1].takes_value:
                result["value"] = str(bound)
            return result
        case SharpNullIR(model=model, predicate=predicate):
            return {"predicate": predicate, "model": normalize(model)}
        case RandomisationAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha, draws=draws):
            result = {
                "test": "randomisation",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
            if draws is not None:
                result["draws"] = draws
            return result
        case CitedAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha, method=method):
            result = {
                "test": method.key,
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
            if method.grade == "declared":
                # A declared test is described by the file, not by the registry.
                result.update(
                    method=method.title, scope=method.scope, references=list(method.references)
                )
            return result
        case PlanIR(model=model, stopping=stopping):
            return {"model": normalize(model), "stopping": stopping}
        case HypothesisIR(model=model, predicate=predicate, value=bound):
            result = {"predicate": predicate, "model": normalize(model)}
            if predicate != "equal_proportions":
                result["value"] = str(bound)
            return result
        case AnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha, alternative=alternative):
            result = {
                "test": "fisher",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
            if alternative != "two_sided":
                result["alternative"] = alternative
            return result
        case ComposedFamilyIR(
            analyses=analyses, alpha=alpha, mode=mode, weights=weights, transitions=transitions
        ):
            result = {
                "method": MODES[mode].method,
                "composition": "conditional",
                "alpha": str(alpha),
                "analyses": [
                    {"name": name, "analysis": normalize(analysis)} for name, analysis in analyses
                ],
            }
            if mode == "graphical":
                result["weights"] = [str(weight) for weight in weights]
                result["transitions"] = [[str(share) for share in row] for row in transitions]
            return result
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
        case MeanDifferenceIR(value=difference, sd=sd):
            return {"mean_difference": str(difference), "sd": str(sd)}
        case HazardRatioIR(value=ratio, events=events):
            return {"hazard_ratio": str(ratio), "events": events}
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
        case TwoStageObservationIR(
            analysis=analysis, stage1_responses=first, stage2_responses=second
        ):
            return {
                "analysis": normalize(analysis),
                "stage1_responses": first,
                "stage2_responses": second,
            }
        case OneSampleObservationIR(analysis=analysis, responses=responses):
            return {"analysis": normalize(analysis), "responses": responses}
        case DifferenceIntervalIR(
            model=model, control_successes=control, treatment_successes=treatment, level=level
        ):
            return {
                "model": normalize(model),
                "control_successes": control,
                "treatment_successes": treatment,
                "level": str(level),
            }
        case IntervalIR(model=model, responses=responses, level=level):
            return {"model": normalize(model), "responses": responses, "level": str(level)}
        case TwoStageCandidatesIR(null_rate=rate, max_total=total, criterion=criterion):
            return {
                "design": "two_stage_threshold",
                "null_rate": str(rate),
                "max_total": total,
                "criterion": criterion,
            }
        case OneArmCandidatesIR(analysis=analysis, min_n=low, max_n=high):
            return {"analysis": normalize(analysis), "min_n": low, "max_n": high}
        case FeasibilityIR(analysis=analysis, target=target):
            return {"analysis": normalize(analysis), "target": normalize(target)}
        case CandidatesIR(analysis=analysis, min_per_arm=low, max_per_arm=high, ratio=ratio):
            return {
                "analysis": normalize(analysis),
                "allocation": "equal_arms" if ratio == 1 else f"1:{ratio}",
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


def fail(code: str, message: str, span: Span) -> None:
    raise LanguageError(Diagnostic(code, message, span))


def _declare_randomisation(
    assignment: AssignmentIR, arguments: dict[str, LocatedValue], span: Span
) -> AssignmentIR:
    """Add the declared randomisation scheme, strata and block size, checked to fit."""
    scheme, strata, block = (
        arguments.get(name) for name in ("randomisation", "strata", "block_size")
    )
    named = scheme is not None and scheme.value is not None
    detail = next(
        (item for item in (strata, block) if item is not None and item.value is not None), None
    )
    if not named:
        if detail is not None:
            fail(
                "domain",
                "strata and block_size describe how the assignment was randomised; declare "
                'randomisation="stratified" or "blocked" with them.',
                detail.span,
            )
        return assignment
    if scheme.value not in SCHEMES:
        fail(
            "domain",
            'randomisation must be "complete", "stratified" or "blocked": every split, within '
            "each stratum or block where declared, was equally likely. Minimisation and other "
            "schemes are not supported yet; leave randomisation out for them.",
            scheme.span,
        )
    layers = []
    for item in (strata.value or ()) if strata is not None else ():
        if not isinstance(item.value, StratumIR):
            fail("type", "Each stratum must be stratum(control=..., treatment=...).", item.span)
        layers.append((item.value.control, item.value.treatment))
    size = block.value if block is not None else None
    declared = replace(
        assignment, randomisation=scheme.value, strata=tuple(layers), block_size=size
    )
    try:
        groups_of(*declared.randomised_units[1:], scheme.value, tuple(layers), size)
    except ValueError as error:
        fail("domain", str(error), (detail or scheme).span)
    return declared


def _arm_sizes(arguments: dict[str, LocatedValue]) -> AssignmentIR:
    for name in ("n_control", "n_treatment"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be a positive integer.", arguments[name].span)
    return AssignmentIR(arguments["n_control"].value, arguments["n_treatment"].value)


def _assignment(arguments: dict[str, LocatedValue], span: Span) -> AssignmentIR:
    return _declare_randomisation(_arm_sizes(arguments), arguments, span)


def _stratum(arguments: dict[str, LocatedValue], span: Span) -> StratumIR:
    for name in ("control", "treatment"):
        if arguments[name].value < 0:
            fail("domain", f"{name} must be a whole number, zero or more.", arguments[name].span)
    if arguments["control"].value + arguments["treatment"].value == 0:
        fail("domain", "A stratum needs at least one unit.", span)
    return StratumIR(arguments["control"].value, arguments["treatment"].value)


def _cluster_assignment(arguments: dict[str, LocatedValue], span: Span) -> AssignmentIR:
    sizes = _arm_sizes(arguments)
    for arm in ("control", "treatment"):
        clusters, size = arguments[f"clusters_{arm}"], arguments[f"n_{arm}"].value
        if not 1 <= clusters.value <= size:
            fail(
                "domain",
                f"clusters_{arm} must be a positive integer no larger than n_{arm} ({size}).",
                clusters.span,
            )
    clustered = AssignmentIR(
        sizes.n_control,
        sizes.n_treatment,
        arguments["clusters_control"].value,
        arguments["clusters_treatment"].value,
    )
    return _declare_randomisation(clustered, arguments, span)


def _outcome_piece(kind: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> OutcomeIR:
        better = arguments["better"]
        if better.value not in (None, "higher", "lower"):
            fail("domain", 'better must be "higher" or "lower".', better.span)
        measurements = arguments.get("measurements")
        count = 1 if measurements is None or measurements.value is None else measurements.value
        if count < 1:
            fail("domain", "measurements must be a positive integer.", measurements.span)
        return OutcomeIR(kind, better.value, count)

    return build


# Lean-backed two-arm analyses rest on independent binomial arms (methods/identify.py).
BINOMIAL_ASSUMPTIONS = ("independent_binomial_arms",)
PLAIN_ASSUMPTIONS = {
    "independent_observations": "independent observations",
    "independent_participants": "independent participants",
    "independent_binomial_arms": "two independent binomial samples, one value per participant",
}


def _fitting(model) -> list[str]:
    """Registered tests for the model's outcome whose unit fits the assignment and whose
    assumptions no declared feature contradicts."""
    unit = "cluster" if model.assignment.clustered else "participant"
    contradicted = {a for feature in model.features for a in CONTRADICTED_BY[feature]}
    return [
        m.key
        for m in methods_for(model.outcome)
        if m.unit == unit and not {a.id for a in m.assumptions} & contradicted
    ]


def _design_remedy(feature: str, model) -> str:
    fitting = _fitting(model)
    if feature == "clusters":
        cited = (
            f"Use {', '.join(fitting)}, which takes one summary per cluster with the clusters "
            "as the sample size; or "
            if fitting
            else "Use "
        )
        return (
            f'{cited}randomisation_test, with randomisation="complete" declared on the '
            "assignment, whose level Lean proves. For another analysis that accounts for "
            "clustering, such as a mixed model with a random effect for cluster, use "
            "declared_test(...)."
        )
    kind = "that fits this design" if model.assignment.clustered else "for repeated measurements"
    tests = f"a test {kind} ({', '.join(fitting)})" if fitting else None
    summary = (
        "declare one value per participant, such as the final visit or the mean, as an "
        "outcome with one measurement"
    )
    return f"Use {tests}, or {summary}." if tests else f"{summary.capitalize()}."


def check_design(model, assumptions: tuple[str, ...], test: str, span: Span) -> None:
    """Refuse a test whose assumptions the declared design contradicts."""
    for feature in getattr(model, "features", ()):
        contradicted = [a for a in assumptions if a in CONTRADICTED_BY[feature]]
        if not contradicted:
            continue
        assumed = PLAIN_ASSUMPTIONS.get(contradicted[0], contradicted[0])
        if feature == "clusters":
            design = (
                f"the assignment randomises whole clusters ({model.assignment.clusters_control} "
                f"control and {model.assignment.clusters_treatment} treatment clusters), and "
                "participants in one cluster tend to be alike"
            )
        else:
            design = (
                f"the outcome is measured {model.measured.measurements} times on each "
                "participant, and measurements on one participant are correlated"
            )
        fail(
            "unit_mismatch",
            f"{test} assumes {assumed}, but {design}. The test would overstate the evidence. "
            f"{_design_remedy(feature, model)}",
            span,
        )


def _model_from_sizes(kind: str) -> Callable:
    """The one-call spelling: the same assignment and outcome as two_arm(...)."""

    def build(arguments: dict[str, LocatedValue], span: Span) -> TwoArmModelIR:
        return two_arm_model(_assignment(arguments, span), _outcome_piece(kind)(arguments, span))

    return build


def _two_arm(arguments: dict[str, LocatedValue], span: Span) -> TwoArmModelIR:
    return two_arm_model(arguments["assignment"].value, arguments["outcome"].value)


def _check_direction(form, model, span: Span) -> None:
    """A one-sided null must favour the treatment in the direction the model calls better."""
    if form.favours is None or model.better is None or form.favours == model.better:
        return
    outcome = OUTCOMES[model.outcome]
    mirror = next((f for f in outcome.nulls if f.favours == model.better), None)
    remedy = (
        f"Use {mirror.key}(...) to ask whether the treatment's outcome is {model.better}."
        if mirror
        else "No null for this outcome asks the other way. State the complementary outcome "
        "instead, such as alive rather than dead, for which higher is better."
    )
    fail(
        "direction_mismatch",
        f"{form.key} asks whether the treatment's outcome is {form.favours}, but the model "
        f'declares better="{model.better}". {remedy}',
        span,
    )


def _outcome_null(outcome, form) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> OutcomeNullIR:
        model = arguments["model"]
        if model.value.outcome != outcome.key:
            fail(
                "type",
                f"{form.key} is a null for a {outcome.key} outcome; this model's outcome is "
                f"{model.value.outcome}.",
                model.span,
            )
        _check_direction(form, model.value, span)
        value = arguments["value"].value if form.takes_value else Fraction(0)
        return OutcomeNullIR(model.value, form.key, value)

    return build


def _cited_test(method: CitedMethod) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> CitedAnalysisIR:
        design, alpha = arguments["design"], arguments["alpha"]
        model = design.value.model
        if getattr(model, "outcome", None) != method.outcome:
            fail(
                "type",
                f"{method.key} is a test for a {method.outcome} outcome; this design's "
                "model is of another kind.",
                design.span,
            )
        if method.unit == "cluster" and not model.assignment.clustered:
            fail(
                "unit_mismatch",
                f"{method.key} takes one summary per cluster, with the clusters as the sample "
                "size, but the assignment randomises participants one by one. Declare "
                "cluster_assignment(...) if whole clusters were randomised; otherwise use a "
                "test of participants, such as t_test.",
                design.span,
            )
        sizes = (
            (model.assignment.clusters_control, model.assignment.clusters_treatment)
            if method.unit == "cluster"
            else (model.n_control, model.n_treatment)
        )
        if min(sizes) < method.min_per_arm or sum(sizes) < method.min_total:
            counted = "clusters " if method.unit == "cluster" else ""
            fail(
                "domain",
                f"{method.key} needs at least {method.min_per_arm} {counted}per arm and "
                f"{method.min_total} in total to estimate the variance"
                + (f"; this design randomises {sizes[0]} and {sizes[1]}." if counted else "."),
                design.span,
            )
        if not 0 < alpha.value < 1:
            fail("domain", "alpha must lie strictly between 0 and 1 for this test.", alpha.span)
        check_design(model, tuple(a.id for a in method.assumptions), method.key, design.span)
        return CitedAnalysisIR(design.value, arguments["null"].value, alpha.value, method)

    return build


def _declared_test(arguments: dict[str, LocatedValue], span: Span) -> CitedAnalysisIR:
    """A test the author names and vouches for. Nothing about it is checked or cited."""
    design, null, alpha = arguments["design"], arguments["null"], arguments["alpha"]
    HypothesisContract((null.value.predicate,), null.value.statement, "").check(
        "declared_test", arguments
    )
    if not 0 < alpha.value < 1:
        fail("domain", "alpha must lie strictly between 0 and 1 for this test.", alpha.span)
    title = arguments["method"]
    if not title.value.strip() or "\n" in title.value or len(title.value) > 200:
        fail("domain", "method must be one line of at most 200 characters.", title.span)
    scope = arguments["scope"]
    if scope.value is not None and scope.value not in SCOPES:
        fail("domain", f"scope must be one of: {', '.join(SCOPES)}.", scope.span)
    reference = arguments["reference"]
    if reference.value is not None and (not reference.value.strip() or "\n" in reference.value):
        fail("domain", "reference must be one non-empty line.", reference.span)
    method = CitedMethod(
        key="declared_test",
        module="tests.declared",
        title=title.value.strip(),
        version=1,
        outcome=design.value.model.outcome,
        null=null.value.predicate,
        relation="at_most",
        # Without a stated scope, nothing exact is claimed.
        scope=scope.value or "asymptotic",
        assumptions=(DECLARED_VALID,),
        references=(reference.value.strip(),) if reference.value else (),
        min_per_arm=1,
        min_total=2,
        grade="declared",
    )
    return CitedAnalysisIR(design.value, null.value, alpha.value, method)


def _no_effect(arguments: dict[str, LocatedValue], span: Span) -> SharpNullIR:
    model = arguments["model"]
    if not isinstance(model.value, TwoArmModelIR):
        fail("type", "no_effect is a null for a two-arm model.", model.span)
    return SharpNullIR(model.value)


def _randomisation_test(arguments: dict[str, LocatedValue], span: Span) -> RandomisationAnalysisIR:
    design, alpha = arguments["design"], arguments["alpha"]
    assignment = design.value.model.assignment
    unit, units, treated = assignment.randomised_units
    if assignment.randomisation is None:
        constructor = "cluster_assignment" if assignment.clustered else "assignment"
        fail(
            "undeclared_randomisation",
            "randomisation_test needs the assignment to say how it was randomised: its level "
            "follows from the randomisation alone. If every split of the "
            f"{units} {unit}s into arms of these sizes was equally likely, declare "
            f'randomisation="complete" in {constructor}(...); for strata or blocks, declare '
            'randomisation="stratified" with strata=[...] or "blocked" with block_size=...',
            design.span,
        )
    if units > MAX_UNITS:
        fail(
            "domain",
            f"randomisation_test supports up to {MAX_UNITS} randomised units; this design has "
            f"{units}.",
            design.span,
        )
    if alpha.value == 0:
        fail("domain", "alpha must be positive for this test.", alpha.span)
    drawn = arguments.get("draws")
    draws = drawn.value if drawn is not None else None
    if draws is not None:
        if not 1 <= draws <= MAX_DRAWS:
            fail("domain", f"draws must be a whole number from 1 to {MAX_DRAWS}.", drawn.span)
        if Fraction(1, draws + 1) > alpha.value:
            fail(
                "never_rejects",
                f"With {draws} drawn assignments, no Monte Carlo p-value is below "
                f"1/{draws + 1}, which is above the level {alpha.value}. The test can never "
                f"reject. Draw at least {splits_needed(alpha.value) - 1}.",
                drawn.span,
            )
        return RandomisationAnalysisIR(design.value, arguments["null"].value, alpha.value, draws)
    splits = count_splits(assignment.groups)
    if Fraction(1, splits) > alpha.value:
        grouped = assignment.randomisation != "complete"
        layout = f", in {len(assignment.groups)} strata or blocks" if grouped else ""
        fail(
            "never_rejects",
            f"With {units} {unit}s, {treated} treated{layout}, there are {splits} equally likely "
            f"splits, so no p-value is below 1/{splits}, which is above the level "
            f"{alpha.value}. The test can never reject. It needs at least "
            f"{splits_needed(alpha.value)} splits: randomise more {unit}s, use fewer strata or "
            "larger blocks, or use a larger level.",
            design.span,
        )
    return RandomisationAnalysisIR(design.value, arguments["null"].value, alpha.value)


def _fisher(alternative: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> AnalysisIR:
        plan, hypothesis = arguments["design"].value, arguments["null"].value
        test = "fisher" if alternative == "two_sided" else "fisher_one_sided"
        check_design(plan.model, BINOMIAL_ASSUMPTIONS, test, arguments["design"].span)
        return AnalysisIR(plan, hypothesis, arguments["alpha"].value, alternative)

    return build


def _difference(predicate: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> HypothesisIR:
        bound = arguments["value"]
        if not -1 <= bound.value <= 1:
            fail("domain", "A proportion-difference value must lie in [-1, 1].", bound.span)
        _check_direction(NULL_FORMS[predicate][1], arguments["model"].value, span)
        # This alias is backed by proportionDifference_zero_iff in the Lean model.
        canonical = (
            "equal_proportions"
            if predicate == "proportion_difference" and bound.value == 0
            else predicate
        )
        return HypothesisIR(arguments["model"].value, canonical, bound.value)

    return build


def _difference_test(arguments: dict[str, LocatedValue], span: Span) -> AnalysisIR:
    plan, null, alpha = arguments["design"].value, arguments["null"], arguments["alpha"]
    if not -1 < null.value.value < 1:
        fail("domain", "The margin must lie strictly between -1 and 1.", null.span)
    if alpha.value == 0:
        fail("domain", "alpha must be positive for this test.", alpha.span)
    check_design(plan.model, BINOMIAL_ASSUMPTIONS, "difference_test", arguments["design"].span)
    if max(plan.model.n_control, plan.model.n_treatment) > MAX_MARGIN_ARM:
        fail(
            "domain",
            f"The exact difference test currently supports up to {MAX_MARGIN_ARM} per arm; "
            "larger designs take too long to verify.",
            arguments["design"].span,
        )
    return AnalysisIR(plan, null.value, alpha.value, "margin")


def _members(
    argument: LocatedValue, what: str, *, combinations: bool = True
) -> list[tuple[str, object]]:
    """Named, distinct analyses for a family, a sequence, a graph or a design's looks.

    With combinations=True an entry may also be a whole design with looks, a
    family, a sequence or a graph.
    """
    items = argument.value
    allowed = (
        (AnalysisIR, CitedAnalysisIR, ComposedFamilyIR, FamilyIR)
        if combinations
        else (AnalysisIR, CitedAnalysisIR)
    )
    if not 2 <= len(items) <= MAX_ENDPOINTS:
        fail("family_size", f"This needs between 2 and {MAX_ENDPOINTS} {what}.", argument.span)
    members = []
    for item in items:
        if not isinstance(item.value, allowed) or item.name is None:
            fail(
                "type",
                "Each entry must be a named analysis: an exact two-arm test"
                + (
                    ", a cited test, or a named design, family, sequence or graph."
                    if combinations
                    else " or a cited test."
                ),
                item.span,
            )
        value = item.value
        if isinstance(value, FamilyIR):
            # As a member, a proved Fisher family is one more combination of assumed parts.
            value = ComposedFamilyIR(value.analyses, value.alpha)
        members.append((item.name, value))
    if len({name for name, _ in members}) != len(members):
        fail("duplicate_analysis", "The entries must have distinct names.", argument.span)
    # A name labels one outcome or one look. Two names for one declaration would
    # count it twice while reporting two.
    if len({id(item.value) for item in items}) != len(members):
        fail(
            "duplicate_analysis",
            "Two entries are the same declaration under different names. "
            "Declare each analysis separately; its name is its label.",
            argument.span,
        )
    return members


def _family(arguments: dict[str, LocatedValue], span: Span) -> FamilyLikeIR:
    analyses = _members(arguments["analyses"], "analyses")
    law = arguments["joint_law"]
    proved = all(
        isinstance(analysis, AnalysisIR) and analysis.alternative == "two_sided"
        for _, analysis in analyses
    )
    if not proved:
        # The union bound needs no joint law, so there is nothing to declare.
        if law.value is not None:
            fail(
                "sampling_contract",
                "Leave joint_law out unless every member is a two-sided Fisher analysis. "
                "The combination holds for any dependence between members.",
                law.span,
            )
        return ComposedFamilyIR(tuple(analyses), arguments["alpha"].value)
    if law.value not in (None, "binomial_marginals"):
        fail(
            "sampling_contract",
            'The supported joint contract is "binomial_marginals"; '
            "dependence between outcomes is unrestricted.",
            law.span,
        )
    return FamilyIR(tuple(analyses), arguments["alpha"].value, "binomial_marginals")


def _test_key(analysis: LevelTestIR) -> str:
    if isinstance(analysis, CitedAnalysisIR):
        return analysis.method.key
    return EXACT_CONTRACT_IDS[analysis.alternative].split("/")[1]


def _sequential(arguments: dict[str, LocatedValue], span: Span) -> SequentialIR:
    looks = _members(arguments["looks"], "looks", combinations=False)
    first = looks[0][1]
    previous = None
    for name, look in looks:
        null, model = look.hypothesis, look.plan.model
        same = (
            _test_key(look) == _test_key(first)
            and type(model) is type(first.plan.model)
            and getattr(model, "outcome", None) == getattr(first.plan.model, "outcome", None)
            and (null.predicate, null.value) == (first.hypothesis.predicate, first.hypothesis.value)
        )
        if not same:
            fail(
                "sequential_question",
                f"{name}: every look must use the same test and the same null as the first "
                "look. Different questions belong in a bonferroni family.",
                arguments["looks"].span,
            )
        sizes = (model.n_control, model.n_treatment)
        if previous is not None and not (
            sizes[0] >= previous[0] and sizes[1] >= previous[1] and sum(sizes) > sum(previous)
        ):
            fail(
                "sequential_order",
                f"{name}: list the looks in order. Each look's model gives the cumulative "
                "arm sizes at that look, so they must grow.",
                arguments["looks"].span,
            )
        previous = sizes
    return SequentialIR(tuple(looks), arguments["alpha"].value)


def _fixed_sequence(arguments: dict[str, LocatedValue], span: Span) -> ComposedFamilyIR:
    analyses = _members(arguments["analyses"], "analyses")
    alpha = arguments["alpha"]
    for name, analysis in analyses:
        if analysis.alpha != alpha.value:
            fail(
                "sequence_level",
                f"{name} has alpha {analysis.alpha}, but every test in a fixed sequence uses "
                f"the full level {alpha.value}. The order, not a split of the level, controls "
                "the error. To split the level, use bonferroni.",
                arguments["analyses"].span,
            )
    return ComposedFamilyIR(tuple(analyses), alpha.value, "fixed_sequence")


def _share(item: LocatedValue, what: str) -> Fraction:
    value = Fraction(item.value) if type(item.value) is int else item.value
    if not isinstance(value, Fraction) or not 0 <= value <= 1:
        fail("graph_definition", f"Each {what} must be an exact number from 0 to 1.", item.span)
    return value


def _graphical(arguments: dict[str, LocatedValue], span: Span) -> ComposedFamilyIR:
    analyses = _members(arguments["analyses"], "analyses", combinations=False)
    alpha, count = arguments["alpha"], len(analyses)
    for name, analysis in analyses:
        if analysis.alpha != alpha.value:
            fail(
                "sequence_level",
                f"{name} has alpha {analysis.alpha}. In a graph, declare every test at the "
                f"overall level {alpha.value}; the weights say what share each starts with.",
                arguments["analyses"].span,
            )
    weights = arguments["weights"]
    if not isinstance(weights.value, tuple) or len(weights.value) != count:
        fail(
            "graph_definition",
            f"weights needs one number for each of the {count} tests.",
            weights.span,
        )
    shares = tuple(_share(item, "weight") for item in weights.value)
    if sum(shares) > 1:
        fail("graph_definition", f"The weights sum to {sum(shares)}, more than 1.", weights.span)
    table = arguments["transitions"]
    rows = table.value
    if len(rows) != count or any(
        not isinstance(row.value, tuple) or len(row.value) != count for row in rows
    ):
        fail(
            "graph_definition",
            f"transitions needs {count} rows of {count} numbers: row i says how test i's "
            "level is shared out when it is rejected.",
            table.span,
        )
    passed = tuple(tuple(_share(item, "transition") for item in row.value) for row in rows)
    for index, row in enumerate(passed):
        if row[index] != 0:
            fail("graph_definition", "A test cannot pass its level to itself.", rows[index].span)
        if sum(row) > 1:
            fail(
                "graph_definition",
                f"Row {index + 1} of transitions sums to {sum(row)}, more than 1.",
                rows[index].span,
            )
    return ComposedFamilyIR(tuple(analyses), alpha.value, "graphical", shares, passed)


def _familywise(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    family = arguments["family"]
    if isinstance(family.value, SequentialIR):
        fail(
            "type",
            "A sequential design tests one null, so ask for typeI(...) instead of familywise.",
            family.span,
        )
    return ClaimIR("familywise", family.value, family.name or "<expression>")


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
    if claim.value.kind not in ("result", "meets", "sample_size", "interval"):
        fail(
            "type",
            "Only results, intervals and planning claims are numerical calculations. "
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


def _mean_difference(arguments: dict[str, LocatedValue], span: Span) -> MeanDifferenceIR:
    sd = arguments["sd"]
    if sd.value <= 0:
        fail("domain", "sd must be positive.", sd.span)
    return MeanDifferenceIR(arguments["value"].value, sd.value)


def _hazard_ratio(arguments: dict[str, LocatedValue], span: Span) -> HazardRatioIR:
    ratio, events = arguments["value"], arguments["events"]
    if ratio.value <= 0:
        fail("domain", "A hazard ratio must be positive.", ratio.span)
    if events.value < 1:
        fail("domain", "events must be a positive integer.", events.span)
    return HazardRatioIR(ratio.value, events.value)


def _power_target(arguments: dict[str, LocatedValue], span: Span) -> PowerTargetIR:
    return PowerTargetIR(
        arguments["at"].value,
        _probability(arguments["minimum"], "minimum", positive=True),
        arguments["maximum_typeI"].value,
    )


# How to write the planning point each kind of power formula takes.
POINT_SIGNATURES = {
    "mean_difference": (MeanDifferenceIR, "mean_difference(value=..., sd=...)"),
    "binomial_rates": (RatesIR, "binomial_rates(p_control=..., p_treatment=...)"),
    "hazard_ratio": (HazardRatioIR, "hazard_ratio(value=..., events=...)"),
}


def _check_cited_point(analysis: CitedAnalysisIR, target: LocatedValue, where: Span) -> None:
    """A cited test can be planned only with a power formula, at that formula's kind of point."""
    method, point = analysis.method, target.value.at
    if method.power is None:
        others = ", ".join(m.key for m in methods_for(method.outcome) if m.power) or "none"
        fail(
            "no_power_formula",
            f"{method.key} has no power formula, so its power cannot be calculated. Tests "
            f"for this outcome with one: {others}.",
            where,
        )
    kind, signature = POINT_SIGNATURES[method.power.point]
    if not isinstance(point, kind):
        fail("planning_point", f"Plan {method.key} at {signature}.", target.span)
    model = analysis.plan.model
    if isinstance(point, HazardRatioIR) and point.events > model.n_control + model.n_treatment:
        fail(
            "planning_point",
            f"events cannot exceed the {model.n_control + model.n_treatment} participants "
            "in the design.",
            target.span,
        )
    null = analysis.hypothesis
    if isinstance(point, MeanDifferenceIR):
        effect = point.value
    elif isinstance(point, RatesIR):
        effect = point.p_treatment - point.p_control
    else:
        effect = point.value - 1  # a hazard ratio of 1 is no effect
    favours = NULL_FORMS[null.predicate][1].favours
    outside = {
        "higher": effect > null.value,
        "lower": effect < null.value,
        None: effect != 0,
    }[favours]
    if not outside:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({null.statement}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _check_point(analysis: PlannableIR, target: LocatedValue, where: Span) -> None:
    """The planning point must belong to the analysis's parameter space, outside its null."""
    point = target.value.at
    if isinstance(analysis, CitedAnalysisIR):
        _check_cited_point(analysis, target, where)
        return
    if isinstance(analysis, (TwoStageAnalysisIR, OneSampleAnalysisIR)):
        if not isinstance(point, RateIR):
            fail(
                "planning_point",
                "A single-arm analysis has one response rate. "
                "Declare the target at response_rate(value=...).",
                target.span,
            )
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
        if analysis.alternative == "margin":
            margin = analysis.hypothesis.value
            null = f"p_treatment - p_control <= {margin}"
            outside = point.p_treatment - point.p_control > margin
        elif analysis.alternative == "greater":
            null, outside = "p_treatment <= p_control", point.p_treatment > point.p_control
        else:
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
    _check_point(analysis.value, arguments["target"], analysis.span)
    return ClaimIR(
        "meets",
        FeasibilityIR(analysis.value, arguments["target"].value),
        analysis.name or "<expression>",
    )


def _arm_limit(analysis: TwoArmTestIR) -> int:
    """The largest arm a search may reach: exact tests are slower to evaluate."""
    if isinstance(analysis, CitedAnalysisIR):
        return MAX_CITED_ARM
    return MAX_MARGIN_ARM if analysis.alternative == "margin" else MAX_PER_ARM


def _candidates(arguments: dict[str, LocatedValue], span: Span) -> CandidatesIR:
    low, high = arguments["min_per_arm"], arguments["max_per_arm"]
    if low.value < 1:
        fail("domain", "min_per_arm must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_per_arm must be at least min_per_arm.", high.span)
    limit = _arm_limit(arguments["analysis"].value)
    if high.value > limit:
        fail("domain", f"max_per_arm is currently limited to {limit} for this analysis.", high.span)
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


def _responses(arguments: dict[str, LocatedValue], span: Span) -> OneSampleObservationIR:
    analysis, count = arguments["analysis"].value, arguments["count"]
    if not 0 <= count.value <= analysis.model.n:
        fail("domain", f"count must be between 0 and {analysis.model.n}.", count.span)
    return OneSampleObservationIR(analysis, count.value)


def _interval(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    model, count, level = arguments["model"], arguments["count"], arguments["level"]
    if not 0 <= count.value <= model.value.n:
        fail("domain", f"count must be between 0 and {model.value.n}.", count.span)
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    return ClaimIR(
        "interval",
        IntervalIR(model.value, count.value, level.value),
        model.name or "<expression>",
    )


def _difference_interval(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    model, level = arguments["model"], arguments["level"]
    check_design(model.value, BINOMIAL_ASSUMPTIONS, "difference_interval", model.span)
    for name, size in (
        ("control_successes", model.value.n_control),
        ("treatment_successes", model.value.n_treatment),
    ):
        if not 0 <= arguments[name].value <= size:
            fail("domain", f"{name} must be between 0 and {size}.", arguments[name].span)
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    interval = DifferenceIntervalIR(
        model.value,
        arguments["control_successes"].value,
        arguments["treatment_successes"].value,
        level.value,
    )
    try:
        interval.lower()
    except ValueError as error:
        fail("domain", str(error), level.span)
    return ClaimIR("interval", interval, model.name or "<expression>")


def _one_arm_candidates(arguments: dict[str, LocatedValue], span: Span) -> OneArmCandidatesIR:
    low, high = arguments["min_n"], arguments["max_n"]
    if low.value < 1:
        fail("domain", "min_n must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_n must be at least min_n.", high.span)
    if high.value > MAX_ONE_ARM:
        fail("domain", f"max_n is currently limited to {MAX_ONE_ARM}.", high.span)
    return OneArmCandidatesIR(arguments["analysis"].value, low.value, high.value)


def _allocated(arguments: dict[str, LocatedValue], span: Span) -> CandidatesIR:
    low, high = arguments["min_control"], arguments["max_control"]
    ratio = arguments["treatment_per_control"]
    if not 1 <= ratio.value <= MAX_RATIO:
        fail("domain", f"treatment_per_control must be between 1 and {MAX_RATIO}.", ratio.span)
    if low.value < 1:
        fail("domain", "min_control must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_control must be at least min_control.", high.span)
    limit = _arm_limit(arguments["analysis"].value)
    if high.value * ratio.value > limit:
        fail(
            "domain",
            f"The larger arm is currently limited to {limit} participants for this analysis.",
            high.span,
        )
    return CandidatesIR(arguments["analysis"].value, low.value, high.value, ratio.value)


def _sizing(minimal: bool) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        candidates = arguments["candidates"]
        if (
            minimal
            and isinstance(candidates.value, CandidatesIR)
            and isinstance(candidates.value.analysis, AnalysisIR)
            and candidates.value.analysis.alternative == "margin"
        ):
            fail(
                "unsupported_claim",
                "Each sample size has its own critical value for this test, so a "
                "smallest-size claim is not supported. Use sample_size(...) to certify a "
                "sufficient design.",
                candidates.span,
            )
        if minimal and isinstance(candidates.value, TwoStageCandidatesIR):
            fail(
                "unsupported_claim",
                "A two-stage search ranks designs by its criterion; that ranking is a "
                "calculation and is not certified. Use sample_size(...) to certify the "
                "selected design's error and power.",
                candidates.span,
            )
        _check_point(candidates.value.analysis, arguments["target"], candidates.span)
        if isinstance(arguments["target"].value.at, HazardRatioIR):
            fail(
                "unsupported_claim",
                "Log-rank power depends on the number of events, not on the arm sizes, so a "
                "search over arm sizes does not apply. Calculate meets(...) for a number "
                "of events instead.",
                arguments["target"].span,
            )
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


def _two_stage_candidates(arguments: dict[str, LocatedValue], span: Span) -> TwoStageCandidatesIR:
    rate, total, criterion = arguments["null_rate"], arguments["max_total"], arguments["criterion"]
    if not 0 < rate.value < 1:
        fail("domain", "null_rate must lie strictly between 0 and 1.", rate.span)
    if not 2 <= total.value <= MAX_SEARCH_TOTAL:
        fail("domain", f"max_total must be between 2 and {MAX_SEARCH_TOTAL}.", total.span)
    if criterion.value not in CRITERIA:
        fail("domain", 'criterion must be "optimal" or "minimax".', criterion.span)
    return TwoStageCandidatesIR(rate.value, total.value, criterion.value)


def _stage_data(completed: bool) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> TwoStageObservationIR:
        analysis, first = arguments["analysis"].value, arguments["stage1_responses"]
        second = arguments["stage2_responses"] if completed else None
        for argument, size in (
            (first, analysis.design.n_stage1),
            (second, analysis.design.n_stage2),
        ):
            if argument is not None and not 0 <= argument.value <= size:
                fail("domain", f"Responses must be between 0 and {size}.", argument.span)
        observation = TwoStageObservationIR(
            analysis, first.value, second.value if completed else None
        )
        try:
            observation.lower()
        except ValueError as error:
            # The data must be what the declared rule would have produced.
            fail("rule_mismatch", str(error), first.span)
        return observation

    return build


def _two_stage_test(arguments: dict[str, LocatedValue], span: Span) -> TwoStageAnalysisIR:
    return TwoStageAnalysisIR(
        arguments["design"].value,
        arguments["rule"].value,
        _probability(arguments["null_rate"], "null_rate"),
    )


def planned_analysis(subject: object) -> object:
    """The analysis a planning claim is about."""
    if isinstance(subject, FeasibilityIR):
        return subject.analysis
    return subject.candidates.analysis


def _verification(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    claim = arguments["claim"]
    if claim.value.kind in ("meets", "sample_size") and isinstance(
        planned_analysis(claim.value.subject), CitedAnalysisIR
    ):
        fail(
            "unsupported_claim",
            "The power of a cited test is a normal approximation, with no proof or cited "
            "theorem behind it, so it cannot be verified. Use calculate(...) instead.",
            claim.span,
        )
    return claim.value


# Always available, with the same argument checking as module constructors.
# Their builders validate claims only; evaluate records execution slots below.
OPERATIONS = {
    "verify": _constructor("verify", (("claim", ClaimIR),), "VerificationResult", _verification),
    "calculate": _constructor(
        "calculate", (("claim", ClaimIR),), "CalculationResult", _calculation
    ),
}


FAMILYWISE = _constructor("familywise", (("family", FamilyLikeIR),), "FamilywiseClaim", _familywise)
# One constructor shared by every module whose analyses carry a Type I claim.
TYPE_I = _constructor(
    "typeI", (("analysis", LevelTestIR),), "TypeIClaim", _claim("typeI", "analysis")
)


def _cited_contract(method: CitedMethod) -> HypothesisContract:
    """Built from the registry, so the guidance always lists the current alternatives."""
    value = "value" if method.null_value is None else method.null_value
    statements = " or ".join(
        NULL_FORMS[null][1].statement.format(value=value) for null in method.nulls
    )
    others = "; ".join(
        f"{other.key} takes {' or '.join(other.nulls)}" for other in methods_for(method.outcome)
    )
    fixed = "" if method.null_value is None else f", with value {method.null_value}"
    return HypothesisContract(
        method.nulls,
        statements,
        f"{method.title} supports the null {' or '.join(method.nulls)}{fixed}. Keep your null "
        f"if it states your question, and choose the test that supports it. For this "
        f"outcome: {others}.",
        required_value=method.null_value,
        version=method.version,
    )


def _cited_constructor(method: CitedMethod) -> Constructor:
    contract = _cited_contract(method)
    return _constructor(
        method.key,
        (("design", PlanIR), ("null", NullIR), ("alpha", "level")),
        "CitedAnalysis",
        _cited_test(method),
        hypothesis_contract=contract,
        documentation=f"{method.title}. Its guarantee is cited from the literature and is "
        f"not checked by Lean. Null: {contract.expected}.",
    )


BETTER_DOCUMENTATION = (
    'better is "higher" or "lower": which direction of the outcome is better. When given, '
    "a one-sided null must ask whether the treatment is better in that direction. When "
    "left out, a one-sided null's direction is listed as an assumption."
)

DECLARED_MODULE_SUMMARY = (
    "A test the author names and vouches for, for analyses StatClaim has no contract for. "
    "Only its fit to the design is checked: the null and the design must describe the same "
    "model. Its result has the status 'declared', the weakest, and any plan that contains it "
    "reports that status."
)


RANDOMISATION_DOCUMENTATION = (
    'randomisation is "complete" when every split of the units into arms of these sizes was '
    'equally likely; "stratified" with strata=[stratum(...), ...] when that holds within each '
    'stratum; "blocked" with block_size=... (and optional strata) when it holds within each '
    "block of that size. Strata and blocks count randomised units. Leave it out otherwise; "
    "only randomisation_test reads it, and it refuses an assignment without it."
)
RANDOMISATION_PARAMETERS = (
    ("randomisation", "string", True),
    ("strata", "list", True),
    ("block_size", "integer", True),
)
# Shared by every two-arm model module, so a file that loads several gets one copy.
ASSIGNMENT = _constructor(
    "assignment",
    (("n_control", "integer"), ("n_treatment", "integer"), *RANDOMISATION_PARAMETERS),
    "Assignment",
    _assignment,
    documentation="How participants are assigned to the two arms: the two arm sizes and, "
    "when declared, how the assignment was randomised. One assignment can be shared by "
    f"several outcomes measured on the same participants. {RANDOMISATION_DOCUMENTATION}",
)
CLUSTER_ASSIGNMENT = _constructor(
    "cluster_assignment",
    (
        ("clusters_control", "integer"),
        ("clusters_treatment", "integer"),
        ("n_control", "integer"),
        ("n_treatment", "integer"),
        *RANDOMISATION_PARAMETERS,
    ),
    "Assignment",
    _cluster_assignment,
    documentation="Whole clusters, such as clinics or schools, are assigned to the arms, and "
    "everyone in a cluster gets the same arm. clusters_control and clusters_treatment count "
    "the clusters; n_control and n_treatment count the participants. Sites in a trial that "
    "randomises participants are not clusters: use assignment(...) there. Tests that assume "
    "independent participants are refused. With randomisation, the units are the clusters. "
    + RANDOMISATION_DOCUMENTATION,
)
STRATUM = _constructor(
    "stratum",
    (("control", "integer"), ("treatment", "integer")),
    "Stratum",
    _stratum,
    documentation="One stratum of a stratified or blocked assignment: how many randomised "
    "units, participants or clusters, it has in each arm.",
)
NO_EFFECT = _constructor(
    "no_effect",
    (("model", StudyModelIR),),
    "SharpNull",
    _no_effect,
    documentation=SHARP_NULL.documentation,
)
TWO_ARM = _constructor(
    "two_arm",
    (("assignment", AssignmentIR), ("outcome", OutcomeIR)),
    "Model",
    _two_arm,
    documentation="A two-arm model from an assignment and an outcome. A binary outcome "
    "gives the binomial model; any other outcome gives an OutcomeModel. The same pieces "
    "give the same model as the one-call constructors, such as two_arm_continuous.",
)


def outcome_constructor_name(kind: str) -> str:
    return f"{kind}_outcome"


MEASUREMENTS_DOCUMENTATION = (
    "measurements is how many times the outcome is measured on each participant, 1 if left "
    "out. With more than one, tests that take one value per participant are refused."
)


def _outcome_piece_constructor(outcome) -> Constructor:
    repeated = (("measurements", "integer", True),) if outcome.repeatable else ()
    return _constructor(
        outcome_constructor_name(outcome.key),
        (("better", "string", True), *repeated),
        "Outcome",
        _outcome_piece(outcome.key),
        documentation=f"The {outcome.key} outcome measured on each participant. Combine "
        f"it with an assignment in two_arm(...). {BETTER_DOCUMENTATION}"
        + (f" {MEASUREMENTS_DOCUMENTATION}" if outcome.repeatable else ""),
    )


def _shorthand_note(outcome) -> str:
    return (
        f"Shorthand for two_arm(assignment=assignment(n_control, n_treatment), "
        f"outcome={outcome_constructor_name(outcome.key)}(better))."
    )


def _outcome_module(outcome) -> "Module":
    nulls = tuple(
        _constructor(
            form.key,
            (("model", OutcomeModelIR), *((("value", "number"),) if form.takes_value else ())),
            "OutcomeNull",
            _outcome_null(outcome, form),
            documentation=form.documentation,
        )
        for form in outcome.nulls
    )
    model = _constructor(
        outcome.constructor,
        (("n_control", "integer"), ("n_treatment", "integer"), ("better", "string", True)),
        "OutcomeModel",
        _model_from_sizes(outcome.key),
        documentation=f"{outcome.documentation} The model fixes no distribution; each test "
        f"states the one it assumes. {_shorthand_note(outcome)} {BETTER_DOCUMENTATION}",
    )
    pieces = (
        ASSIGNMENT,
        CLUSTER_ASSIGNMENT,
        STRATUM,
        _outcome_piece_constructor(outcome),
        TWO_ARM,
    )
    return Module(outcome.module, (model, *pieces, *nulls, NO_EFFECT, TYPE_I))


# Extending this registry adds vocabulary and typed builders; parsing is unchanged.
MODULES = {
    module.name: module
    for module in (
        *(_outcome_module(outcome) for outcome in OUTCOMES.values() if not outcome.builtin),
        Module(
            "tests.declared",
            (
                _constructor(
                    "declared_test",
                    (
                        ("design", PlanIR),
                        ("null", NullIR),
                        ("alpha", "level"),
                        ("method", "string"),
                        ("scope", "string", True),
                        ("reference", "string", True),
                    ),
                    "CitedAnalysis",
                    _declared_test,
                    documentation="A test you name and vouch for, when StatClaim has no "
                    "contract for the analysis. method says what the test is. scope is "
                    "finite_sample or asymptotic, and asymptotic if left out. reference is "
                    "where the test is specified. Nothing about its guarantee is checked.",
                ),
            ),
        ),
        *(
            Module(group.name, tuple(_cited_constructor(method) for method in group.methods))
            for group in METHOD_MODULES
        ),
        Module(
            "models.two_arm_binomial",
            (
                _constructor(
                    "two_arm_binomial",
                    (
                        ("n_control", "integer"),
                        ("n_treatment", "integer"),
                        ("better", "string", True),
                    ),
                    "Model",
                    _model_from_sizes("binary"),
                    documentation="Two independent binomial arms. "
                    + _shorthand_note(OUTCOMES["binary"])
                    + " "
                    + BETTER_DOCUMENTATION,
                ),
                ASSIGNMENT,
                CLUSTER_ASSIGNMENT,
                STRATUM,
                _outcome_piece_constructor(OUTCOMES["binary"]),
                TWO_ARM,
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
                NO_EFFECT,
                TYPE_I,
                _constructor(
                    "result",
                    (("observation", ObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                ),
            ),
        ),
        Module(
            "sampling",
            (
                _constructor(
                    "fixed",
                    (("model", StudyModelIR),),
                    "StudyDesign",
                    lambda args, span: PlanIR(args["model"].value, "fixed"),
                ),
                _constructor(
                    "adaptive",
                    (("model", StudyModelIR),),
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
                    _fisher("two_sided"),
                    hypothesis_contract=FISHER_CONTRACT,
                    documentation=FISHER_CONTRACT.guidance,
                ),
                _constructor(
                    "fisher_one_sided",
                    (("design", PlanIR), ("null", HypothesisIR), ("alpha", "level")),
                    "Analysis",
                    _fisher("greater"),
                    hypothesis_contract=ONE_SIDED_FISHER_CONTRACT,
                    documentation=ONE_SIDED_FISHER_CONTRACT.guidance,
                ),
            ),
        ),
        Module(
            "tests.randomisation",
            (
                _constructor(
                    "randomisation_test",
                    (
                        ("design", PlanIR),
                        ("null", NullIR),
                        ("alpha", "level"),
                        ("draws", "integer", True),
                    ),
                    "RandomisationAnalysis",
                    _randomisation_test,
                    hypothesis_contract=RANDOMISATION_CONTRACT,
                    documentation="Randomisation test of the sharp null. Its level follows "
                    "from the randomisation declared on the assignment, and Lean proves it "
                    "for every test statistic fixed in advance; no distribution is assumed. "
                    "With cluster_assignment the clusters are randomised, so the test "
                    "permutes clusters. Without draws the p-value counts every possible "
                    "assignment; with draws=B it compares the observed assignment with B "
                    "drawn at random, which Lean also proves. " + RANDOMISATION_CONTRACT.guidance,
                ),
                TYPE_I,
            ),
        ),
        Module(
            "tests.difference",
            (
                _constructor(
                    "difference_test",
                    (("design", PlanIR), ("null", HypothesisIR), ("alpha", "level")),
                    "Analysis",
                    _difference_test,
                    hypothesis_contract=MARGIN_CONTRACT,
                    documentation=MARGIN_CONTRACT.guidance,
                ),
            ),
        ),
        Module(
            "multiplicity.bonferroni",
            (
                _constructor(
                    "bonferroni",
                    (("analyses", "list"), ("alpha", "level"), ("joint_law", "string", True)),
                    "Family",
                    _family,
                    documentation="Bonferroni: the members' levels may sum to at most alpha. "
                    "Members may be exact tests, cited tests, designs with interim looks, "
                    "sequences, graphs or other families; dependence between them is "
                    "unrestricted. "
                    "A family of two-sided Fisher analyses is proved "
                    "outright. Any other family is conditional: Lean checks the combination "
                    "and each member's own bound is assumed.",
                ),
                FAMILYWISE,
            ),
        ),
        Module(
            "multiplicity.graphical",
            (
                _constructor(
                    "graphical",
                    (
                        ("analyses", "list"),
                        ("weights", "list"),
                        ("transitions", "list"),
                        ("alpha", "level"),
                    ),
                    "ComposedFamily",
                    _graphical,
                    documentation="A graphical procedure with recycling. weights gives each "
                    "test's starting share of alpha. Row i of transitions says how test i's "
                    "level is shared among the others when it is rejected. Declare every test "
                    "at the overall alpha. The procedure's guarantee is cited, not checked by "
                    "Lean; the contract checks that the weights and transitions are valid.",
                ),
                FAMILYWISE,
            ),
        ),
        Module(
            "multiplicity.fixed_sequence",
            (
                _constructor(
                    "fixed_sequence",
                    (("analyses", "list"), ("alpha", "level")),
                    "ComposedFamily",
                    _fixed_sequence,
                    documentation="Hierarchical testing: the analyses are tested in the listed "
                    "order, each at the full level alpha, and a test is carried out only if "
                    "every earlier one rejected. An entry may be a test, a design with interim "
                    "looks, or a family, sequence or graph; such an entry must be rejected in "
                    "full before the next is tested. Lean checks the combination; each "
                    "entry's own bound is assumed.",
                ),
                FAMILYWISE,
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
                    "mean_difference",
                    (("value", "number"), ("sd", "number")),
                    "MeanDifference",
                    _mean_difference,
                    documentation="A planning point for a continuous outcome: the true mean "
                    "difference, treatment minus control, and the standard deviation of one "
                    "participant's outcome on the analysed scale. For a mixed model, sd is the "
                    "effective standard deviation of the contrast. Both are planning inputs.",
                ),
                _constructor(
                    "hazard_ratio",
                    (("value", "number"), ("events", "integer")),
                    "HazardRatio",
                    _hazard_ratio,
                    documentation="A planning point for a survival outcome: the true hazard "
                    "ratio, treatment over control, and the expected total number of events. "
                    "Power depends on the events, not on the arm sizes. Both are planning inputs.",
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
                    "target. calculate computes the components; verify must establish all. "
                    "For a cited test, calculate gives approximate power and verify is refused.",
                ),
                _constructor(
                    "equal_arm_sizes",
                    (
                        ("analysis", TwoArmTestIR),
                        ("min_per_arm", "integer"),
                        ("max_per_arm", "integer"),
                    ),
                    "Candidates",
                    _candidates,
                    documentation="A finite design space: equal arm sizes within inclusive "
                    "bounds, keeping the analysis's sampling, null form, test and alpha.",
                ),
                _constructor(
                    "allocated_arm_sizes",
                    (
                        ("analysis", TwoArmTestIR),
                        ("min_control", "integer"),
                        ("max_control", "integer"),
                        ("treatment_per_control", "integer"),
                    ),
                    "Candidates",
                    _allocated,
                    documentation="A finite design space with unequal allocation: each "
                    "candidate has n controls and treatment_per_control * n treated "
                    "participants, for n within the inclusive bounds.",
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
            "designs.group_sequential",
            (
                _constructor(
                    "alpha_spending",
                    (("looks", "list"), ("alpha", "level")),
                    "Sequential",
                    _sequential,
                    documentation="One test repeated at several looks, stopping at the first "
                    "rejection. Give each look as an analysis whose model has the cumulative "
                    "arm sizes at that look, with the level spent there. The levels may sum "
                    "to at most alpha. Lean checks the combination; each look's own bound is "
                    "assumed. The split is conservative.",
                ),
                TYPE_I,
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
                    "stopped_at_interim",
                    (("analysis", TwoStageAnalysisIR), ("stage1_responses", "integer")),
                    "TwoStageObservation",
                    _stage_data(False),
                    documentation="Observed data when the interim rule stopped the study. "
                    "Rejected if the declared rule would have continued.",
                ),
                _constructor(
                    "completed_stages",
                    (
                        ("analysis", TwoStageAnalysisIR),
                        ("stage1_responses", "integer"),
                        ("stage2_responses", "integer"),
                    ),
                    "TwoStageObservation",
                    _stage_data(True),
                    documentation="Observed data from both stages. Rejected if the declared "
                    "rule would have stopped after stage one.",
                ),
                _constructor(
                    "two_stage_result",
                    (("observation", TwoStageObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                    documentation="Claim about the decision the declared design reaches for "
                    "the observed counts, with the design's error bound.",
                ),
                _constructor(
                    "two_stage_designs",
                    (("null_rate", "number"), ("max_total", "integer"), ("criterion", "string")),
                    "TwoStageCandidates",
                    _two_stage_candidates,
                    documentation="Count-threshold two-stage designs with total size up to "
                    'max_total. criterion="optimal" minimises the expected sample size at the '
                    'null rate; "minimax" minimises the maximum sample size. The selected '
                    "design is certified; the ranking is a calculation.",
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
            "estimation",
            (
                _constructor(
                    "difference_interval",
                    (
                        ("model", ModelIR),
                        ("control_successes", "integer"),
                        ("treatment_successes", "integer"),
                        ("level", "number"),
                    ),
                    "IntervalClaim",
                    _difference_interval,
                    documentation="Confidence interval for p_treatment - p_control, built "
                    "from an exact interval for each arm. It is valid for every pair of true "
                    "rates and is wider than intervals built for the difference directly, so "
                    "it can include zero when a test rejects.",
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
                _constructor(
                    "confidence_interval",
                    (("model", OneArmModelIR), ("count", "integer"), ("level", "number")),
                    "IntervalClaim",
                    _interval,
                    documentation="Exact (Clopper-Pearson) confidence interval for the response "
                    "rate. Endpoints are rounded outward to four decimals, so coverage is at "
                    "least the stated level for every true rate.",
                ),
                _constructor(
                    "responses",
                    (("analysis", OneSampleAnalysisIR), ("count", "integer")),
                    "OneSampleObservation",
                    _responses,
                    documentation="The observed number of responses for this analysis.",
                ),
                _constructor(
                    "binomial_result",
                    (("observation", OneSampleObservationIR),),
                    "ResultClaim",
                    _claim("result", "observation"),
                    documentation="Claim about the exact p-value and decision for the "
                    "observed count, with the test's Type I bound.",
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
