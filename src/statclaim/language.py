"""Typed statistical objects and module-driven elaboration of .stat files.

No Python or Lean source in a user file is executed. Module builders lower the
supported objects to the same validated requests as the TOML and Lean routes.
"""

import json
from collections.abc import Callable, Iterator
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Literal as Choice

from statclaim.association import (
    CELLS,
    MAX_PARTICIPANTS,
    MEASURES,
    NAME,
    AssociationResult,
    AssociationTable,
    AssociationTest,
    EffectInterval,
    not_estimable,
    null_statement,
    table_problem,
)
from statclaim.composition import MODES, Component, Composition
from statclaim.design import Design
from statclaim.family import MAX_ENDPOINTS, Endpoint, FisherFamily
from statclaim.fisher import validate_alpha
from statclaim.incidence import (
    MAX_EVENTS,
    PROPORTIONS,
    ObservedEvents,
    ProportionEstimate,
    RateRatioInterval,
    RateResult,
    RateTest,
    proportion_not_estimable,
)
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
from statclaim.matched import (
    MAX_PAIRS,
    PAIR_CELLS,
    MatchedInterval,
    MatchedPairs,
    MatchedResult,
    MatchedTest,
    pairs_problem,
)
from statclaim.methods import METHOD_MODULES, NULL_FORMS, OUTCOMES, SHARP_NULL, methods_for
from statclaim.methods.assumptions import (
    ACCOUNTS_FOR,
    CONTRADICTED_BY,
    DECLARED_VALID,
    HIGHER_IS_BETTER,
    LOWER_IS_BETTER,
    POPULATION_COVERED,
    POPULATIONS,
)
from statclaim.methods.core import SCOPES, Assumption, CitedMethod, Guarantee
from statclaim.methods.observational import (
    CORRELATION,
    MAX_COVARIATES,
    REGRESSION,
    SCALES,
    SURVEY,
    SURVEYS,
    ObservationalMethod,
)
from statclaim.methods.observational import (
    METHODS as OBSERVATIONAL_METHODS,
)
from statclaim.observational_planning import (
    MAX_GROUP,
    MAX_PLANNED_PAIRS,
    MAX_TOTAL,
    AssociationPowerPlan,
    MatchedPowerPlan,
    RatePowerPlan,
    TotalPowerPlan,
)
from statclaim.observational_planning import SEARCH_KEYS as GROUP_SEARCH_KEYS
from statclaim.plan_kinds import kind_of, resolve
from statclaim.planning import (
    CRITERIA,
    MAX_CITED_ARM,
    MAX_CITED_TOTAL,
    MAX_CLUSTER_SIZE,
    MAX_CLUSTERS,
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
from statclaim.precision import MAX_EXACT_PAIRS
from statclaim.precision import MAX_SIZE as MAX_PRECISION_SIZE
from statclaim.precision import MEASURES as PLANNED_MEASURES
from statclaim.precision import METHODS as PRECISION_METHODS
from statclaim.randomisation import (
    MAX_DRAWS,
    MAX_UNITS,
    SCHEMES,
    RandomisationTest,
    count_splits,
    groups_of,
    splits_needed,
)
from statclaim.simulation import (
    DEFAULT_RUNS,
    MAX_RUNS,
    MAX_SIMULATED_PARTICIPANTS,
    MAX_SIMULATED_STUDIES,
    MAX_SKEWNESS,
    MIN_RUNS,
)

LANGUAGE_VERSION = "0.41.0"


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


class EstimableModelIR:
    """A model whose interval can be planned: one arm, two binomial arms, or an observational
    study."""


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
    # A key of POPULATIONS when declared: who is analysed. A randomisation test reads it,
    # and other tests' claims say which population their bound covers.
    population: str | None = None

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
    """What is measured on each participant: its kind, which direction is better, how many
    times it is measured, and its name when declared. One name is one outcome."""

    kind: str  # a key of OUTCOMES
    # "higher" or "lower": which direction of the outcome is better, when declared.
    better: str | None = None
    measurements: int = 1
    name: str | None = None


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
class ModelIR(TwoArmModelIR, EstimableModelIR):
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


def population_conditions(subject: object) -> tuple[Assumption, ...]:
    """Which population the bounds in a claim cover, for each population an assignment
    declares, with what that population adds to the assumptions. A randomisation test is
    left out: its own premises say who is analysed."""
    found: list[Assumption] = []

    def visit(item: object) -> None:
        if isinstance(item, RandomisationAnalysisIR):
            return
        if isinstance(item, (FeasibilityIR, SizingIR)):
            visit(planned_analysis(item))
        elif isinstance(item, ObservationIR):
            visit(item.analysis)
        elif isinstance(item, (ComposedFamilyIR, FamilyIR)):
            for _, analysis in item.analyses:
                visit(analysis)
        else:
            plan = getattr(item, "plan", None)
            model = plan.model if isinstance(plan, PlanIR) else getattr(item, "model", None)
            assignment = getattr(model, "assignment", None)
            population = getattr(assignment, "population", None)
            for condition in POPULATION_COVERED.get(population, ()):
                if condition not in found:
                    found.append(condition)

    visit(subject)
    return tuple(found)


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
            model.assignment.population,
        )


@dataclass(frozen=True)
class ObservationalStudyIR(StudyModelIR, EstimableModelIR):
    """An observational study: exposure was not assigned. Its design says what the
    sampling fixed, which decides what the study can estimate and how a test is justified.
    """

    exposure: str
    outcome: str
    # How each variable is measured, and how a survey sampled. Proved methods need binary
    # variables and simple random sampling; cited methods say what they take.
    exposure_scale: str = "binary"
    outcome_scale: str = "binary"
    survey: str = "simple_random"
    clusters: int | None = None

    observational = True
    design = ""

    @property
    def groups(self) -> tuple[int, int] | None:
        """The two group sizes the design fixes: (unexposed, exposed) or (controls, cases)."""
        return None

    @property
    def total(self) -> int:
        groups = self.groups
        return sum(groups) if groups is not None else self.n


@dataclass(frozen=True)
class CrossSectionalStudyIR(ObservationalStudyIR):
    """A sample of n from one population, with exposure and outcome measured at once.
    Only the total is fixed. It measures prevalence, not incidence."""

    n: int = 0
    design = "cross_sectional"


@dataclass(frozen=True)
class CohortStudyIR(ObservationalStudyIR):
    """Participants followed over time from exposure to outcome. The exposed and unexposed
    group sizes are fixed when sampled separately; otherwise only the total n is."""

    exposed: int | None = None
    unexposed: int | None = None
    n: int | None = None
    design = "cohort"

    @property
    def groups(self) -> tuple[int, int] | None:
        return None if self.exposed is None else (self.unexposed, self.exposed)


@dataclass(frozen=True)
class CaseControlStudyIR(ObservationalStudyIR):
    """Cases with the outcome and controls without it, sampled in fixed numbers, then asked
    about past exposure. It cannot estimate risk or prevalence: the design fixed how many
    have the outcome."""

    cases: int = 0
    controls: int = 0
    design = "case_control"

    @property
    def groups(self) -> tuple[int, int]:
        return (self.controls, self.cases)


@dataclass(frozen=True)
class MatchedStudyIR(ObservationalStudyIR):
    """A 1:1 matched case-control study: each case matched to one control on chosen
    characteristics. Only the pairs where exactly one was exposed carry information."""

    pairs: int = 0
    design = "matched_case_control"

    @property
    def n(self) -> int:
        return self.pairs


@dataclass(frozen=True)
class PersonTimeStudyIR(ObservationalStudyIR):
    """A cohort followed over person-time, counting events in the exposed and unexposed. It
    measures incidence rates; no group size is fixed."""

    design = "person_time_cohort"

    @property
    def n(self) -> None:
        return None


@dataclass(frozen=True)
class AssociationNullIR(NullIR):
    """No association between an observational study's exposure and outcome: an odds ratio
    of 1, stated in the terms the design can estimate."""

    model: ObservationalStudyIR
    predicate: str = "no_association"
    value: Fraction = Fraction(0)

    @property
    def statement(self) -> str:
        model = self.model
        if "continuous" in (model.exposure_scale, model.outcome_scale):
            return "exposure_coefficient = 0"
        return null_statement(model.design)


@dataclass(frozen=True)
class AssociationAnalysisIR(LevelTestIR, PlannableIR):
    """Fisher's exact test of no association in an observational 2x2 study. Lean proves its
    level for every design: with the group sizes fixed, or with only the total fixed. With
    the group sizes fixed, its exact power at a planning point is calculated and checked."""

    plan: PlanIR
    hypothesis: AssociationNullIR
    alpha: Fraction

    @property
    def guarantee(self) -> Guarantee:
        return Guarantee(
            "type_I_error", "at_most", self.alpha, self.hypothesis.statement, "finite_sample"
        )

    def lower(self) -> AssociationTest:
        model = self.plan.model
        groups = model.groups
        return AssociationTest(
            model.design,
            self.alpha,
            groups,
            None if groups is not None else model.n,
            model.exposure,
            model.outcome,
        )


@dataclass(frozen=True)
class CitedAssociationIR(LevelTestIR, PlannableIR):
    """A test of no association whose guarantee is cited, not proved: regression with
    covariates, correlation, or an analysis of a complex survey sample. Its power, when its
    method has a formula, is a calculation only."""

    plan: PlanIR
    hypothesis: AssociationNullIR
    alpha: Fraction
    method: ObservationalMethod
    covariates: tuple[str, ...] = ()

    @property
    def guarantee(self) -> Guarantee:
        return self.method.guarantee(self.alpha)

    @property
    def assumptions(self) -> tuple[Assumption, ...]:
        return self.method.assumptions


@dataclass(frozen=True)
class AssociationTableIR:
    """An observed 2x2 table of an observational study. Cases have the outcome."""

    model: ObservationalStudyIR
    exposed_cases: int
    exposed_noncases: int
    unexposed_cases: int
    unexposed_noncases: int

    @property
    def cells(self) -> tuple[int, int, int, int]:
        return (
            self.exposed_cases,
            self.exposed_noncases,
            self.unexposed_cases,
            self.unexposed_noncases,
        )

    def lower(self) -> AssociationTable:
        model = self.model
        return AssociationTable(
            model.design,
            self.cells,
            model.groups,
            None if model.groups is not None else model.n,
            model.exposure,
            model.outcome,
        )


@dataclass(frozen=True)
class AssociationResultIR:
    """Fisher's exact test applied to an observed table: its p-value and decision."""

    analysis: AssociationAnalysisIR
    table: AssociationTableIR

    def lower(self) -> AssociationResult:
        return AssociationResult(self.analysis.lower(), self.table.lower())


@dataclass(frozen=True)
class EffectIntervalIR:
    """An interval for an effect measure the design can estimate, from an observed table."""

    measure: str
    table: AssociationTableIR
    level: Fraction

    def lower(self) -> EffectInterval:
        return EffectInterval(self.measure, self.table.lower(), self.level)


@dataclass(frozen=True)
class MatchedAnalysisIR(LevelTestIR, PlannableIR):
    """McNemar's exact test of no association within matched pairs."""

    plan: PlanIR
    hypothesis: AssociationNullIR
    alpha: Fraction

    @property
    def guarantee(self) -> Guarantee:
        return Guarantee(
            "type_I_error", "at_most", self.alpha, self.hypothesis.statement, "finite_sample"
        )

    def lower(self) -> MatchedTest:
        model = self.plan.model
        return MatchedTest(model.pairs, self.alpha, model.exposure, model.outcome)


@dataclass(frozen=True)
class MatchedPairsIR:
    """Observed pairs of a matched study, classified by who was exposed."""

    model: MatchedStudyIR
    both_exposed: int
    case_exposed_only: int
    control_exposed_only: int
    neither_exposed: int

    @property
    def cells(self) -> tuple[int, int, int, int]:
        return (
            self.both_exposed,
            self.case_exposed_only,
            self.control_exposed_only,
            self.neither_exposed,
        )

    def lower(self) -> MatchedPairs:
        model = self.model
        return MatchedPairs(model.pairs, self.cells, model.exposure, model.outcome)


@dataclass(frozen=True)
class MatchedResultIR:
    """McNemar's exact test applied to observed pairs."""

    analysis: MatchedAnalysisIR
    observed: MatchedPairsIR

    def lower(self) -> MatchedResult:
        return MatchedResult(self.analysis.lower(), self.observed.lower())


@dataclass(frozen=True)
class MatchedIntervalIR:
    """An interval for the conditional odds ratio of a matched study."""

    observed: MatchedPairsIR
    level: Fraction

    def lower(self) -> MatchedInterval:
        return MatchedInterval(self.observed.lower(), self.level)


@dataclass(frozen=True)
class RateAnalysisIR(LevelTestIR, PlannableIR):
    """The conditional exact test of equal incidence rates, given the total events."""

    plan: PlanIR
    hypothesis: AssociationNullIR
    alpha: Fraction

    @property
    def guarantee(self) -> Guarantee:
        return Guarantee(
            "type_I_error", "at_most", self.alpha, self.hypothesis.statement, "finite_sample"
        )

    def lower(self) -> RateTest:
        model = self.plan.model
        return RateTest(self.alpha, model.exposure, model.outcome)


@dataclass(frozen=True)
class ObservedEventsIR:
    """Events and person-time in a person-time cohort's exposed and unexposed groups."""

    model: PersonTimeStudyIR
    exposed_events: int
    exposed_time: Fraction
    unexposed_events: int
    unexposed_time: Fraction

    def lower(self) -> ObservedEvents:
        return ObservedEvents(
            self.exposed_events,
            self.exposed_time,
            self.unexposed_events,
            self.unexposed_time,
            self.model.exposure,
            self.model.outcome,
        )


@dataclass(frozen=True)
class RateResultIR:
    """The conditional rate test applied to observed events."""

    analysis: RateAnalysisIR
    events: ObservedEventsIR

    def lower(self) -> RateResult:
        return RateResult(self.analysis.lower(), self.events.lower())


@dataclass(frozen=True)
class RateRatioIR:
    """An interval for the incidence rate ratio from observed events."""

    events: ObservedEventsIR
    level: Fraction

    def lower(self) -> RateRatioInterval:
        return RateRatioInterval(self.events.lower(), self.level)


@dataclass(frozen=True)
class ProportionIR:
    """Prevalence or cumulative incidence, with its exact interval."""

    measure: str
    model: ObservationalStudyIR
    cases: int
    level: Fraction
    group: str | None = None

    @property
    def size(self) -> int:
        groups = self.model.groups
        if groups is None:
            return self.model.n
        return groups[1] if self.group == "exposed" else groups[0]

    def lower(self) -> ProportionEstimate:
        return ProportionEstimate(
            self.measure,
            self.model.design,
            self.size,
            self.cases,
            self.level,
            self.model.exposure,
            self.model.outcome,
            self.group,
        )


class FamilyLikeIR(PlannableIR):
    """Several analyses under one familywise error bound. Its power, for a family of Fisher
    tests and t-tests, can be simulated at one point per member."""


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
class SequentialIR(ComposedFamilyIR, LevelTestIR, PlannableIR):
    """One question tested at several looks, with the error level split across them. Its
    power can be simulated when its test has a simulation model for looks."""

    mode: str = "sequential"

    @property
    def final(self):
        """The last look: the whole study."""
        return self.analyses[-1][1]


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
    if isinstance(analysis, RandomisationAnalysisIR):
        return Component(
            name,
            analysis.alpha,
            "finite_sample",
            "proved",
            "tests.randomisation/randomisation_test",
            analysis.hypothesis.statement,
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
    """One success probability per arm and, for a test of cluster proportions, the
    intracluster correlation."""

    p_control: Fraction
    p_treatment: Fraction
    icc: Fraction | None = None
    # How much cluster sizes vary, for simulating a cluster test: their coefficient of variation.
    cluster_size_cv: Fraction | None = None


@dataclass(frozen=True)
class RateIR(PlanningPointIR):
    value: Fraction


@dataclass(frozen=True)
class MeanDifferenceIR(PlanningPointIR):
    """A true mean difference, treatment minus control, one participant's SD and, for a test
    of cluster means, the intracluster correlation."""

    value: Fraction
    sd: Fraction
    icc: Fraction | None = None
    cluster_size_cv: Fraction | None = None
    # A scenario for simulating a two-sample t-test: the treatment arm's own SD (sd is then
    # the control arm's) and the skewness of the outcome.
    sd_treatment: Fraction | None = None
    skewness: Fraction | None = None


@dataclass(frozen=True)
class HazardRatioIR(PlanningPointIR):
    """A true hazard ratio, treatment over control, and the expected number of events."""

    value: Fraction
    events: int


@dataclass(frozen=True)
class ExponentialSurvivalIR(PlanningPointIR):
    """A planning point for a survival outcome given by its times: the hazard ratio, the
    control arm's median time to the event, the accrual period and the follow-up after it,
    and optionally the probability of dropping out by dropout_time. All times are in one
    unit, such as months."""

    hazard_ratio: Fraction
    control_median: Fraction
    accrual: Fraction
    follow_up: Fraction
    dropout: Fraction | None = None
    dropout_time: Fraction | None = None
    # For simulation: the treatment's hazard ratio applies only from this time after entry.
    effect_delay: Fraction | None = None


@dataclass(frozen=True)
class CorrelationIR(PlanningPointIR):
    """A planning point for two continuous variables: their correlation, and for simulation,
    the skewness of the exposure and of the outcome's error."""

    value: Fraction
    skewness: Fraction | None = None
    exposure_skewness: Fraction | None = None


@dataclass(frozen=True)
class OutcomeMeansIR(PlanningPointIR):
    """A planning point for a measured outcome by a yes-or-no exposure: the outcome's mean
    without and with the exposure, its standard deviation about them, the share exposed when
    only the total is fixed, and a survey's design effect."""

    unexposed: Fraction
    exposed: Fraction
    sd: Fraction
    exposed_share: Fraction | None = None
    design_effect: Fraction | None = None


@dataclass(frozen=True)
class OddsPerSdIR(PlanningPointIR):
    """A planning point for logistic regression on a measured exposure: the odds ratio per
    standard deviation of the exposure, the outcome's probability at the exposure's mean, and
    the share of the exposure's variance the covariates explain."""

    odds_ratio: Fraction
    baseline: Fraction
    exposure_r2: Fraction | None = None
    design_effect: Fraction | None = None


@dataclass(frozen=True)
class SlopeIR(PlanningPointIR):
    """A planning point for a linear regression: the exposure's slope, the exposure's and
    the residual standard deviations, and the share of the exposure's variance the
    covariates explain."""

    value: Fraction
    exposure_sd: Fraction
    residual_sd: Fraction
    exposure_r2: Fraction | None = None
    design_effect: Fraction | None = None
    skewness: Fraction | None = None  # of the residual, for simulation
    exposure_skewness: Fraction | None = None


@dataclass(frozen=True)
class RisksIR(PlanningPointIR):
    """A planning point for a cohort: the risk of the outcome without and with exposure, and
    for a cohort of one population, the share of participants exposed."""

    unexposed: Fraction
    exposed: Fraction
    exposed_share: Fraction | None = None


@dataclass(frozen=True)
class OutcomePrevalenceIR(PlanningPointIR):
    """A planning point for a cross-sectional study: the prevalence of the outcome without
    and with exposure, and the share of participants exposed."""

    unexposed: Fraction
    exposed: Fraction
    exposed_share: Fraction
    # For a survey test of a complex sample: the design effect, a planning input.
    design_effect: Fraction | None = None


@dataclass(frozen=True)
class ExposurePrevalenceIR(PlanningPointIR):
    """A planning point for a case-control study: the probability of having been exposed,
    among controls and among cases."""

    controls: Fraction
    cases: Fraction


@dataclass(frozen=True)
class DiscordantPairsIR(PlanningPointIR):
    """A planning point for a matched study: the probability that a pair is discordant, and
    the conditional odds ratio."""

    share: Fraction
    odds_ratio: Fraction


@dataclass(frozen=True)
class IncidenceRatesIR(PlanningPointIR):
    """A planning point for a person-time cohort: the rate ratio, the person-time in each
    group, and the total number of events power is calculated for."""

    rate_ratio: Fraction
    exposed_time: Fraction
    unexposed_time: Fraction
    events: int | None = None


def group_probabilities(point: PlanningPointIR) -> tuple[Fraction, Fraction]:
    """The planning point's probabilities in Fisher's first and second groups:
    (unexposed, exposed) for a cohort, (controls, cases) for a case-control study."""
    if isinstance(point, (RisksIR, OutcomePrevalenceIR)):
        return point.unexposed, point.exposed
    return point.controls, point.cases


class TargetIR:
    """What a planning claim asks of a design: power, or precision."""


@dataclass(frozen=True)
class PowerTargetIR(TargetIR):
    at: PlanningPointIR
    minimum: Fraction
    maximum_typeI: Fraction
    # Where the Type I error is judged by simulation, for a design whose level is not proved.
    nulls: "NullScenariosIR | None" = None
    # For a family: whether power means rejecting "any" endpoint or "all" of them.
    rejecting: str | None = None


@dataclass(frozen=True)
class EndpointPointsIR(PlanningPointIR):
    """A planning point for a family: one point per member, in order, and the exchangeable
    correlation between endpoints measured on the same participants."""

    points: tuple[PlanningPointIR, ...]
    correlation: Fraction


@dataclass(frozen=True)
class NullScenariosIR:
    """Points at the null at which a design's simulated Type I error is judged: for a design
    whose level is not proved, such as one that re-estimates its size."""

    points: tuple[PlanningPointIR, ...]


@dataclass(frozen=True)
class ReestimationIR(PlannableIR):
    """A two-arm Student t-test whose size per arm is re-estimated after interim_per_arm per
    arm, from the variance of all outcomes with the arms pooled (blinded). The new size gives
    power at the planned difference; it is never below the analysis's size per arm nor above
    max_per_arm. Its Type I error is not proved: it is judged by simulation at declared nulls."""

    analysis: "CitedAnalysisIR"
    interim_per_arm: int
    difference: Fraction
    power: Fraction
    max_per_arm: int

    @property
    def initial_per_arm(self) -> int:
        return self.analysis.plan.model.n_control


@dataclass(frozen=True)
class SingleProportionIR(PlanningPointIR):
    """A planning point for one proportion, such as a prevalence: its value, and for the
    normal interval of a survey, the design effect and the size of the population sampled."""

    value: Fraction
    design_effect: Fraction | None = None
    population_size: int | None = None


@dataclass(frozen=True)
class PrecisionTargetIR(TargetIR):
    """Require an interval's margin of error, half its width, to be at most margin, or its
    relative margin of error at most relative; with assurance, require that chance."""

    at: PlanningPointIR
    level: Fraction
    margin: Fraction | None = None
    relative: Fraction | None = None
    assurance: Fraction | None = None

    @property
    def bound(self) -> Fraction:
        return self.margin if self.margin is not None else self.relative


@dataclass(frozen=True)
class PlannedIntervalIR(PlannableIR):
    """An interval a study plans to report: its measure, its method, and for a cohort that
    sampled two groups, which group's proportion."""

    model: object
    measure: str
    method: str = "exact"
    group: str | None = None


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
class OneArmModelIR(EstimableModelIR):
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

    def lower(self) -> object:
        target = self.target
        if (
            isinstance(self.analysis, AssociationAnalysisIR)
            and self.analysis.plan.model.groups is None
        ):
            return TotalPowerPlan(
                self.analysis.lower(),
                *group_probabilities(target.at),
                target.at.exposed_share,
                target.minimum,
                target.maximum_typeI,
            )
        if isinstance(self.analysis, AssociationAnalysisIR):
            return AssociationPowerPlan(
                self.analysis.lower(),
                *group_probabilities(target.at),
                target.minimum,
                target.maximum_typeI,
            )
        if isinstance(self.analysis, MatchedAnalysisIR):
            point = target.at
            return MatchedPowerPlan(
                self.analysis.lower(),
                point.share,
                point.odds_ratio,
                target.minimum,
                target.maximum_typeI,
            )
        if isinstance(self.analysis, RateAnalysisIR):
            point = target.at
            return RatePowerPlan(
                self.analysis.lower(),
                point.exposed_time,
                point.unexposed_time,
                point.rate_ratio,
                point.events,
                target.minimum,
                target.maximum_typeI,
            )
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
class ClusterCandidatesIR(CandidateSpaceIR):
    """Cluster-randomised trials for a test of cluster summaries. With cluster_size set, low
    to high clusters per arm of that many participants each; without it, the declared
    clusters per arm with low to high participants in each cluster. Each keeps the
    analysis's null, test and alpha."""

    analysis: "CitedAnalysisIR"
    low: int
    high: int
    cluster_size: int | None = None

    @property
    def varies(self) -> str:
        return "clusters" if self.cluster_size is not None else "cluster_size"

    def designs(self):
        """Each candidate as (clusters per arm, participants per cluster), ascending."""
        model = self.analysis.plan.model
        for value in range(self.low, self.high + 1):
            if self.cluster_size is not None:
                yield (value, value), (self.cluster_size, self.cluster_size)
            else:
                assignment = model.assignment
                yield (assignment.clusters_control, assignment.clusters_treatment), (value, value)


@dataclass(frozen=True)
class GroupCandidatesIR(CandidateSpaceIR):
    """Designs of a cohort or case-control study for Fisher's test: from min_size to
    max_size exposed participants or cases, with ratio unexposed participants or controls
    for each. Each keeps the analysis's study, null and alpha."""

    analysis: AssociationAnalysisIR
    min_size: int
    max_size: int
    ratio: int = 1


@dataclass(frozen=True)
class TotalCandidatesIR(CandidateSpaceIR):
    """Cross-sectional studies, or cohorts of one population, of min_n to max_n participants.
    Each keeps the analysis's study, null and alpha."""

    analysis: AssociationAnalysisIR
    min_n: int
    max_n: int


@dataclass(frozen=True)
class CountCandidatesIR(CandidateSpaceIR):
    """Matched studies with min_size to max_size pairs, or totals of min_size to max_size
    events for the rate test. Each keeps the analysis's null and alpha."""

    analysis: "MatchedAnalysisIR | RateAnalysisIR"
    min_size: int
    max_size: int

    @property
    def unit(self) -> str:
        return "pairs" if isinstance(self.analysis.plan.model, MatchedStudyIR) else "events"


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
class IntervalCandidatesIR(CandidateSpaceIR):
    """Sizes for a planned interval, in the design's own units: participants, the first group
    (exposed, cases or controls in a trial) with ratio of the other for each, pairs or
    events."""

    interval: PlannedIntervalIR
    min_size: int
    max_size: int
    ratio: int = 1

    @property
    def analysis(self) -> PlannedIntervalIR:
        return self.interval


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
        if isinstance(
            subject,
            (
                CitedAnalysisIR,
                RandomisationAnalysisIR,
                AssociationAnalysisIR,
                MatchedAnalysisIR,
                RateAnalysisIR,
                CitedAssociationIR,
            ),
        ):
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
class SimulationIR:
    """How a simulate(...) request draws its studies: a seed and the number of runs."""

    seed: int
    runs: int


@dataclass(frozen=True)
class RequestIR:
    operation: Choice["verify", "calculate", "simulate"]
    claim: ClaimIR
    span: Span
    # Only for simulate(...): the seed and the number of simulated studies.
    settings: SimulationIR | None = None


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
                    **(
                        {"settings": {"seed": r.settings.seed, "runs": r.settings.runs}}
                        if r.settings
                        else {}
                    ),
                }
                for index, r in enumerate(self.requests, 1)
            ],
        }


def _study_extras(study: "ObservationalStudyIR") -> dict:
    """Scales and survey designs, recorded only when they differ from the defaults."""
    extras = {}
    if study.exposure_scale != "binary":
        extras["exposure_scale"] = study.exposure_scale
    if study.outcome_scale != "binary":
        extras["outcome_scale"] = study.outcome_scale
    if study.survey != "simple_random":
        extras["survey"] = study.survey
    if study.clusters is not None:
        extras["clusters"] = study.clusters
    return extras


def _with_cluster_cv(point: dict, value) -> dict:
    """How much cluster sizes vary, and a simulation's scenario, are written only when given."""
    for name in ("cluster_size_cv", "sd_treatment", "skewness", "exposure_skewness"):
        if getattr(value, name, None) is not None:
            point = {**point, name: str(getattr(value, name))}
    return point


def skewed(point) -> bool:
    """Whether a planning point describes skewed data, for simulation."""
    return any(getattr(point, name, None) for name in ("skewness", "exposure_skewness"))


def departs(point) -> bool:
    """Whether a planning point leaves normal data, with a common SD for two means."""
    sd_treatment = getattr(point, "sd_treatment", None)
    return skewed(point) or (sd_treatment is not None and sd_treatment != point.sd)


def participant_draws(point) -> bool:
    """Whether simulating at this point draws every participant, not summary statistics."""
    return isinstance(point, ExponentialSurvivalIR) or skewed(point)


def _check_skewed_point(analysis: object, target: LocatedValue) -> None:
    """Skewed data are simulated for the correlation and slope tests, without covariates."""
    simulated = isinstance(analysis, CitedAssociationIR) and analysis.method.simulation
    if not simulated:
        key = getattr(getattr(analysis, "method", None), "key", "this analysis")
        fail(
            "planning_point",
            f"{key} is not simulated with skewed data. skewness and exposure_skewness are for "
            "simulating the tests of a correlation or a regression slope.",
            target.span,
        )
    if analysis.covariates:
        fail(
            "planning_point",
            "Skewed data are simulated without covariates for now. With covariates and normal "
            "data, calculate(...) gives the slope's exact power.",
            target.span,
        )


SCENARIO_REFUSED = (
    "sd_treatment and skewness describe a scenario for simulating a two-sample t-test; "
    "leave them out here."
)


def _with_design_effect(point: dict, value) -> dict:
    """A survey's design effect is written only when the point gives one."""
    effect = getattr(value, "design_effect", None)
    return point if effect is None else {**point, "design_effect": str(effect)}


def normalize(value: object) -> object:
    """Serialize semantic objects, without implying a proof or executing a backend."""
    match value:
        case Fraction():
            return str(value)
        case TwoArmModelIR(assignment=assignment, measured=measured):
            # Only what a file declared beyond the arm sizes is written, so a model keeps
            # the same record however it is spelled and whatever was added later.
            outcome = normalize(measured)
            return {
                "module": OUTCOMES[measured.kind].constructor,
                **normalize(assignment),
                **{key: value for key, value in outcome.items() if key not in ("outcome", "name")},
                **({"outcome_name": outcome["name"]} if "name" in outcome else {}),
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
            if value.population is not None:
                result["population"] = value.population
            return result
        case StratumIR(control=control, treatment=treatment):
            return {"control": control, "treatment": treatment}
        case OutcomeIR(kind=kind, better=better, measurements=measurements):
            return {
                "outcome": kind,
                **({"better": better} if better else {}),
                **({"measurements": measurements} if measurements > 1 else {}),
                **({"name": value.name} if value.name is not None else {}),
            }
        case OutcomeNullIR(model=model, predicate=predicate, value=bound):
            result = {"predicate": predicate, "model": normalize(model)}
            if NULL_FORMS[predicate][1].takes_value:
                result["value"] = str(bound)
            return result
        case SharpNullIR(model=model, predicate=predicate):
            return {"predicate": predicate, "model": normalize(model)}
        case CrossSectionalStudyIR(n=n, exposure=exposure, outcome=outcome):
            return {
                "study": "cross_sectional",
                "n": n,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case CohortStudyIR(exposure=exposure, outcome=outcome):
            sizes = (
                {"n": value.n}
                if value.groups is None
                else {"exposed": value.exposed, "unexposed": value.unexposed}
            )
            return {
                "study": "cohort",
                **sizes,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case CaseControlStudyIR(cases=cases, controls=controls, exposure=exposure, outcome=outcome):
            return {
                "study": "case_control",
                "cases": cases,
                "controls": controls,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case PersonTimeStudyIR(exposure=exposure, outcome=outcome):
            return {
                "study": "person_time_cohort",
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case RateAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "rate_test",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
        case ObservedEventsIR(model=model):
            return {
                "model": normalize(model),
                "exposed_events": value.exposed_events,
                "exposed_time": str(value.exposed_time),
                "unexposed_events": value.unexposed_events,
                "unexposed_time": str(value.unexposed_time),
            }
        case RateResultIR(analysis=analysis, events=events):
            return {"analysis": normalize(analysis), "events": normalize(events)}
        case RateRatioIR(events=events, level=level):
            return {"events": normalize(events), "level": str(level)}
        case ProportionIR(measure=measure, model=model, cases=cases, level=level, group=group):
            return {
                "measure": measure,
                "model": normalize(model),
                "cases": cases,
                "level": str(level),
                **({"group": group} if group else {}),
            }
        case MatchedStudyIR(pairs=pairs, exposure=exposure, outcome=outcome):
            return {
                "study": "matched_case_control",
                "pairs": pairs,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case MatchedAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "mcnemar",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
        case MatchedPairsIR(model=model):
            return {"model": normalize(model), **dict(zip(PAIR_CELLS, value.cells, strict=True))}
        case MatchedResultIR(analysis=analysis, observed=observed):
            return {"analysis": normalize(analysis), "pairs": normalize(observed)}
        case MatchedIntervalIR(observed=observed, level=level):
            return {"pairs": normalize(observed), "level": str(level)}
        case AssociationTableIR(model=model):
            return {"model": normalize(model), **dict(zip(CELLS, value.cells, strict=True))}
        case AssociationResultIR(analysis=analysis, table=table):
            return {"analysis": normalize(analysis), "table": normalize(table)}
        case EffectIntervalIR(measure=measure, table=table, level=level):
            return {"measure": measure, "table": normalize(table), "level": str(level)}
        case AssociationNullIR(model=model, predicate=predicate):
            return {"predicate": predicate, "model": normalize(model)}
        case CitedAssociationIR(plan=plan, hypothesis=hypothesis, alpha=alpha, method=method):
            return {
                "test": method.key,
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
                **({"adjusted_for": list(value.covariates)} if value.covariates else {}),
            }
        case AssociationAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "fisher_exact",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
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
        case RatesIR(p_control=control, p_treatment=treatment, icc=icc):
            point = {"p_control": str(control), "p_treatment": str(treatment)}
            point = point if icc is None else {**point, "icc": str(icc)}
            return _with_cluster_cv(point, value)
        case RateIR(value=rate):
            return {"response_rate": str(rate)}
        case RisksIR(unexposed=unexposed, exposed=exposed, exposed_share=share):
            point = {"risk_unexposed": str(unexposed), "risk_exposed": str(exposed)}
            return point if share is None else {**point, "exposed_share": str(share)}
        case OutcomePrevalenceIR(unexposed=unexposed, exposed=exposed, exposed_share=share):
            point = {
                "prevalence_unexposed": str(unexposed),
                "prevalence_exposed": str(exposed),
                "exposed_share": str(share),
            }
            return _with_design_effect(point, value)
        case TotalCandidatesIR(analysis=analysis, min_n=low, max_n=high):
            return {"analysis": normalize(analysis), "min_n": low, "max_n": high}
        case ExposurePrevalenceIR(controls=controls, cases=cases):
            return {"exposure_controls": str(controls), "exposure_cases": str(cases)}
        case DiscordantPairsIR(share=share, odds_ratio=ratio):
            return {"discordant": str(share), "odds_ratio": str(ratio)}
        case IncidenceRatesIR(rate_ratio=ratio, exposed_time=exposed, unexposed_time=unexposed):
            point = {
                "rate_ratio": str(ratio),
                "exposed_time": str(exposed),
                "unexposed_time": str(unexposed),
            }
            return point if value.events is None else {**point, "events": value.events}
        case CountCandidatesIR(analysis=analysis, min_size=low, max_size=high):
            unit = value.unit
            return {"analysis": normalize(analysis), f"min_{unit}": low, f"max_{unit}": high}
        case GroupCandidatesIR(analysis=analysis, min_size=low, max_size=high, ratio=ratio):
            low_key, high_key, ratio_key = GROUP_SEARCH_KEYS[analysis.plan.model.design]
            return {"analysis": normalize(analysis), low_key: low, high_key: high, ratio_key: ratio}
        case MeanDifferenceIR(value=difference, sd=sd, icc=icc):
            point = {"mean_difference": str(difference), "sd": str(sd)}
            point = point if icc is None else {**point, "icc": str(icc)}
            return _with_cluster_cv(point, value)
        case HazardRatioIR(value=ratio, events=events):
            return {"hazard_ratio": str(ratio), "events": events}
        case CorrelationIR(value=rho):
            return _with_cluster_cv({"correlation": str(rho)}, value)
        case OutcomeMeansIR(unexposed=unexposed, exposed=exposed, sd=sd, exposed_share=share):
            point = {"mean_unexposed": str(unexposed), "mean_exposed": str(exposed), "sd": str(sd)}
            point = point if share is None else {**point, "exposed_share": str(share)}
            return _with_design_effect(point, value)
        case OddsPerSdIR(odds_ratio=ratio, baseline=baseline, exposure_r2=share):
            point = {"odds_ratio_per_sd": str(ratio), "baseline": str(baseline)}
            point = point if share is None else {**point, "exposure_r2": str(share)}
            return _with_design_effect(point, value)
        case SlopeIR(value=slope, exposure_sd=exposure, residual_sd=residual):
            point = {
                "slope": str(slope),
                "exposure_sd": str(exposure),
                "residual_sd": str(residual),
            }
            if value.exposure_r2 is not None:
                point["exposure_r2"] = str(value.exposure_r2)
            return _with_cluster_cv(_with_design_effect(point, value), value)
        case ExponentialSurvivalIR(hazard_ratio=ratio, control_median=median):
            point = {
                "hazard_ratio": str(ratio),
                "control_median": str(median),
                "accrual": str(value.accrual),
                "follow_up": str(value.follow_up),
            }
            if value.dropout is not None:
                point.update(dropout=str(value.dropout), dropout_time=str(value.dropout_time))
            if value.effect_delay is not None:
                point["effect_delay"] = str(value.effect_delay)
            return point
        case SingleProportionIR(value=rate):
            point = {"proportion": str(rate)}
            if value.population_size is not None:
                point["population_size"] = value.population_size
            return _with_design_effect(point, value)
        case PrecisionTargetIR(at=point, level=level):
            result = {"at": normalize(point), "level": str(level)}
            if value.margin is not None:
                result["margin_of_error"] = str(value.margin)
            else:
                result["relative_margin_of_error"] = str(value.relative)
            if value.assurance is not None:
                result["assurance"] = str(value.assurance)
            return result
        case PlannedIntervalIR(model=model, measure=measure, method=method, group=group):
            result = {"interval": measure, "model": normalize(model), "method": method}
            return result if group is None else {**result, "group": group}
        case IntervalCandidatesIR(interval=interval, min_size=low, max_size=high, ratio=ratio):
            return {
                "interval": normalize(interval),
                "min_size": low,
                "max_size": high,
                "ratio": ratio,
            }
        case PowerTargetIR(at=point, minimum=minimum, maximum_typeI=maximum):
            target = {
                "at": normalize(point),
                "minimum_power": str(minimum),
                "maximum_typeI": str(maximum),
            }
            if value.nulls is not None:
                target["nulls"] = [normalize(null) for null in value.nulls.points]
            if value.rejecting is not None:
                target["rejecting"] = value.rejecting
            return target
        case EndpointPointsIR(points=points, correlation=correlation):
            return {
                "endpoints": [normalize(point) for point in points],
                "correlation": str(correlation),
            }
        case NullScenariosIR(points=points):
            return {"null_scenarios": [normalize(point) for point in points]}
        case ReestimationIR(analysis=analysis):
            return {
                "rule": "blinded_reestimation",
                "analysis": normalize(analysis),
                "interim_per_arm": value.interim_per_arm,
                "max_per_arm": value.max_per_arm,
                "difference": str(value.difference),
                "power": str(value.power),
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
        case ClusterCandidatesIR(analysis=analysis, low=low, high=high, cluster_size=size):
            if value.varies == "clusters":
                return {
                    "analysis": normalize(analysis),
                    "cluster_size": size,
                    "min_clusters_per_arm": low,
                    "max_clusters_per_arm": high,
                }
            return {
                "analysis": normalize(analysis),
                "min_cluster_size": low,
                "max_cluster_size": high,
            }
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


def _declare_population(
    assignment: AssignmentIR, arguments: dict[str, LocatedValue]
) -> AssignmentIR:
    """Add who is analysed, when the assignment declares it."""
    population = arguments.get("population")
    if population is None or population.value is None:
        return assignment
    if population.value not in POPULATIONS:
        fail(
            "domain",
            'population must be "randomised" (everyone randomised, analysed in the arm they '
            'were assigned to) or "per_protocol" (participants excluded after randomisation '
            "are left out). Leave it out if the file does not say.",
            population.span,
        )
    return replace(assignment, population=population.value)


def _arm_sizes(arguments: dict[str, LocatedValue]) -> AssignmentIR:
    for name in ("n_control", "n_treatment"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be a positive integer.", arguments[name].span)
    return AssignmentIR(arguments["n_control"].value, arguments["n_treatment"].value)


def _assignment(arguments: dict[str, LocatedValue], span: Span) -> AssignmentIR:
    declared = _declare_randomisation(_arm_sizes(arguments), arguments, span)
    return _declare_population(declared, arguments)


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
    declared = _declare_randomisation(clustered, arguments, span)
    return _declare_population(declared, arguments)


def _outcome_piece(kind: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> OutcomeIR:
        better = arguments["better"]
        if better.value not in (None, "higher", "lower"):
            fail("domain", 'better must be "higher" or "lower".', better.span)
        measurements = arguments.get("measurements")
        count = 1 if measurements is None or measurements.value is None else measurements.value
        if count < 1:
            fail("domain", "measurements must be a positive integer.", measurements.span)
        named = arguments.get("name")
        name = None if named is None or named.value is None else named.value.strip()
        if name is not None and (not name or "\n" in name or len(name) > MAX_NAME):
            fail(
                "domain",
                f'name must be one line of 1 to {MAX_NAME} characters, such as "response".',
                named.span,
            )
        return OutcomeIR(kind, better.value, count, name)

    return build


# Longest outcome name.
MAX_NAME = 100
MAX_SIMULATED_CLUSTER = 1000  # participants per cluster when simulating cluster proportions


def _leaves(members) -> Iterator[tuple[str, object]]:
    """The single analyses in a combination, inside nested ones too, with their names."""
    for name, analysis in members:
        if isinstance(analysis, (ComposedFamilyIR, FamilyIR)):
            yield from _leaves(analysis.analyses)
        else:
            yield name, analysis


def named_outcomes(members) -> list[str]:
    """The outcome names a combination's analyses declare, in order, each once."""
    names = (analysis.plan.model.measured.name for _, analysis in _leaves(members))
    return list(dict.fromkeys(name for name in names if name is not None))


def _question(analysis) -> str:
    """What an analysis asks, whatever its level: its test, its null and its design."""
    return json.dumps(
        {key: value for key, value in normalize(analysis).items() if key != "alpha"},
        sort_keys=True,
    )


def _outcome_words(outcome: OutcomeIR) -> str:
    better = f' with better="{outcome.better}"' if outcome.better else " with no better="
    return f"a {outcome.kind} outcome{better}"


def _check_named_outcomes(members, span: Span) -> None:
    """One name is one outcome, and a combination asks each question of it once."""
    first: dict[str, tuple[str, OutcomeIR]] = {}
    asked: dict[str, str] = {}
    for label, analysis in _leaves(members):
        outcome = analysis.plan.model.measured
        if outcome.name is None:
            continue
        earlier, seen = first.setdefault(outcome.name, (label, outcome))
        if (seen.kind, seen.better) != (outcome.kind, outcome.better):
            fail(
                "outcome_conflict",
                f'The outcome "{outcome.name}" is {_outcome_words(seen)} in {earlier} but '
                f"{_outcome_words(outcome)} in {label}. One name is one outcome; give different "
                "outcomes different names.",
                span,
            )
        question = _question(analysis)
        if question in asked:
            fail(
                "duplicate_analysis",
                f"{asked[question]} and {label} ask the same question of the outcome "
                f'"{outcome.name}": the same test of the same null on the same participants. '
                "Listed twice, one question would be reported as two. Keep one; if the other "
                "is a different outcome, give it its own name.",
                span,
            )
        asked[question] = label


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
        _observational_refused(design, method.key)
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
    _observational_refused(design, "declared_test")
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
    _observational_refused(model, "no_effect")
    if not isinstance(model.value, TwoArmModelIR):
        fail("type", "no_effect is a null for a two-arm model.", model.span)
    return SharpNullIR(model.value)


def _randomisation_test(arguments: dict[str, LocatedValue], span: Span) -> RandomisationAnalysisIR:
    design, alpha = arguments["design"], arguments["alpha"]
    _observational_refused(design, "randomisation_test")
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
    if assignment.population == "per_protocol":
        model = design.value.model
        others = "fisher" if model.outcome == "binary" else next(iter(_fitting(model)), "")
        fail(
            "population_mismatch",
            "randomisation_test needs every randomised unit analysed, in the arm it was "
            "assigned to: its level comes from how exactly those units were randomised. The "
            'assignment declares population="per_protocol", which leaves out units excluded '
            "after randomisation, so the units analysed were not randomised as a set. Analyse "
            'everyone randomised and declare population="randomised"'
            + (
                f"; for a per-protocol analysis, use another test, such as {others}, whose "
                "claim says it covers the per-protocol population only."
                if others
                else "."
            ),
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


def _observational_refused(design: LocatedValue, test: str) -> None:
    """Tests built on randomised arms refuse an observational design, whose exposure was
    not assigned."""
    model = design.value.model if isinstance(design.value, PlanIR) else design.value
    if isinstance(model, ObservationalStudyIR):
        fail(
            "observational_design",
            f"{test} relies on randomised arms, but this is an observational "
            f"{model.design.replace('_', '-')} study: exposure was not assigned. Use "
            "fisher_exact from tests.association to test association.",
            design.span,
        )


def _study_name(arguments: dict[str, LocatedValue], key: str) -> str:
    argument = arguments.get(key)
    if argument is None or argument.value is None:
        return key
    if not NAME.fullmatch(argument.value):
        fail(
            "domain",
            f"{key} names what is studied in a few plain words, starting with a letter, "
            "at most 60 characters.",
            argument.span,
        )
    return argument.value


def _size(arguments: dict[str, LocatedValue], key: str) -> int | None:
    argument = arguments.get(key)
    if argument is None or argument.value is None:
        return None
    if argument.value < 1:
        fail("domain", f"{key} must be a positive whole number.", argument.span)
    if argument.value > MAX_PARTICIPANTS:
        fail("domain", f"{key} may be at most {MAX_PARTICIPANTS}.", argument.span)
    return argument.value


def _choice(arguments: dict[str, LocatedValue], key: str, choices: dict, default: str) -> str:
    argument = arguments.get(key)
    if argument is None or argument.value is None:
        return default
    if argument.value not in choices:
        fail("domain", f"{key} must be one of: {', '.join(choices)}.", argument.span)
    return argument.value


def _study_options(arguments: dict[str, LocatedValue], span: Span, n: int | None = None) -> dict:
    """Names, measurement scales and the survey design, as a study declares them."""
    options = {
        "exposure": _study_name(arguments, "exposure"),
        "outcome": _study_name(arguments, "outcome"),
        "exposure_scale": _choice(arguments, "exposure_scale", SCALES, "binary"),
        "outcome_scale": _choice(arguments, "outcome_scale", SCALES, "binary"),
        "survey": _choice(arguments, "survey", SURVEYS, "simple_random"),
    }
    clusters = _size(arguments, "clusters")
    if options["survey"] == "cluster":
        if clusters is None:
            fail(
                "domain",
                "A cluster survey declares how many clusters it sampled: clusters=....",
                span,
            )
        if clusters < 2 or (n is not None and clusters > n):
            fail(
                "domain",
                "clusters must be at least 2 and at most the number sampled.",
                arguments["clusters"].span,
            )
    elif clusters is not None:
        fail(
            "domain",
            'clusters belongs to a cluster survey: declare survey="cluster" with it.',
            arguments["clusters"].span,
        )
    options["clusters"] = clusters
    return options


def _simple_binary(
    argument: LocatedValue, test: str, *, outcome: bool = True, exposure: bool = True
) -> None:
    """Proved methods need yes-or-no variables and simple random sampling."""
    model = argument.value.model if isinstance(argument.value, PlanIR) else argument.value
    if not isinstance(model, ObservationalStudyIR):
        return
    for wanted, which, scale in (
        (outcome, "outcome", model.outcome_scale),
        (exposure, "exposure", model.exposure_scale),
    ):
        if wanted and scale != "binary":
            fail(
                "type",
                f"{test} needs a yes-or-no {which}; this study declares a continuous {which}. "
                "For continuous variables use linear_association from tests.regression or "
                "pearson_correlation from tests.correlation.",
                argument.span,
            )
    if model.survey != "simple_random":
        fail(
            "complex_sample",
            f"{test} assumes participants were sampled independently with equal probability; "
            f"this survey declares {model.survey} sampling. Use a design-based test from "
            "tests.survey, such as survey_logistic or rao_scott_test.",
            argument.span,
        )


def _cross_sectional(arguments: dict[str, LocatedValue], span: Span) -> CrossSectionalStudyIR:
    n = _size(arguments, "n")
    return CrossSectionalStudyIR(n=n, **_study_options(arguments, span, n))


def _cohort(arguments: dict[str, LocatedValue], span: Span) -> CohortStudyIR:
    exposed, unexposed, n = (_size(arguments, key) for key in ("exposed", "unexposed", "n"))
    if n is not None and (exposed is not None or unexposed is not None):
        fail(
            "domain",
            "Declare either exposed and unexposed, when the cohort sampled the groups in fixed "
            "numbers, or n, when it sampled one population and exposure was measured; not both.",
            span,
        )
    if n is None and (exposed is None or unexposed is None):
        fail(
            "domain",
            "A cohort needs exposed and unexposed group sizes, or its total n when the number "
            "exposed was not fixed.",
            span,
        )
    total = n if n is not None else exposed + unexposed
    if total > MAX_PARTICIPANTS:
        fail("domain", f"A study may have at most {MAX_PARTICIPANTS} participants.", span)
    return CohortStudyIR(
        exposed=exposed, unexposed=unexposed, n=n, **_study_options(arguments, span, total)
    )


def _case_control(arguments: dict[str, LocatedValue], span: Span) -> CaseControlStudyIR:
    cases, controls = _size(arguments, "cases"), _size(arguments, "controls")
    if cases + controls > MAX_PARTICIPANTS:
        fail("domain", f"A study may have at most {MAX_PARTICIPANTS} participants.", span)
    return CaseControlStudyIR(
        cases=cases, controls=controls, **_study_options(arguments, span, cases + controls)
    )


def _no_association(arguments: dict[str, LocatedValue], span: Span) -> AssociationNullIR:
    return AssociationNullIR(arguments["model"].value)


def _fisher_exact(arguments: dict[str, LocatedValue], span: Span) -> AssociationAnalysisIR:
    design, null = arguments["design"], arguments["null"]
    _matched_refused(
        design,
        "fisher_exact ignores the matching, so its guarantee does not apply to matched pairs. "
        "Use mcnemar for a matched study.",
    )
    _rates_refused(
        design,
        "fisher_exact compares counts of participants; a person-time cohort counts events over "
        "person-time. Use rate_test.",
    )
    _simple_binary(design, "fisher_exact")
    if not isinstance(design.value.model, ObservationalStudyIR):
        fail(
            "type",
            "fisher_exact tests association in an observational study, but this design is a "
            "randomised trial. Use fisher from tests.fisher to compare randomised arms.",
            design.span,
        )
    if design.value.model != null.value.model:
        fail(
            "model_mismatch",
            "fisher_exact: the null belongs to a different study. Declare "
            "no_association(model=...) over the study the design samples.",
            null.span,
        )
    return AssociationAnalysisIR(design.value, null.value, arguments["alpha"].value)


def _matched_refused(argument: LocatedValue, message: str) -> None:
    model = argument.value.model if isinstance(argument.value, PlanIR) else argument.value
    if isinstance(model, MatchedStudyIR):
        fail("matched_design", message, argument.span)


def _matched_case_control(arguments: dict[str, LocatedValue], span: Span) -> MatchedStudyIR:
    pairs = arguments["pairs"]
    if not 1 <= pairs.value <= MAX_PAIRS:
        fail("domain", f"pairs must be a whole number from 1 to {MAX_PAIRS}.", pairs.span)
    return MatchedStudyIR(pairs=pairs.value, **_study_options(arguments, span, pairs.value))


def _observed_pairs(arguments: dict[str, LocatedValue], span: Span) -> MatchedPairsIR:
    _simple_binary(arguments["model"], "observed_pairs", outcome=False)
    model = arguments["model"].value
    cells = []
    for key in PAIR_CELLS:
        argument = arguments[key]
        if argument.value < 0:
            fail("domain", f"{key} must be a whole number, zero or more.", argument.span)
        cells.append(argument.value)
    problem = pairs_problem(model.pairs, cells)
    if problem:
        fail("domain", problem, span)
    return MatchedPairsIR(model, *cells)


def _mcnemar(arguments: dict[str, LocatedValue], span: Span) -> MatchedAnalysisIR:
    design, null = arguments["design"], arguments["null"]
    _simple_binary(design, "mcnemar", outcome=False)
    if not isinstance(design.value.model, MatchedStudyIR):
        fail(
            "type",
            "mcnemar tests matched pairs, but this design is not matched. For unmatched "
            "groups use fisher_exact.",
            design.span,
        )
    if design.value.model != null.value.model:
        fail(
            "model_mismatch",
            "mcnemar: the null belongs to a different study. Declare no_association(model=...) "
            "over the study the design samples.",
            null.span,
        )
    return MatchedAnalysisIR(design.value, null.value, arguments["alpha"].value)


def _matched_result(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis, observed = arguments["analysis"], arguments["pairs"]
    if analysis.value.plan.model != observed.value.model:
        fail(
            "model_mismatch",
            "matched_result: the pairs belong to another study than the analysis.",
            observed.span,
        )
    return ClaimIR(
        "result",
        MatchedResultIR(analysis.value, observed.value),
        observed.name or analysis.name or "<expression>",
    )


def _conditional_odds_ratio(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    observed, level = arguments["pairs"], arguments["level"]
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    interval = MatchedIntervalIR(observed.value, level.value)
    try:
        interval.lower()
    except ValueError as error:
        fail("domain", str(error), observed.span)
    return ClaimIR("interval", interval, observed.name or "<expression>")


def _rates_refused(argument: LocatedValue, message: str) -> None:
    model = argument.value.model if isinstance(argument.value, PlanIR) else argument.value
    if isinstance(model, PersonTimeStudyIR):
        fail("type", message, argument.span)


def _person_time_cohort(arguments: dict[str, LocatedValue], span: Span) -> PersonTimeStudyIR:
    return PersonTimeStudyIR(**_study_options(arguments, span))


def _observed_events(arguments: dict[str, LocatedValue], span: Span) -> ObservedEventsIR:
    _simple_binary(arguments["model"], "observed_events", outcome=False)
    values = {}
    for key in ("exposed_events", "unexposed_events"):
        if arguments[key].value < 0:
            fail("domain", f"{key} must be a whole number, zero or more.", arguments[key].span)
        values[key] = arguments[key].value
    for key in ("exposed_time", "unexposed_time"):
        if arguments[key].value <= 0:
            fail("domain", f"{key} must be positive person-time.", arguments[key].span)
        values[key] = arguments[key].value
    events = ObservedEventsIR(
        arguments["model"].value,
        values["exposed_events"],
        values["exposed_time"],
        values["unexposed_events"],
        values["unexposed_time"],
    )
    try:
        events.lower()
    except ValueError as error:
        fail("domain", str(error), span)
    return events


def _rate_test(arguments: dict[str, LocatedValue], span: Span) -> RateAnalysisIR:
    design, null = arguments["design"], arguments["null"]
    _simple_binary(design, "rate_test", outcome=False)
    if not isinstance(design.value.model, PersonTimeStudyIR):
        fail(
            "type",
            "rate_test compares incidence rates over person-time, but this design does not "
            "count person-time. Use person_time_cohort, or fisher_exact to compare counts.",
            design.span,
        )
    if design.value.model != null.value.model:
        fail(
            "model_mismatch",
            "rate_test: the null belongs to a different study. Declare "
            "no_association(model=...) over the study the design samples.",
            null.span,
        )
    return RateAnalysisIR(design.value, null.value, arguments["alpha"].value)


def _rate_result(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis, events = arguments["analysis"], arguments["events"]
    if analysis.value.plan.model != events.value.model:
        fail(
            "model_mismatch",
            "rate_result: the events belong to another study than the analysis.",
            events.span,
        )
    return ClaimIR(
        "result",
        RateResultIR(analysis.value, events.value),
        events.name or analysis.name or "<expression>",
    )


def _rate_ratio(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    events, level = arguments["events"], arguments["level"]
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    interval = RateRatioIR(events.value, level.value)
    try:
        interval.lower()
    except ValueError as error:
        fail("domain", str(error), events.span)
    return ClaimIR("interval", interval, events.name or "<expression>")


def _proportion(measure: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        model, cases, level = arguments["model"], arguments["cases"], arguments["level"]
        _simple_binary(model, measure, exposure=False)
        group = arguments.get("group")
        group = group.value if group is not None else None
        reason = proportion_not_estimable(measure, model.value.design)
        if reason:
            fail("not_estimable", f"{measure}: {reason}", model.span)
        if model.value.groups is not None and group is None:
            fail(
                "domain",
                "This cohort sampled exposed and unexposed groups separately, so say which: "
                'group="exposed" or group="unexposed".',
                span,
            )
        if model.value.groups is None and group is not None:
            fail(
                "domain",
                "This study did not fix exposed and unexposed groups; leave group out.",
                arguments["group"].span,
            )
        if not 0 < level.value < 1:
            fail("domain", "level must lie strictly between 0 and 1.", level.span)
        estimate = ProportionIR(measure, model.value, cases.value, level.value, group)
        if not 0 <= cases.value <= estimate.size:
            fail("domain", f"cases must be between 0 and {estimate.size}.", cases.span)
        try:
            estimate.lower()
        except ValueError as error:
            fail("domain", str(error), span)
        return ClaimIR("interval", estimate, model.name or "<expression>")

    return build


def _words(items) -> str:
    items = [item.replace("_", "-") for item in items]
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " or " + items[-1]


def _fitting_methods(model: "ObservationalStudyIR") -> str:
    """The cited methods whose design, scales and survey fit a study, as a hint."""
    keys = [
        m.key
        for m in OBSERVATIONAL_METHODS.values()
        if model.design in m.designs
        and model.outcome_scale in m.outcome_scales
        and model.exposure_scale in m.exposure_scales
        and model.survey in m.surveys
    ]
    return f" Methods that fit this study: {', '.join(keys)}." if keys else ""


def _cited_association(method: ObservationalMethod) -> Callable:
    """The contract of a cited observational method: design, scales, survey, size, covariates."""

    def build(arguments: dict[str, LocatedValue], span: Span) -> CitedAssociationIR:
        design, null, alpha = arguments["design"], arguments["null"], arguments["alpha"]
        model = design.value.model
        key = method.key
        if not isinstance(model, ObservationalStudyIR):
            fail(
                "type",
                f"{key} is for observational studies; this design is a randomised trial.",
                design.span,
            )
        if model != null.value.model:
            fail(
                "model_mismatch",
                f"{key}: the null belongs to a different study. Declare "
                "no_association(model=...) over the study the design samples.",
                null.span,
            )
        if model.design not in method.designs:
            kinds = _words(method.designs)
            code = (
                "not_estimable"
                if key == "modified_poisson" and model.design.endswith("case_control")
                else "type"
            )
            fail(
                code,
                f"{key} fits {kinds} studies; this is a {model.design.replace('_', '-')} study."
                + (
                    " A case-control study cannot estimate a risk or prevalence ratio."
                    if code == "not_estimable"
                    else ""
                )
                + _fitting_methods(model),
                design.span,
            )
        for which, scale, allowed in (
            ("outcome", model.outcome_scale, method.outcome_scales),
            ("exposure", model.exposure_scale, method.exposure_scales),
        ):
            if scale not in allowed:
                fail(
                    "type",
                    f"{key} needs a {' or '.join(allowed)} {which}; this study declares a "
                    f"{scale} {which}." + _fitting_methods(model),
                    design.span,
                )
        if model.survey not in method.surveys:
            fail(
                "complex_sample",
                f"{key} assumes participants were sampled independently with equal "
                f"probability; this survey declares {model.survey} sampling."
                + _fitting_methods(model),
                design.span,
            )
        total = (
            model.pairs
            if isinstance(model, MatchedStudyIR)
            else (model.total if not isinstance(model, PersonTimeStudyIR) else None)
        )
        if total is not None and total < method.min_total:
            fail(
                "domain",
                f"{key} needs at least {method.min_total} participants; this study has {total}.",
                design.span,
            )
        clustered = model.survey == "cluster"
        if method.min_clusters and clustered and model.clusters < method.min_clusters:
            fail(
                "domain",
                f"{key} needs at least {method.min_clusters} sampled clusters for its "
                f"design-based variance; this survey sampled {model.clusters}.",
                design.span,
            )
        if not 0 < alpha.value < 1:
            fail("domain", "alpha must lie strictly between 0 and 1 for this test.", alpha.span)
        covariates: list[str] = []
        listed = arguments.get("adjusted_for")
        if listed is not None and listed.value is not None:
            for item in listed.value:
                if not isinstance(item.value, str) or not NAME.fullmatch(item.value):
                    fail("domain", "Each covariate is a name in a few plain words.", item.span)
                if item.value in covariates or item.value in (model.exposure, model.outcome):
                    fail(
                        "domain",
                        "Each covariate is named once, and is neither the exposure nor the "
                        "outcome.",
                        item.span,
                    )
                covariates.append(item.value)
            if len(covariates) > MAX_COVARIATES:
                fail("domain", f"At most {MAX_COVARIATES} covariates.", listed.span)
        return CitedAssociationIR(design.value, null.value, alpha.value, method, tuple(covariates))

    return build


def _cited_association_constructor(method: ObservationalMethod) -> Constructor:
    parameters = [("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")]
    if method.covariates:
        parameters.append(("adjusted_for", "list", True))
    designs = _words(method.designs)
    return _constructor(
        method.key,
        tuple(parameters),
        "CitedAssociation",
        _cited_association(method),
        documentation=f"{method.title}. Fits {designs} studies with a "
        f"{' or '.join(method.outcome_scales)} outcome. Its guarantee is cited from the "
        "literature and not checked by Lean."
        + (" adjusted_for lists the covariates, by name." if method.covariates else ""),
    )


def _observed_table(arguments: dict[str, LocatedValue], span: Span) -> AssociationTableIR:
    _simple_binary(arguments["model"], "observed_table")
    _rates_refused(
        arguments["model"],
        "A person-time cohort records events and person-time, not a table of participants. "
        "Use observed_events.",
    )
    _matched_refused(
        arguments["model"],
        "observed_table records two unmatched groups, which loses the pairs. Use "
        "observed_pairs for a matched study.",
    )
    model = arguments["model"].value
    cells = []
    for key in CELLS:
        argument = arguments[key]
        if argument.value < 0:
            fail("domain", f"{key} must be a whole number, zero or more.", argument.span)
        cells.append(argument.value)
    problem = table_problem(
        model.design, model.groups, None if model.groups is not None else model.n, cells
    )
    if problem:
        fail("domain", problem, span)
    return AssociationTableIR(model, *cells)


def _association_result(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis, table = arguments["analysis"], arguments["table"]
    if analysis.value.plan.model != table.value.model:
        fail(
            "model_mismatch",
            "association_result: the table belongs to another study than the analysis. "
            "Declare observed_table(model=...) over the study the analysis tests.",
            table.span,
        )
    return ClaimIR(
        "result",
        AssociationResultIR(analysis.value, table.value),
        table.name or analysis.name or "<expression>",
    )


def _effect_interval(measure: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        table, level = arguments["table"], arguments["level"]
        reason = not_estimable(measure, table.value.model.design)
        if reason:
            fail("not_estimable", f"{measure}: {reason}", table.span)
        if not 0 < level.value < 1:
            fail("domain", "level must lie strictly between 0 and 1.", level.span)
        interval = EffectIntervalIR(measure, table.value, level.value)
        try:
            interval.lower()
        except ValueError as error:
            fail("domain", str(error), level.span)
        return ClaimIR("interval", interval, table.name or "<expression>")

    return build


def _fisher(alternative: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> AnalysisIR:
        plan, hypothesis = arguments["design"].value, arguments["null"].value
        test = "fisher" if alternative == "two_sided" else "fisher_one_sided"
        _observational_refused(arguments["design"], test)
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
    _observational_refused(arguments["design"], "difference_test")
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
    argument: LocatedValue, what: str, *, combinations: bool = True, randomisation: bool = True
) -> list[tuple[str, object]]:
    """Named, distinct analyses for a family, a sequence, a graph or a design's looks.

    With combinations=True an entry may also be a whole design with looks, a
    family, a sequence or a graph. With randomisation=True an entry may be a
    randomisation test.
    """
    items = argument.value
    allowed = (
        (AnalysisIR, CitedAnalysisIR, ComposedFamilyIR, FamilyIR)
        if combinations
        else (AnalysisIR, CitedAnalysisIR)
    ) + ((RandomisationAnalysisIR,) if randomisation else ())
    if not 2 <= len(items) <= MAX_ENDPOINTS:
        fail("family_size", f"This needs between 2 and {MAX_ENDPOINTS} {what}.", argument.span)
    members = []
    for item in items:
        if not isinstance(item.value, allowed) or item.name is None:
            fail(
                "type",
                "Each entry must be a named analysis: an exact two-arm test"
                + (", a randomisation test" if randomisation else "")
                + (
                    ", a cited test, or a named design, family, sequence or graph."
                    if combinations
                    else " or a cited test."
                )
                + (
                    ""
                    if randomisation
                    else " A randomisation test counts splits of one fixed set of units, so it "
                    "cannot be a look of a sequential design."
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
    _check_named_outcomes(members, argument.span)
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
    looks = _members(arguments["looks"], "looks", combinations=False, randomisation=False)
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
    target = getattr(claim.value.subject, "target", None)
    point = getattr(target, "at", None)
    if claim.value.kind in ("meets", "sample_size"):
        # What the analysis's kind allows: see plan_kinds.KINDS.
        kind = kind_of(planned_analysis(claim.value.subject))
        if kind.calculate is None:
            fail("unsupported_claim", kind.refuse_calculate, claim.span)
        if kind.check_calculate is not None:
            resolve(kind.check_calculate)(claim)
    if getattr(point, "cluster_size_cv", None):
        fail(
            "unsupported_claim",
            "The noncentral t assumes clusters of equal size. For clusters whose sizes vary, "
            "use simulate(...), which draws the sizes.",
            claim.span,
        )
    if getattr(point, "effect_delay", None):
        fail(
            "unsupported_claim",
            "Schoenfeld's formula assumes the hazard ratio holds from entry on. For an effect "
            "that starts later, use simulate(...), which draws the survival times.",
            claim.span,
        )
    if departs(point):
        fail(
            "unsupported_claim",
            "The formula assumes normal data, with a common SD for two means. For unequal SDs "
            "or skewed data, use simulate(...), which runs the test on that scenario.",
            claim.span,
        )
    return claim.value


def _probability(argument: LocatedValue, name: str, *, positive: bool = False) -> Fraction:
    low_ok = argument.value > 0 if positive else argument.value >= 0
    if not (low_ok and argument.value <= 1):
        bounds = "(0, 1]" if positive else "[0, 1]"
        fail("domain", f"{name} must lie in {bounds}.", argument.span)
    return argument.value


def _icc(arguments: dict[str, LocatedValue]) -> Fraction | None:
    """The intracluster correlation, when given: from 0, independent participants, up to but
    not including 1, identical participants within a cluster."""
    icc = arguments.get("icc")
    if icc is None or icc.value is None:
        return None
    if not 0 <= icc.value < 1:
        fail("domain", "icc must lie in [0, 1).", icc.span)
    return icc.value


def _cluster_cv(arguments: dict[str, LocatedValue]) -> Fraction | None:
    """The coefficient of variation of cluster sizes, when given: 0 for equal clusters."""
    cv = arguments.get("cluster_size_cv")
    if cv is None or cv.value is None:
        return None
    if not 0 <= cv.value <= 3:
        fail("domain", "cluster_size_cv must lie between 0 and 3.", cv.span)
    return cv.value


def _rates(arguments: dict[str, LocatedValue], span: Span) -> RatesIR:
    return RatesIR(
        _probability(arguments["p_control"], "p_control"),
        _probability(arguments["p_treatment"], "p_treatment"),
        _icc(arguments),
        _cluster_cv(arguments),
    )


def _mean_difference(arguments: dict[str, LocatedValue], span: Span) -> MeanDifferenceIR:
    sd = arguments["sd"]
    if sd.value <= 0:
        fail("domain", "sd must be positive.", sd.span)
    sd_treatment, skewness = arguments.get("sd_treatment"), arguments.get("skewness")
    if sd_treatment is not None and sd_treatment.value is not None and sd_treatment.value <= 0:
        fail("domain", "sd_treatment must be positive.", sd_treatment.span)
    if skewness is not None and skewness.value is not None and abs(skewness.value) > MAX_SKEWNESS:
        fail(
            "domain",
            f"skewness must lie between -{MAX_SKEWNESS} and {MAX_SKEWNESS}.",
            skewness.span,
        )
    return MeanDifferenceIR(
        arguments["value"].value,
        sd.value,
        _icc(arguments),
        _cluster_cv(arguments),
        None if sd_treatment is None else sd_treatment.value,
        None if skewness is None else skewness.value,
    )


def _hazard_ratio(arguments: dict[str, LocatedValue], span: Span) -> HazardRatioIR:
    ratio, events = arguments["value"], arguments["events"]
    if ratio.value <= 0:
        fail("domain", "A hazard ratio must be positive.", ratio.span)
    if events.value < 1:
        fail("domain", "events must be a positive integer.", events.span)
    return HazardRatioIR(ratio.value, events.value)


def _exponential_survival(arguments: dict[str, LocatedValue], span: Span) -> ExponentialSurvivalIR:
    ratio, median = arguments["hazard_ratio"], arguments["control_median"]
    accrual, follow_up = arguments["accrual"], arguments["follow_up"]
    if ratio.value <= 0:
        fail("domain", "A hazard ratio must be positive.", ratio.span)
    if median.value <= 0:
        fail("domain", "control_median must be a positive time.", median.span)
    for argument, name in ((accrual, "accrual"), (follow_up, "follow_up")):
        if argument.value < 0:
            fail("domain", f"{name} must be a time of at least 0.", argument.span)
    if accrual.value + follow_up.value <= 0:
        fail("domain", "accrual and follow_up cannot both be 0: no one would be followed.", span)
    dropout, when = arguments.get("dropout"), arguments.get("dropout_time")
    given = [a for a in (dropout, when) if a is not None and a.value is not None]
    if len(given) == 1:
        fail(
            "domain",
            "Give dropout and dropout_time together: the probability of dropping out by that "
            "time, such as dropout=1/10, dropout_time=12.",
            given[0].span,
        )
    if given:
        if not 0 <= dropout.value < 1:
            fail("domain", "dropout must lie in [0, 1).", dropout.span)
        if when.value <= 0:
            fail("domain", "dropout_time must be a positive time.", when.span)
    delay = arguments.get("effect_delay")
    if delay is not None and delay.value is not None and delay.value < 0:
        fail("domain", "effect_delay must be a time of at least 0.", delay.span)
    return ExponentialSurvivalIR(
        ratio.value,
        median.value,
        accrual.value,
        follow_up.value,
        dropout.value if given else None,
        when.value if given else None,
        None if delay is None else delay.value,
    )


def _correlation(arguments: dict[str, LocatedValue], span: Span) -> CorrelationIR:
    rho = arguments["value"]
    if not -1 < rho.value < 1:
        fail("domain", "A correlation must lie strictly between -1 and 1.", rho.span)
    return CorrelationIR(rho.value, *_skews(arguments))


def _outcome_means(arguments: dict[str, LocatedValue], span: Span) -> OutcomeMeansIR:
    sd = arguments["sd"]
    if sd.value <= 0:
        fail("domain", "sd must be positive.", sd.span)
    share = arguments.get("exposed_share")
    exposed_share = None if share is None or share.value is None else share.value
    if exposed_share is not None and not 0 < exposed_share < 1:
        fail("domain", "exposed_share must lie strictly between 0 and 1.", share.span)
    return OutcomeMeansIR(
        arguments["unexposed"].value,
        arguments["exposed"].value,
        sd.value,
        exposed_share,
        _design_effect(arguments),
    )


def _odds_per_sd(arguments: dict[str, LocatedValue], span: Span) -> OddsPerSdIR:
    ratio = arguments["odds_ratio"]
    if ratio.value <= 0:
        fail("domain", "odds_ratio must be positive.", ratio.span)
    baseline = _probability(arguments["baseline"], "baseline")
    if baseline in (0, 1):
        fail("domain", "baseline must lie strictly between 0 and 1.", arguments["baseline"].span)
    explained = arguments.get("exposure_r2")
    share = None if explained is None or explained.value is None else explained.value
    if share is not None and not 0 <= share < 1:
        fail("domain", "exposure_r2 must lie in [0, 1).", explained.span)
    return OddsPerSdIR(ratio.value, baseline, share, _design_effect(arguments))


def _slope(arguments: dict[str, LocatedValue], span: Span) -> SlopeIR:
    for name in ("exposure_sd", "residual_sd"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be positive.", arguments[name].span)
    explained = arguments.get("exposure_r2")
    share = None if explained is None or explained.value is None else explained.value
    if share is not None and not 0 <= share < 1:
        fail("domain", "exposure_r2 must lie in [0, 1).", explained.span)
    return SlopeIR(
        arguments["value"].value,
        arguments["exposure_sd"].value,
        arguments["residual_sd"].value,
        share,
        _design_effect(arguments),
        *_skews(arguments),
    )


def _skews(arguments: dict[str, LocatedValue]) -> tuple:
    """The skewness of the outcome's error and of the exposure, for simulation."""
    found = []
    for name in ("skewness", "exposure_skewness"):
        given = arguments.get(name)
        if given is not None and given.value is not None and abs(given.value) > MAX_SKEWNESS:
            fail(
                "domain", f"{name} must lie between -{MAX_SKEWNESS} and {MAX_SKEWNESS}.", given.span
            )
        found.append(None if given is None else given.value)
    return tuple(found)


def _power_target(arguments: dict[str, LocatedValue], span: Span) -> PowerTargetIR:
    nulls, rejecting = arguments.get("nulls"), arguments.get("rejecting")
    if rejecting is not None and rejecting.value is not None and rejecting.value not in REJECTING:
        fail("domain", 'rejecting is "any" or "all".', rejecting.span)
    return PowerTargetIR(
        arguments["at"].value,
        _probability(arguments["minimum"], "minimum", positive=True),
        arguments["maximum_typeI"].value,
        None if nulls is None else nulls.value,
        None if rejecting is None else rejecting.value,
    )


REJECTING = ("any", "all")


def _endpoint_points(arguments: dict[str, LocatedValue], span: Span) -> EndpointPointsIR:
    items, correlation = arguments["at"].value, arguments["correlation"]
    if not 2 <= len(items) <= MAX_ENDPOINTS:
        fail("domain", f"Give between 2 and {MAX_ENDPOINTS} points.", arguments["at"].span)
    for item in items:
        if not isinstance(item.value, (RatesIR, MeanDifferenceIR)):
            fail(
                "type",
                "Each endpoint's point is binomial_rates(...) for a yes-or-no endpoint or "
                "mean_difference(...) for a measured one.",
                item.span,
            )
    if not 0 <= correlation.value < 1:
        fail("domain", "correlation must lie in [0, 1).", correlation.span)
    return EndpointPointsIR(tuple(item.value for item in items), correlation.value)


MAX_NULL_SCENARIOS = 20


def _null_scenarios(arguments: dict[str, LocatedValue], span: Span) -> NullScenariosIR:
    items = arguments["at"].value
    if not 1 <= len(items) <= MAX_NULL_SCENARIOS:
        fail(
            "domain",
            f"List between 1 and {MAX_NULL_SCENARIOS} null scenarios.",
            arguments["at"].span,
        )
    for item in items:
        if not isinstance(item.value, PlanningPointIR):
            fail(
                "type",
                "Each null scenario is a planning point at the null, such as "
                "mean_difference(value=0, sd=10).",
                item.span,
            )
        if type(item.value) is not type(items[0].value):
            fail("type", "Every null scenario must be the same kind of point.", item.span)
    return NullScenariosIR(tuple(item.value for item in items))


REESTIMATED_TESTS = ("t_test", "t_test_one_sided")


def _reestimation(arguments: dict[str, LocatedValue], span: Span) -> ReestimationIR:
    analysis = arguments["analysis"]
    test = analysis.value
    if not isinstance(test, CitedAnalysisIR) or test.method.key not in REESTIMATED_TESTS:
        fail(
            "unsupported_claim",
            "Blinded re-estimation is simulated for Student's t-test: t_test or t_test_one_sided.",
            analysis.span,
        )
    model = test.plan.model
    if model.n_control != model.n_treatment:
        fail(
            "domain",
            "Blinded re-estimation keeps the arms equal: give the analysis equal arm sizes.",
            analysis.span,
        )
    interim, largest = arguments["interim_per_arm"], arguments["max_per_arm"]
    if not 2 <= interim.value < model.n_control:
        fail(
            "domain",
            f"interim_per_arm must be at least 2 and below the planned {model.n_control} per arm.",
            interim.span,
        )
    if not model.n_control <= largest.value <= MAX_CITED_ARM:
        fail(
            "domain",
            f"max_per_arm must lie from the planned {model.n_control} to {MAX_CITED_ARM}.",
            largest.span,
        )
    difference = arguments["difference"]
    if difference.value == 0:
        fail(
            "domain",
            "The planned difference cannot be 0: no size would detect it.",
            difference.span,
        )
    power = arguments["power"]
    if not 0 < power.value < 1:
        fail("domain", "power must lie strictly between 0 and 1.", power.span)
    return ReestimationIR(test, interim.value, difference.value, power.value, largest.value)


def _reference_and_other(
    arguments: dict[str, LocatedValue],
    span: Span,
    reference: str,
    other: str,
    measure: str,
) -> tuple[Fraction, Fraction]:
    """A reference group's probability, and the other group's given directly or through the
    measure the design estimates."""
    base = _probability(arguments[reference], reference)
    given, ratio = arguments.get(other), arguments.get(measure)
    given = None if given is None or given.value is None else given
    ratio = None if ratio is None or ratio.value is None else ratio
    if (given is None) == (ratio is None):
        fail(
            "planning_point",
            f"Give {other}=... or {measure}=..., one of the two.",
            span,
        )
    if given is not None:
        return base, _probability(given, other)
    if ratio.value <= 0:
        fail("domain", f"{measure} must be positive.", ratio.span)
    if measure in ("risk_ratio", "prevalence_ratio"):
        noun = measure.removesuffix("_ratio")
        value = base * ratio.value
        if value > 1:
            fail(
                "domain",
                f"A {noun} ratio of {ratio.value} with a {noun} of {base} without exposure "
                f"gives a {noun} above 1.",
                ratio.span,
            )
        return base, value
    # The odds of exposure among cases are the odds among controls times the odds ratio.
    odds = ratio.value * base
    return base, odds / (1 - base + odds)


def _exposed_share(arguments: dict[str, LocatedValue]) -> Fraction | None:
    share = arguments.get("exposed_share")
    if share is None or share.value is None:
        return None
    if not 0 < share.value < 1:
        fail("domain", "exposed_share must lie strictly between 0 and 1.", share.span)
    return share.value


def _risks(arguments: dict[str, LocatedValue], span: Span) -> RisksIR:
    return RisksIR(
        *_reference_and_other(arguments, span, "unexposed", "exposed", "risk_ratio"),
        _exposed_share(arguments),
    )


def _design_effect(arguments: dict[str, LocatedValue]) -> Fraction | None:
    """A survey's design effect, when given: positive, and below 1 for a design, such as a
    stratified one, that is more precise than simple random sampling."""
    effect = arguments.get("design_effect")
    if effect is None or effect.value is None:
        return None
    if effect.value <= 0:
        fail("domain", "design_effect must be positive.", effect.span)
    return effect.value


def _outcome_prevalence(arguments: dict[str, LocatedValue], span: Span) -> OutcomePrevalenceIR:
    return OutcomePrevalenceIR(
        *_reference_and_other(arguments, span, "unexposed", "exposed", "prevalence_ratio"),
        _exposed_share(arguments),
        _design_effect(arguments),
    )


def _total_sizes(arguments: dict[str, LocatedValue], span: Span) -> TotalCandidatesIR:
    analysis, low, high = arguments["analysis"], arguments["min_n"], arguments["max_n"]
    if not isinstance(analysis.value, (AssociationAnalysisIR, CitedAssociationIR)):
        fail(
            "type",
            "total_sizes searches an observational study by its total: give it Fisher's test "
            "of association or a cited observational test.",
            analysis.span,
        )
    if analysis.value.plan.model.groups is not None:
        fail(
            "type",
            "total_sizes searches studies that fix only their total. This study fixes its "
            "groups: use cohort_sizes or case_control_sizes.",
            analysis.span,
        )
    if isinstance(analysis.value, CitedAssociationIR):
        fewest = len(analysis.value.covariates) + 3
        if low.value < fewest:
            fail(
                "domain",
                f"min_n must be at least {fewest}: the error needs a degree of freedom after "
                "the exposure, the intercept and the covariates.",
                low.span,
            )
        if high.value < low.value:
            fail("domain", "max_n must be at least min_n.", high.span)
        if high.value > MAX_CITED_TOTAL:
            fail("domain", f"max_n is currently limited to {MAX_CITED_TOTAL:,}.", high.span)
        return TotalCandidatesIR(analysis.value, low.value, high.value)
    if low.value < 1:
        fail("domain", "min_n must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_n must be at least min_n.", high.span)
    if high.value > MAX_TOTAL:
        fail("domain", f"Exact power is limited to {MAX_TOTAL} participants in all.", high.span)
    return TotalCandidatesIR(analysis.value, low.value, high.value)


def _exposure_prevalence(arguments: dict[str, LocatedValue], span: Span) -> ExposurePrevalenceIR:
    return ExposurePrevalenceIR(
        *_reference_and_other(arguments, span, "controls", "cases", "odds_ratio")
    )


def _discordant_pairs(arguments: dict[str, LocatedValue], span: Span) -> DiscordantPairsIR:
    share, ratio = arguments["share"], arguments["odds_ratio"]
    if not 0 < share.value <= 1:
        fail("domain", "share must lie in (0, 1]: some pairs must be discordant.", share.span)
    if ratio.value <= 0:
        fail("domain", "odds_ratio must be positive.", ratio.span)
    return DiscordantPairsIR(share.value, ratio.value)


def _incidence_rates(arguments: dict[str, LocatedValue], span: Span) -> IncidenceRatesIR:
    for name in ("rate_ratio", "exposed_time", "unexposed_time"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be positive.", arguments[name].span)
    events = arguments.get("events")
    count = None if events is None or events.value is None else events.value
    if count is not None and not 1 <= count <= MAX_EVENTS:
        fail("domain", f"events must be from 1 to {MAX_EVENTS}.", events.span)
    return IncidenceRatesIR(
        arguments["rate_ratio"].value,
        arguments["exposed_time"].value,
        arguments["unexposed_time"].value,
        count,
    )


def _count_sizes(unit: str, limit: int) -> Callable:
    exact = MatchedAnalysisIR if unit == "pairs" else RateAnalysisIR
    study = MatchedStudyIR if unit == "pairs" else PersonTimeStudyIR

    def build(arguments: dict[str, LocatedValue], span: Span) -> CountCandidatesIR:
        analysis = arguments["analysis"]
        cited = isinstance(analysis.value, CitedAssociationIR) and isinstance(
            analysis.value.plan.model, study
        )
        if not (isinstance(analysis.value, exact) or cited):
            fail(
                "type",
                f"This search counts {unit}: give it "
                + (
                    "McNemar's test or a conditional logistic regression of a matched study."
                    if unit == "pairs"
                    else "the rate test or a Poisson rate regression of a person-time cohort."
                ),
                analysis.span,
            )
        low, high = arguments[f"min_{unit}"], arguments[f"max_{unit}"]
        if low.value < 1:
            fail("domain", f"min_{unit} must be a positive integer.", low.span)
        if high.value < low.value:
            fail("domain", f"max_{unit} must be at least min_{unit}.", high.span)
        bound = MAX_CITED_TOTAL if cited else limit
        if high.value > bound:
            words = "is currently limited to" if cited else "Exact power is limited to"
            fail("domain", f"{words[0].upper()}{words[1:]} {bound:,} {unit}.", high.span)
        return CountCandidatesIR(analysis.value, low.value, high.value)

    return build


def _group_sizes(design: str) -> Callable:
    low_key, high_key, ratio_key = GROUP_SEARCH_KEYS[design]
    study = {
        "cohort": "a cohort that sampled its exposed and unexposed groups",
        "case_control": "a case-control study",
    }[design]

    def build(arguments: dict[str, LocatedValue], span: Span) -> GroupCandidatesIR:
        analysis, low, high = arguments["analysis"], arguments[low_key], arguments[high_key]
        if not isinstance(analysis.value, (AssociationAnalysisIR, CitedAssociationIR)):
            fail(
                "type",
                f"{design}_sizes searches Fisher's test of association or a cited "
                "observational test.",
                analysis.span,
            )
        model = analysis.value.plan.model
        if model.design != design:
            fail(
                "type",
                f"{design}_sizes searches the sizes of {study}; this analysis's study is "
                "another design.",
                analysis.span,
            )
        if model.groups is None:
            fail(
                "unsupported_claim",
                "This cohort fixes only its total, so how many are exposed is random; its "
                "power is not available yet. Declare exposed and unexposed when the groups "
                "are sampled separately.",
                analysis.span,
            )
        ratio = arguments.get(ratio_key)
        each = 1 if ratio is None or ratio.value is None else ratio.value
        if not 1 <= each <= MAX_RATIO:
            fail("domain", f"{ratio_key} must be from 1 to {MAX_RATIO}.", ratio.span)
        if low.value < 1:
            fail("domain", f"{low_key} must be a positive integer.", low.span)
        if high.value < low.value:
            fail("domain", f"{high_key} must be at least {low_key}.", high.span)
        cited = isinstance(analysis.value, CitedAssociationIR)
        if cited and high.value * (1 + each) > MAX_CITED_TOTAL:
            fail(
                "domain",
                f"The total is currently limited to {MAX_CITED_TOTAL:,} participants.",
                high.span,
            )
        if not cited and high.value * each > MAX_GROUP:
            fail(
                "domain",
                f"Exact power is limited to {MAX_GROUP} participants in each group.",
                high.span,
            )
        return GroupCandidatesIR(analysis.value, low.value, high.value, each)

    return build


# The planning point each observational design is planned at.
GROUP_POINTS = {
    "cohort": (RisksIR, "risks(unexposed=..., exposed=...)"),
    "case_control": (ExposurePrevalenceIR, "exposure_prevalence(controls=..., cases=...)"),
    "cross_sectional": (
        OutcomePrevalenceIR,
        "outcome_prevalence(unexposed=..., exposed=..., exposed_share=...)",
    ),
}


def _check_count_point(analysis, target: LocatedValue, where: Span) -> None:
    """McNemar's test is planned at discordant_pairs, the rate test at incidence_rates."""
    point = target.value.at
    if isinstance(analysis, MatchedAnalysisIR):
        if not isinstance(point, DiscordantPairsIR):
            fail(
                "planning_point",
                "Plan a matched study at discordant_pairs(share=..., odds_ratio=...).",
                target.span,
            )
        ratio = point.odds_ratio
    else:
        if not isinstance(point, IncidenceRatesIR):
            fail(
                "planning_point",
                "Plan a person-time cohort at incidence_rates(rate_ratio=..., exposed_time=..., "
                "unexposed_time=..., events=...).",
                target.span,
            )
        ratio = point.rate_ratio
    if ratio == 1:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({analysis.hypothesis.statement}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _check_association_point(
    analysis: AssociationAnalysisIR, target: LocatedValue, where: Span
) -> None:
    """Fisher's test of association is planned when its design fixes both groups."""
    model, point = analysis.plan.model, target.value.at
    kind, signature = GROUP_POINTS[model.design]
    if model.design == "cohort" and model.groups is None:
        signature = "risks(unexposed=..., exposed=..., exposed_share=...)"
    if not isinstance(point, kind):
        fail(
            "planning_point",
            f"Plan a {model.design.replace('_', '-')} study at {signature}.",
            target.span,
        )
    share = getattr(point, "exposed_share", None)
    if model.groups is None:
        if share is None:
            fail(
                "planning_point",
                "This study fixes only its total, so how many are exposed is random. Give "
                "exposed_share, the probability that a participant is exposed.",
                target.span,
            )
    elif share is not None:
        fail(
            "planning_point",
            "This cohort sampled its exposed and unexposed groups in fixed numbers, so the "
            "share exposed is not random. Leave exposed_share out.",
            target.span,
        )
    first, second = group_probabilities(point)
    if first == second:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null "
            f"({analysis.hypothesis.statement}). Power is assessed at an alternative; choose "
            "a point outside the null.",
            target.span,
        )


# How to write the planning point each kind of power formula takes.
POINT_SIGNATURES = {
    "mean_difference": (MeanDifferenceIR, "mean_difference(value=..., sd=...)"),
    "binomial_rates": (RatesIR, "binomial_rates(p_control=..., p_treatment=...)"),
    "hazard_ratio": (HazardRatioIR, "hazard_ratio(value=..., events=...)"),
    "exponential_survival": (
        ExponentialSurvivalIR,
        "exponential_survival(hazard_ratio=..., control_median=..., accrual=..., follow_up=...)",
    ),
    "correlation": (CorrelationIR, "correlation(value=...)"),
    "slope": (SlopeIR, "slope(value=..., exposure_sd=..., residual_sd=...)"),
}
# A test of cluster summaries also takes the intracluster correlation.
CLUSTER_POINT_SIGNATURES = {
    "mean_difference": "mean_difference(value=..., sd=..., icc=...)",
    "binomial_rates": "binomial_rates(p_control=..., p_treatment=..., icc=...)",
}
ICC_REFUSED = (
    "icc is for a test of cluster summaries, such as cluster_t_test, in a cluster-randomised "
    "trial. This analysis takes participants one by one; leave icc out."
)


def clustered_test(analysis: object) -> bool:
    """Whether the analysis is a cited test of one summary per cluster."""
    return isinstance(analysis, CitedAnalysisIR) and analysis.method.unit == "cluster"


def cited_formula(analysis: CitedAnalysisIR, point: PlanningPointIR):
    """The cited test's power formula at this kind of planning point, or None."""
    return next(
        (f for f in analysis.method.formulas if isinstance(point, POINT_SIGNATURES[f.point][0])),
        None,
    )


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
    formula = cited_formula(analysis, point)
    signature = POINT_SIGNATURES[(formula or method.power).point][1]
    if clustered_test(analysis):
        signature = CLUSTER_POINT_SIGNATURES[method.power.point]
    if formula is None:
        signatures = " or ".join(POINT_SIGNATURES[f.point][1] for f in method.formulas)
        if clustered_test(analysis):
            signatures = signature
        fail("planning_point", f"Plan {method.key} at {signatures}.", target.span)
    if clustered_test(analysis) and point.icc is None:
        fail(
            "planning_point",
            f"Plan {method.key} at {signature}: the intracluster correlation sets how much "
            "each cluster's summary varies, and so the power.",
            target.span,
        )
    if not clustered_test(analysis) and getattr(point, "icc", None) is not None:
        fail("planning_point", ICC_REFUSED, target.span)
    if not clustered_test(analysis) and getattr(point, "cluster_size_cv", None) is not None:
        fail(
            "planning_point",
            "cluster_size_cv describes the clusters of a cluster-randomised trial; leave it out.",
            target.span,
        )
    scenario = any(getattr(point, name, None) is not None for name in ("sd_treatment", "skewness"))
    if scenario and analysis.method.module != "tests.t":
        fail("planning_point", SCENARIO_REFUSED, target.span)
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
    elif isinstance(point, ExponentialSurvivalIR):
        effect = point.hazard_ratio - 1
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


# The kinds of planning point a cited observational test's formula takes: the points of that
# kind, the exposure scale it needs, and how to write one.
OBSERVATIONAL_POINTS = {
    "association_groups": (
        (RisksIR, OutcomePrevalenceIR, ExposurePrevalenceIR),
        "binary",
        "the design's own point: risks(...), outcome_prevalence(...) or exposure_prevalence(...)",
    ),
    "odds_per_sd": ((OddsPerSdIR,), "continuous", "odds_per_sd(odds_ratio=..., baseline=...)"),
    "outcome_means": (
        (OutcomeMeansIR,),
        "binary",
        "outcome_means(unexposed=..., exposed=..., sd=...)",
    ),
    "correlation": ((CorrelationIR,), "continuous", "correlation(value=...)"),
    "slope": ((SlopeIR,), "continuous", "slope(value=..., exposure_sd=..., residual_sd=...)"),
    "discordant_pairs": (
        (DiscordantPairsIR,),
        "binary",
        "discordant_pairs(share=..., odds_ratio=...)",
    ),
    "incidence_rates": (
        (IncidenceRatesIR,),
        "binary",
        "incidence_rates(rate_ratio=..., exposed_time=..., unexposed_time=..., events=...)",
    ),
}


DESIGN_EFFECT_REFUSED = (
    "design_effect is for a survey test of a complex sample, such as survey_logistic. This "
    "analysis assumes a simple random sample; leave design_effect out."
)


def observational_formula(analysis: CitedAssociationIR, point: PlanningPointIR):
    """The cited observational test's power formula at this point and exposure scale."""
    scale = analysis.plan.model.exposure_scale
    for formula in analysis.method.formulas:
        kinds, needs, _ = OBSERVATIONAL_POINTS[formula.point]
        if isinstance(point, kinds) and needs == scale:
            return formula
    return None


def _check_cited_association_point(
    analysis: CitedAssociationIR, target: LocatedValue, where: Span
) -> None:
    """A cited observational test is planned at a point its formulas take, for the study's
    exposure scale, outside the null."""
    method, point = analysis.method, target.value.at
    if not method.formulas:
        others = ", ".join(m.key for m in OBSERVATIONAL_METHODS.values() if m.formulas)
        fail(
            "no_power_formula",
            f"{method.key} has no power formula yet, so its power cannot be calculated. Cited "
            f"observational tests with one: {others}.",
            where,
        )
    scale = analysis.plan.model.exposure_scale
    fitting = [f for f in method.formulas if OBSERVATIONAL_POINTS[f.point][1] == scale]
    if not fitting:
        scales = " or ".join(sorted({OBSERVATIONAL_POINTS[f.point][1] for f in method.formulas}))
        fail(
            "planning_point",
            f"{method.key}'s power formulas are for a {scales} exposure; this study declares a "
            f"{scale} exposure.",
            target.span,
        )
    formula = observational_formula(analysis, point)
    if formula is None:
        signatures = " or ".join(OBSERVATIONAL_POINTS[f.point][2] for f in fitting)
        fail("planning_point", f"Plan {method.key} at {signatures}.", target.span)
    model = analysis.plan.model
    if (
        method.module == "tests.survey"
        and model.survey != "simple_random"
        and getattr(point, "design_effect", None) is None
    ):
        fail(
            "planning_point",
            f"This survey samples by {model.survey} design, so its power depends on the design "
            "effect: give design_effect=..., the variance of the exposure's estimate over that "
            "of a simple random sample of the same size.",
            target.span,
        )
    if formula.point == "association_groups":
        _check_association_point(analysis, target, where)
        if method.key == "modified_poisson" and 0 in group_probabilities(point):
            fail(
                "domain",
                "A risk or prevalence ratio needs the outcome in both groups: give "
                "probabilities above 0.",
                target.span,
            )
        return
    if formula.point == "outcome_means":
        share = point.exposed_share
        if model.groups is None and share is None:
            fail(
                "planning_point",
                "This study fixes only its total, so how many are exposed is random. Give "
                "exposed_share, the probability that a participant is exposed.",
                target.span,
            )
        if model.groups is not None and share is not None:
            fail(
                "planning_point",
                "This cohort sampled its exposed and unexposed groups in fixed numbers, so the "
                "share exposed is not random. Leave exposed_share out.",
                target.span,
            )
    effect = {
        "outcome_means": lambda: point.exposed - point.unexposed,
        "odds_per_sd": lambda: point.odds_ratio - 1,
        "correlation": lambda: point.value,
        "slope": lambda: point.value,
        "discordant_pairs": lambda: point.odds_ratio - 1,
        "incidence_rates": lambda: point.rate_ratio - 1,
    }[formula.point]()
    if effect == 0:
        fail(
            "alternative_in_null",
            f"The planning point satisfies the analysis's null ({analysis.hypothesis.statement}). "
            "Power is assessed at an alternative; choose a point outside the null.",
            target.span,
        )


def _check_point(analysis: PlannableIR, target: LocatedValue, where: Span) -> None:
    """The planning point must belong to the analysis's parameter space, outside its null."""
    point = target.value.at
    if isinstance(analysis, ReestimationIR):
        _check_reestimation_point(analysis, target)
        _check_cited_point(analysis.analysis, target, where)
        return
    if getattr(target.value, "nulls", None) is not None:
        fail(
            "planning_point",
            "null_scenarios are for a design whose Type I error is judged by simulation, such "
            "as blinded_reestimation(...). This analysis's level is proved or cited; leave "
            "nulls out.",
            target.span,
        )
    family = isinstance(analysis, FamilyLikeIR) and not isinstance(analysis, SequentialIR)
    if family:
        _check_family_point(analysis, target)
        return
    if getattr(target.value, "rejecting", None) is not None:
        fail(
            "planning_point",
            "rejecting is for a family of tests: whether its power means rejecting any "
            "endpoint or all of them. Leave it out here.",
            target.span,
        )
    if isinstance(point, EndpointPointsIR):
        fail(
            "planning_point",
            "endpoint_points(...) is for a family of tests; give this analysis one point.",
            target.span,
        )
    if isinstance(analysis, SequentialIR):
        _check_sequential(analysis, where)
        if exact_looks(analysis):
            _check_point(analysis.final, target, where)
        else:
            _check_cited_point(analysis.final, target, where)
        return
    if isinstance(analysis, CitedAnalysisIR):
        _check_cited_point(analysis, target, where)
        return
    if any(getattr(point, name, None) is not None for name in ("icc", "cluster_size_cv")):
        fail("planning_point", ICC_REFUSED, target.span)
    if getattr(point, "sd_treatment", None) is not None or (
        isinstance(point, MeanDifferenceIR) and point.skewness is not None
    ):
        fail("planning_point", SCENARIO_REFUSED, target.span)
    if any(getattr(point, name, None) is not None for name in ("skewness", "exposure_skewness")):
        _check_skewed_point(analysis, target)
    survey = isinstance(analysis, CitedAssociationIR) and analysis.method.module == "tests.survey"
    if getattr(point, "design_effect", None) is not None and not survey:
        fail("planning_point", DESIGN_EFFECT_REFUSED, target.span)
    if isinstance(analysis, CitedAssociationIR):
        _check_cited_association_point(analysis, target, where)
        return
    if isinstance(analysis, AssociationAnalysisIR):
        _check_association_point(analysis, target, where)
        return
    if isinstance(analysis, (MatchedAnalysisIR, RateAnalysisIR)):
        _check_count_point(analysis, target, where)
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


def _residual_df(analysis: CitedAssociationIR, n: int) -> int:
    """Degrees of freedom left for a regression's error: n less the slope, the intercept and
    the covariates."""
    return n - len(analysis.covariates) - 2


SIMULATION_SCENARIO = ("icc", "cluster_size_cv", "sd_treatment", "skewness")


def _check_reestimation_point(design: ReestimationIR, target: LocatedValue) -> None:
    """Normal outcomes with a common SD, and the nulls at which Type I error is judged."""
    point, nulls = target.value.at, target.value.nulls
    plain = (
        "Blinded re-estimation is simulated for normal outcomes with a common SD: give "
        "mean_difference(value=..., sd=...)"
    )
    if not isinstance(point, MeanDifferenceIR) or any(
        getattr(point, name, None) is not None for name in SIMULATION_SCENARIO
    ):
        fail("planning_point", plain + ".", target.span)
    if nulls is None:
        fail(
            "planning_point",
            "The Type I error of a re-estimated design is not proved. List the nulls at which "
            "to judge it: power_target(..., nulls=null_scenarios(at=[mean_difference(value="
            f"{design.analysis.hypothesis.value}, sd=...), ...])).",
            target.span,
        )
    for null in nulls.points:
        if not isinstance(null, MeanDifferenceIR) or any(
            getattr(null, name, None) is not None for name in SIMULATION_SCENARIO
        ):
            fail("planning_point", plain + " for each null scenario.", target.span)
        if null.value != design.analysis.hypothesis.value:
            fail(
                "planning_point",
                f"A null scenario lies on the null: its difference must be "
                f"{design.analysis.hypothesis.value}, not {null.value}.",
                target.span,
            )


FAMILY_MODES = {
    "family": "bonferroni",
    "fixed_sequence": "fixed_sequence",
    "graphical": "graphical",
}


def family_procedure(family: FamilyLikeIR) -> str:
    """How a family rejects: each member at its own level, in order, or along a graph."""
    return "bonferroni" if isinstance(family, FamilyIR) else FAMILY_MODES[family.mode]


def endpoint_kind(analysis) -> str | None:
    """A member simulated in a family: "binary" for Fisher's test, "measured" for a t-test."""
    if isinstance(analysis, AnalysisIR) and analysis.alternative in ("two_sided", "greater"):
        return "binary"
    if isinstance(analysis, CitedAnalysisIR) and analysis.method.module == "tests.t":
        return "measured"
    return None


def _outside_null(analysis, point) -> bool:
    if isinstance(point, RatesIR):
        if analysis.alternative == "greater":
            return point.p_treatment > point.p_control
        return point.p_treatment != point.p_control
    null = analysis.hypothesis
    favours = NULL_FORMS[null.predicate][1].favours
    if favours == "higher":
        return point.value > null.value
    if favours == "lower":
        return point.value < null.value
    return point.value != null.value


def _check_family_point(family: FamilyLikeIR, target: LocatedValue) -> None:
    """One point per member, of its kind; any or all; shared participants when correlated."""
    point, members = target.value.at, family.analyses
    if not isinstance(family, FamilyIR) and family.mode not in FAMILY_MODES:
        fail("unsupported_claim", "This kind of family is not simulated yet.", target.span)
    if not isinstance(point, EndpointPointsIR):
        fail(
            "planning_point",
            "A family's power is planned at endpoint_points(at=[one point per member, in "
            "order], correlation=...).",
            target.span,
        )
    if len(point.points) != len(members):
        fail(
            "planning_point",
            f"The family has {len(members)} members, so give {len(members)} points, in order.",
            target.span,
        )
    if target.value.rejecting is None:
        fail(
            "planning_point",
            "Say whether the family's power means rejecting any endpoint or all of them: "
            'power_target(..., rejecting="any") or rejecting="all".',
            target.span,
        )
    for (name, analysis), member_point in zip(members, point.points, strict=True):
        kind = endpoint_kind(analysis)
        if kind is None:
            fail(
                "unsupported_claim",
                f"{name}: a family's power is simulated for members that are Fisher's test or "
                "the t-tests; this member is not simulated yet.",
                target.span,
            )
        wanted = RatesIR if kind == "binary" else MeanDifferenceIR
        scenario = any(
            getattr(member_point, field, None) is not None for field in SIMULATION_SCENARIO
        )
        if not isinstance(member_point, wanted) or scenario:
            words = "binomial_rates(...)" if kind == "binary" else "mean_difference(value, sd)"
            fail("planning_point", f"{name} is planned at {words}.", target.span)
    if point.correlation > 0:
        sizes = {(a.plan.model.n_control, a.plan.model.n_treatment) for _, a in members}
        if len(sizes) > 1:
            fail(
                "planning_point",
                "Correlated endpoints are measured on the same participants: give every "
                "member the same arm sizes, or correlation=0.",
                target.span,
            )
    if not any(_outside_null(a, p) for (_, a), p in zip(members, point.points, strict=True)):
        fail(
            "planning_point",
            "At least one endpoint's point must lie outside its null; otherwise there is no "
            "power to plan.",
            target.span,
        )


def exact_looks(analysis: SequentialIR) -> bool:
    """Whether a design's looks are Fisher's test, whose power is summed exactly."""
    look = analysis.final
    return isinstance(look, AnalysisIR) and look.alternative in ("two_sided", "greater")


MAX_LOOK_ARM = 500  # participants per arm at the last look, for the exact sum


def _check_sequential(analysis: SequentialIR, where: Span) -> None:
    """A design with looks is planned exactly for Fisher's test, and by simulation for tests
    with a simulation model for looks."""
    look = analysis.final
    if exact_looks(analysis):
        model = look.plan.model
        if max(model.n_control, model.n_treatment) > MAX_LOOK_ARM:
            fail(
                "domain",
                f"The exact power of Fisher's test at looks is summed up to {MAX_LOOK_ARM} per "
                "arm at the last look.",
                where,
            )
        return
    model = getattr(getattr(look, "method", None), "simulation", None)
    if not isinstance(look, CitedAnalysisIR) or model is None or model.looks is None:
        key = getattr(getattr(look, "method", None), "key", None) or _test_key(look)
        fail(
            "unsupported_claim",
            f"The power of a design with looks is exact for Fisher's test and simulated for "
            f"the t-tests; {key} looks are not supported yet.",
            where,
        )


def _check_planned_size(analysis: PlannableIR, where: Span, point=None) -> None:
    """The declared study's size, for exact power at it; a search checks its own bounds."""
    if (
        isinstance(analysis, CitedAssociationIR)
        and analysis.method.module != "tests.survey"
        and observational_formula(analysis, point).point
        in ("correlation", "slope", "outcome_means")
        and _residual_df(analysis, analysis.plan.model.total) < 1
    ):
        fail(
            "domain",
            f"{analysis.plan.model.total} participants leave no degrees of freedom for the "
            f"error after the exposure, the intercept and {len(analysis.covariates)} covariates.",
            where,
        )
    if isinstance(analysis, MatchedAnalysisIR) and analysis.plan.model.pairs > MAX_PLANNED_PAIRS:
        fail("domain", f"Exact power is limited to {MAX_PLANNED_PAIRS} pairs.", where)
    if not isinstance(analysis, AssociationAnalysisIR):
        return
    model = analysis.plan.model
    if model.groups is None and model.n > MAX_TOTAL:
        fail(
            "domain",
            f"Exact power is limited to {MAX_TOTAL} participants in all when only the total "
            "is fixed.",
            where,
        )
    if model.groups is not None and max(model.groups) > MAX_GROUP:
        fail("domain", f"Exact power is limited to {MAX_GROUP} participants in each group.", where)


def _design_name(model: object) -> str | None:
    if isinstance(model, OneArmModelIR):
        return "one_arm"
    if isinstance(model, ModelIR):
        return "two_arm"
    if isinstance(model, ObservationalStudyIR):
        return model.design
    return None


def _planned_interval(arguments: dict[str, LocatedValue], span: Span) -> PlannedIntervalIR:
    model, measure = arguments["model"], arguments["measure"]
    method_arg, group_arg = arguments.get("method"), arguments.get("group")
    method = "exact" if method_arg is None or method_arg.value is None else method_arg.value
    group = None if group_arg is None or group_arg.value is None else group_arg.value
    design = _design_name(model.value)
    if design is None:
        fail(
            "type",
            "planned_interval takes a one-arm or two-arm binomial model, or an observational "
            "study.",
            model.span,
        )
    fitting = [key for key, (_, designs) in PLANNED_MEASURES.items() if design in designs]
    if measure.value not in PLANNED_MEASURES:
        fail(
            "domain",
            f"measure must be one of {', '.join(fitting)} for this design.",
            measure.span,
        )
    kind, designs = PLANNED_MEASURES[measure.value]
    if design not in designs:
        reason = (
            proportion_not_estimable(measure.value, design)
            if kind == "proportion" and design != "one_arm"
            else not_estimable(measure.value, design)
            if measure.value in MEASURES
            else None
        )
        fail(
            "not_estimable",
            f"{measure.value}: "
            + (reason or f"a {design.replace('_', '-')} design does not estimate it.")
            + f" This design estimates {', '.join(fitting) or 'none of them'}.",
            measure.span,
        )
    if method not in PRECISION_METHODS:
        fail("domain", 'method must be "exact" or "normal".', method_arg.span)
    if design == "two_arm":
        check_design(model.value, BINOMIAL_ASSUMPTIONS, "planned_interval", model.span)
    observed = model.value if isinstance(model.value, ObservationalStudyIR) else None
    if observed is not None:
        for which, scale in (
            ("outcome", observed.outcome_scale),
            ("exposure", observed.exposure_scale),
        ):
            if scale != "binary" and (which == "outcome" or kind != "proportion"):
                fail(
                    "type",
                    f"planned_interval({measure.value}) needs a yes-or-no {which}; this study "
                    f"declares a continuous {which}.",
                    model.span,
                )
        if method == "exact" and observed.survey != "simple_random":
            fail(
                "complex_sample",
                f"Exact intervals assume a simple random sample; this survey declares "
                f'{observed.survey} sampling. Use method="normal", with design_effect on the '
                "planning point.",
                model.span,
            )
    needs_group = kind == "proportion" and observed is not None and observed.groups is not None
    if needs_group and group not in ("exposed", "unexposed"):
        fail(
            "domain",
            "This cohort sampled exposed and unexposed groups separately, so say which: "
            'group="exposed" or group="unexposed".',
            span,
        )
    if not needs_group and group is not None:
        fail("domain", "This interval has no group to choose; leave group out.", group_arg.span)
    return PlannedIntervalIR(model.value, measure.value, method, group)


def _single_proportion(arguments: dict[str, LocatedValue], span: Span) -> SingleProportionIR:
    value = arguments["value"]
    if not 0 < value.value < 1:
        fail("domain", "value must lie strictly between 0 and 1.", value.span)
    population = arguments.get("population_size")
    size = None if population is None or population.value is None else population.value
    if size is not None and size < 2:
        fail("domain", "population_size must be at least 2.", population.span)
    return SingleProportionIR(value.value, _design_effect(arguments), size)


def _precision_target(arguments: dict[str, LocatedValue], span: Span) -> PrecisionTargetIR:
    level, assurance = arguments["level"], arguments.get("assurance")
    absolute, relative = arguments.get("margin_of_error"), arguments.get("relative_margin_of_error")
    given = [a for a in (absolute, relative) if a is not None and a.value is not None]
    if len(given) != 1:
        fail(
            "domain",
            "Give one of margin_of_error, half the interval's width, or "
            "relative_margin_of_error, a fraction of the planning value.",
            span,
        )
    if given[0].value <= 0:
        fail("domain", "The margin of error must be positive.", given[0].span)
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    chance = None if assurance is None or assurance.value is None else assurance.value
    if chance is not None and not 0 < chance < 1:
        fail("domain", "assurance must lie strictly between 0 and 1.", assurance.span)
    is_absolute = absolute is not None and absolute.value is not None
    return PrecisionTargetIR(
        arguments["at"].value,
        level.value,
        given[0].value if is_absolute else None,
        None if is_absolute else given[0].value,
        chance,
    )


def _two_group_sizes(interval: PlannedIntervalIR) -> bool:
    """Whether a search of this interval varies two fixed groups, the first with ratio of
    the second for each."""
    model = interval.model
    if isinstance(model, ModelIR):
        return True
    kind = PLANNED_MEASURES[interval.measure][0]
    return (
        isinstance(model, ObservationalStudyIR)
        and model.groups is not None
        and kind in ("difference", "ratio", "odds")
    )


def _interval_sizes(arguments: dict[str, LocatedValue], span: Span) -> IntervalCandidatesIR:
    interval, low, high = arguments["interval"], arguments["min_size"], arguments["max_size"]
    if not isinstance(interval.value, PlannedIntervalIR):
        fail("type", "interval_sizes searches a planned_interval(...).", interval.span)
    ratio = arguments.get("ratio")
    each = 1 if ratio is None or ratio.value is None else ratio.value
    if ratio is not None and ratio.value is not None and not _two_group_sizes(interval.value):
        fail(
            "domain",
            "ratio is for a design that samples two groups in fixed numbers; this search "
            "varies one size.",
            ratio.span,
        )
    if not 1 <= each <= MAX_RATIO:
        fail("domain", f"ratio must be from 1 to {MAX_RATIO}.", ratio.span)
    if low.value < 1:
        fail("domain", "min_size must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_size must be at least min_size.", high.span)
    exact_pairs = (
        interval.value.method == "exact" and interval.value.measure == "conditional_odds_ratio"
    )
    limit = MAX_EXACT_PAIRS if exact_pairs else MAX_PRECISION_SIZE
    if high.value * (1 + each if _two_group_sizes(interval.value) else 1) > limit:
        fail("domain", f"The search is currently limited to {limit:,} in all.", high.span)
    return IntervalCandidatesIR(interval.value, low.value, high.value, each)


def _check_precision(
    interval: PlannedIntervalIR, target: LocatedValue, where: Span, search: bool
) -> None:
    """A planned interval is planned at the point its measure takes, with a precision target
    its method can reach."""
    goal = target.value
    if not isinstance(goal, PrecisionTargetIR):
        fail(
            "planning_point",
            "A planned interval takes precision_target(at=..., level=..., margin_of_error=...), "
            "not a power target.",
            target.span,
        )
    point, model, measure = goal.at, interval.model, interval.measure
    kind = PLANNED_MEASURES[measure][0]
    exact = interval.method == "exact"
    if kind == "proportion":
        wanted = (
            (SingleProportionIR, RateIR)
            if isinstance(model, OneArmModelIR)
            else (SingleProportionIR,)
        )
        if not isinstance(point, wanted):
            fail("planning_point", f"Plan {measure} at proportion(value=...).", target.span)
        value = point.value
    elif kind == "difference" and isinstance(model, ModelIR):
        if not isinstance(point, RatesIR) or point.icc is not None:
            fail(
                "planning_point",
                "Plan the difference at binomial_rates(p_control=..., p_treatment=...).",
                target.span,
            )
        value = point.p_treatment - point.p_control
    elif kind in ("difference", "ratio", "odds"):
        wanted, signature = GROUP_POINTS[model.design]
        if model.design == "cohort" and model.groups is None:
            signature = "risks(unexposed=..., exposed=..., exposed_share=...)"
        if not isinstance(point, wanted):
            fail(
                "planning_point",
                f"Plan a {model.design.replace('_', '-')} study's {measure} at {signature}.",
                target.span,
            )
        share = getattr(point, "exposed_share", None)
        if model.groups is None and share is None:
            fail(
                "planning_point",
                "This study fixes only its total, so how many are exposed is random. Give "
                "exposed_share, the probability that a participant is exposed.",
                target.span,
            )
        if model.groups is not None and share is not None:
            fail(
                "planning_point",
                "This cohort sampled its exposed and unexposed groups in fixed numbers; leave "
                "exposed_share out.",
                target.span,
            )
        first, second = group_probabilities(point)
        if kind == "ratio" and 0 in (first, second):
            fail("domain", f"A {measure} needs both probabilities above 0.", target.span)
        if kind == "odds" and not (0 < first < 1 and 0 < second < 1):
            fail(
                "domain",
                "An odds ratio needs both probabilities strictly between 0 and 1.",
                target.span,
            )
        value = (
            second - first
            if kind == "difference"
            else (
                second / first
                if kind == "ratio"
                else (second / (1 - second)) / (first / (1 - first))
            )
        )
    elif kind == "matched":
        if not isinstance(point, DiscordantPairsIR):
            fail(
                "planning_point",
                "Plan the conditional odds ratio at discordant_pairs(share=..., odds_ratio=...).",
                target.span,
            )
        value = point.odds_ratio
    else:
        if not isinstance(point, IncidenceRatesIR):
            fail(
                "planning_point",
                "Plan the rate ratio at incidence_rates(rate_ratio=..., exposed_time=..., "
                "unexposed_time=..., events=...).",
                target.span,
            )
        if search and point.events is not None:
            fail(
                "planning_point",
                "interval_sizes searches the events; leave events out of incidence_rates.",
                target.span,
            )
        if not search and point.events is None:
            fail(
                "planning_point",
                "The rate ratio's interval is given the total events: give events=..., or "
                "search them with interval_sizes.",
                target.span,
            )
        value = point.rate_ratio
    if goal.relative is not None:
        if kind in ("proportion", "difference") and value == 0:
            fail(
                "planning_point",
                "A relative margin of error is a fraction of the planning value, which is 0 "
                "here; give margin_of_error instead.",
                target.span,
            )
        if kind not in ("proportion", "difference") and goal.relative >= 1:
            fail(
                "domain",
                "For a ratio, the relative margin of error r asks that the lower limit be at "
                "least (1 - r) times the estimate, so r must be below 1.",
                target.span,
            )
    effect = getattr(point, "design_effect", None)
    population = getattr(point, "population_size", None)
    survey = isinstance(model, ObservationalStudyIR) and model.survey != "simple_random"
    if exact and (effect is not None or population is not None):
        fail(
            "planning_point",
            "design_effect and population_size describe a survey's normal interval; the exact "
            'interval assumes a simple random sample. Use method="normal" for them.',
            target.span,
        )
    if survey and effect is None:
        fail(
            "planning_point",
            f"This survey samples by {model.survey} design: give design_effect=... on the "
            "planning point.",
            target.span,
        )
    if population is not None and not search and isinstance(model, ObservationalStudyIR):
        if population <= model.total:
            fail(
                "domain",
                f"population_size must exceed the {model.total} sampled.",
                target.span,
            )


def _meets(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis = arguments["analysis"]
    if isinstance(analysis.value, PlannedIntervalIR) or isinstance(
        arguments["target"].value, PrecisionTargetIR
    ):
        if not isinstance(analysis.value, PlannedIntervalIR):
            fail(
                "type",
                "precision_target is for planned_interval(...): a test is planned with "
                "power_target.",
                analysis.span,
            )
        _check_precision(analysis.value, arguments["target"], analysis.span, search=False)
        return ClaimIR(
            "meets",
            FeasibilityIR(analysis.value, arguments["target"].value),
            analysis.name or "<expression>",
        )
    _check_point(analysis.value, arguments["target"], analysis.span)
    _check_planned_size(analysis.value, analysis.span, arguments["target"].value.at)
    point = arguments["target"].value.at
    if isinstance(point, IncidenceRatesIR) and point.events is None:
        fail(
            "planning_point",
            "The rate test's power is given the total number of events. Give events=... in "
            "incidence_rates, or search the events with event_counts.",
            arguments["target"].span,
        )
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


def _not_clustered(analysis: LocatedValue) -> None:
    """A test of cluster summaries is sized in clusters, not participants."""
    if clustered_test(analysis.value):
        fail(
            "unsupported_claim",
            f"{analysis.value.method.key} takes one summary per cluster, so it is sized in "
            "clusters: search cluster_counts(...) for the number of clusters per arm, or "
            "cluster_sizes(...) for the participants in each cluster.",
            analysis.span,
        )


def _cluster_analysis(analysis: LocatedValue, search: str) -> CitedAnalysisIR:
    if not clustered_test(analysis.value):
        fail(
            "unsupported_claim",
            f"{search} searches a test of cluster summaries, such as cluster_t_test, in a "
            "cluster-randomised trial. Use equal_arm_sizes(...) for an analysis of "
            "participants.",
            analysis.span,
        )
    return analysis.value


def _cluster_counts(arguments: dict[str, LocatedValue], span: Span) -> ClusterCandidatesIR:
    analysis = _cluster_analysis(arguments["analysis"], "cluster_counts")
    size, low, high = (arguments[k] for k in ("cluster_size", "min_per_arm", "max_per_arm"))
    if not 1 <= size.value <= MAX_CLUSTER_SIZE:
        fail("domain", f"cluster_size must be between 1 and {MAX_CLUSTER_SIZE:,}.", size.span)
    fewest = analysis.method.min_per_arm
    if low.value < fewest:
        fail(
            "domain",
            f"{analysis.method.key} needs at least {fewest} clusters per arm, so min_per_arm "
            f"must be at least {fewest}.",
            low.span,
        )
    if high.value < low.value:
        fail("domain", "max_per_arm must be at least min_per_arm.", high.span)
    if high.value > MAX_CLUSTERS:
        fail("domain", f"max_per_arm is currently limited to {MAX_CLUSTERS:,} clusters.", high.span)
    return ClusterCandidatesIR(analysis, low.value, high.value, size.value)


def _cluster_sizes(arguments: dict[str, LocatedValue], span: Span) -> ClusterCandidatesIR:
    analysis = _cluster_analysis(arguments["analysis"], "cluster_sizes")
    low, high = arguments["min_size"], arguments["max_size"]
    if low.value < 1:
        fail("domain", "min_size must be a positive integer.", low.span)
    if high.value < low.value:
        fail("domain", "max_size must be at least min_size.", high.span)
    if high.value > MAX_CLUSTER_SIZE:
        fail(
            "domain",
            f"max_size is currently limited to {MAX_CLUSTER_SIZE:,} participants per cluster.",
            high.span,
        )
    return ClusterCandidatesIR(analysis, low.value, high.value)


def _candidates(arguments: dict[str, LocatedValue], span: Span) -> CandidatesIR:
    _not_clustered(arguments["analysis"])
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
    _not_clustered(arguments["analysis"])
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
        goal = arguments["target"].value
        if isinstance(candidates.value, IntervalCandidatesIR) or isinstance(
            goal, PrecisionTargetIR
        ):
            if not isinstance(candidates.value, IntervalCandidatesIR):
                fail(
                    "type",
                    "precision_target is searched with interval_sizes(interval=...).",
                    candidates.span,
                )
            if minimal and getattr(goal, "assurance", None) is not None:
                fail(
                    "unsupported_claim",
                    "With an assurance, the chance of reaching the margin rises with the size "
                    "only roughly, since counts are whole numbers, so a smallest-size claim is "
                    "not offered. Use sample_size(...) for a sufficient size.",
                    candidates.span,
                )
            _check_precision(
                candidates.value.interval, arguments["target"], candidates.span, search=True
            )
            return ClaimIR(
                "sample_size",
                SizingIR(candidates.value, goal, minimal),
                candidates.name or "<expression>",
            )
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
        if (
            minimal
            and isinstance(candidates.value, TotalCandidatesIR)
            and isinstance(candidates.value.analysis, AssociationAnalysisIR)
        ):
            fail(
                "unsupported_claim",
                "With only the total fixed, each candidate's check covers every number "
                "exposed, so a smallest-size claim is not supported. Use sample_size(...) to "
                "certify a sufficient total.",
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
        point = arguments["target"].value.at
        if isinstance(point, IncidenceRatesIR) and point.events is not None:
            fail(
                "planning_point",
                "event_counts searches the total number of events; leave events out of "
                "incidence_rates.",
                arguments["target"].span,
            )
        if isinstance(arguments["target"].value.at, HazardRatioIR):
            fail(
                "unsupported_claim",
                "At hazard_ratio(...), log-rank power depends on the number of events, not on "
                "the arm sizes, so a search over arm sizes does not apply. Plan at "
                "exponential_survival(...), whose times give the events each size expects, or "
                "calculate meets(...) for a number of events.",
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
    if claim.value.kind in ("meets", "sample_size"):
        kind = kind_of(planned_analysis(claim.value.subject))
        if kind.refuse_verify is not None:
            fail("unsupported_claim", kind.refuse_verify, claim.span)
    return claim.value


def simulation_settings(arguments: dict[str, LocatedValue]) -> SimulationIR:
    """The seed and number of runs of simulate(...), with the number of runs checked."""
    seed, runs = arguments["seed"], arguments["runs"]
    if seed.value < 0:
        fail("domain", "seed must be a whole number of at least 0.", seed.span)
    count = DEFAULT_RUNS if runs.value is None else runs.value
    if not MIN_RUNS <= count <= MAX_RUNS:
        fail(
            "domain",
            f"runs must be from {MIN_RUNS:,} to {MAX_RUNS:,}; the default is {DEFAULT_RUNS:,}.",
            runs.span,
        )
    return SimulationIR(seed.value, count)


def _simulation(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    """Power by simulation, for planning claims about tests that have a simulation model."""
    claim = arguments["claim"]
    if claim.value.kind not in ("meets", "sample_size"):
        fail(
            "type",
            "Only planning claims are simulated: meets(...) and sample-size searches. "
            "Use verify(claim) for guarantees and calculate(claim) for results.",
            claim.span,
        )
    subject = claim.value.subject
    analysis = planned_analysis(subject)
    kind = kind_of(analysis)
    if kind.check_simulate is None:
        fail("unsupported_claim", kind.refuse_simulate, claim.span)
    return resolve(kind.check_simulate)(analysis, subject, arguments, claim)


def check_cited_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A cited two-arm test is simulated by its method's model, at the model's point."""
    method = analysis.method
    if method.simulation is None:
        others = ", ".join(m.key for m in methods_for(method.outcome) if m.simulation) or "none"
        fail(
            "no_simulation_model",
            f"{method.key} has no simulation model yet. Tests for this outcome with one: "
            f"{others}." + (" calculate(...) gives its approximate power." if method.power else ""),
            claim.span,
        )
    kind, signature = POINT_SIGNATURES[method.simulation.point]
    if not isinstance(subject.target.at, kind):
        fail("planning_point", f"Simulate {method.key} at {signature}.", claim.span)
    if not clustered_test(analysis) and getattr(subject.target.at, "icc", None) is not None:
        fail("planning_point", ICC_REFUSED, claim.span)
    settings = simulation_settings(arguments)
    if clustered_test(analysis) and method.outcome == "binary":
        if isinstance(subject, SizingIR):
            largest = max(size for _, sizes in subject.candidates.designs() for size in sizes)
        else:
            model = analysis.plan.model
            largest = max(
                Fraction(model.n_control, model.assignment.clusters_control),
                Fraction(model.n_treatment, model.assignment.clusters_treatment),
            )
        if largest > MAX_SIMULATED_CLUSTER:
            fail(
                "domain",
                f"Simulating cluster proportions draws every participant, so clusters are "
                f"limited to {MAX_SIMULATED_CLUSTER:,} participants here.",
                claim.span,
            )
    if isinstance(subject, SizingIR):
        space = subject.candidates
        candidates = (
            space.high - space.low + 1
            if isinstance(space, ClusterCandidatesIR)
            else space.max_per_arm - space.min_per_arm + 1
        )
        if candidates * settings.runs > MAX_SIMULATED_STUDIES:
            fail(
                "domain",
                f"Searching {candidates:,} sizes with {settings.runs:,} runs each could "
                f"simulate more than {MAX_SIMULATED_STUDIES:,} studies. Narrow the range or "
                "use fewer runs.",
                claim.span,
            )
    if participant_draws(subject.target.at):
        # A search simulates each size for power, then confirms the one that passes with
        # power and Type I runs; a claim at the declared sizes runs power and Type I.
        if isinstance(subject, SizingIR):
            space = subject.candidates
            sizes = [s + space.ratio * s for s in range(space.min_per_arm, space.max_per_arm + 1)]
            drawn = sum(sizes) + 2 * sizes[-1]
        else:
            drawn = 2 * (analysis.plan.model.n_control + analysis.plan.model.n_treatment)
        if drawn * settings.runs > MAX_SIMULATED_PARTICIPANTS:
            fail(
                "domain",
                "This scenario is simulated one participant at a time, and this could draw "
                f"more than {MAX_SIMULATED_PARTICIPANTS:,} participants. Narrow the range or "
                "use fewer runs.",
                claim.span,
            )
    return claim.value


def check_family_simulation(family, subject, arguments, claim) -> ClaimIR:
    """A family is simulated as declared; correlated endpoints draw every participant."""
    if isinstance(subject, SizingIR):
        fail(
            "unsupported_claim",
            "A family is simulated as declared; searching its sizes is not supported yet.",
            claim.span,
        )
    settings = simulation_settings(arguments)
    point = subject.target.at
    if point.correlation > 0:
        model = family.analyses[0][1].plan.model
        drawn = 2 * (model.n_control + model.n_treatment) * len(point.points)
        if drawn * settings.runs > MAX_SIMULATED_PARTICIPANTS:
            fail(
                "domain",
                "Correlated endpoints are simulated one participant at a time, and this could "
                f"draw more than {MAX_SIMULATED_PARTICIPANTS:,} outcomes. Use fewer runs.",
                claim.span,
            )
    return claim.value


def check_looks_calculation(claim: LocatedValue) -> None:
    """Fisher's test at looks is calculated as declared; t-test looks are simulated."""
    analysis = planned_analysis(claim.value.subject)
    if not exact_looks(analysis):
        fail(
            "unsupported_claim",
            "A design with t-test looks has no power formula. Use simulate(...), which runs "
            "the trial look by look.",
            claim.span,
        )
    if claim.value.kind == "sample_size":
        fail(
            "unsupported_claim",
            "A design with looks is calculated as declared; searching its sizes is not "
            "supported yet.",
            claim.span,
        )


def check_reestimation_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A re-estimated design chooses its own size, so it is simulated as declared."""
    if isinstance(subject, SizingIR):
        fail(
            "unsupported_claim",
            "A re-estimated design chooses its own size; simulate meets(...) for it.",
            claim.span,
        )
    simulation_settings(arguments)
    return claim.value


def is_margin_test(analysis: object) -> bool:
    """An exact two-arm test with a margin: the difference test."""
    return isinstance(analysis, AnalysisIR) and analysis.alternative == "margin"


def check_looks_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A design with looks is simulated as declared, look by look."""
    if exact_looks(analysis):
        fail(
            "unsupported_claim",
            "Fisher's test at looks has exact power, so there is nothing to simulate: "
            "calculate(...) sums it over every path of counts.",
            claim.span,
        )
    if isinstance(subject, SizingIR):
        fail(
            "unsupported_claim",
            "A design with looks is simulated as declared; searching its sizes is not "
            "supported yet. Declare the looks and simulate meets(...).",
            claim.span,
        )
    settings = simulation_settings(arguments)
    if participant_draws(subject.target.at):
        model = analysis.final.plan.model
        if 2 * (model.n_control + model.n_treatment) * settings.runs > MAX_SIMULATED_PARTICIPANTS:
            fail(
                "domain",
                "This scenario is simulated one participant at a time, and this could draw more "
                f"than {MAX_SIMULATED_PARTICIPANTS:,} participants. Use fewer runs.",
                claim.span,
            )
    return claim.value


def check_association_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A cited test of an observational study is simulated in a scenario its formula cannot
    describe: skewed data, for the tests of a correlation or a slope."""
    method = analysis.method
    if method.simulation is None:
        fail(
            "no_simulation_model",
            f"{method.key} has no simulation model yet. calculate(...) gives its power.",
            claim.span,
        )
    kind, signature = POINT_SIGNATURES[method.simulation.point]
    if not isinstance(subject.target.at, kind):
        fail("planning_point", f"Simulate {method.key} at {signature}.", claim.span)
    if not skewed(subject.target.at):
        fail(
            "unsupported_claim",
            "With normal data this test's power is exact, so there is nothing to simulate: "
            "calculate(...) gives it. Give skewness or exposure_skewness to simulate skewed data.",
            claim.span,
        )
    settings = simulation_settings(arguments)
    if isinstance(subject, SizingIR):
        space = subject.candidates
        if not isinstance(space, TotalCandidatesIR):
            fail(
                "unsupported_claim", "Simulation searches totals: use total_sizes(...).", claim.span
            )
        totals = list(range(space.min_n, space.max_n + 1))
        if len(totals) * settings.runs > MAX_SIMULATED_STUDIES:
            fail(
                "domain",
                f"Searching {len(totals):,} sizes with {settings.runs:,} runs each could "
                f"simulate more than {MAX_SIMULATED_STUDIES:,} studies. Narrow the range or "
                "use fewer runs.",
                claim.span,
            )
        drawn = sum(totals) + 2 * totals[-1]
    else:
        drawn = 2 * analysis.plan.model.total
    if drawn * settings.runs > MAX_SIMULATED_PARTICIPANTS:
        fail(
            "domain",
            "This scenario is simulated one participant at a time, and this could draw more "
            f"than {MAX_SIMULATED_PARTICIPANTS:,} participants. Narrow the range or use fewer "
            "runs.",
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
    "simulate": _constructor(
        "simulate",
        (("claim", ClaimIR), ("seed", int), ("runs", int, True)),
        "CalculationResult",
        _simulation,
        documentation=(
            "Estimate power by simulating the study runs times from seed, for a cited test "
            "with a simulation model. Gives estimates with 95% intervals; never evidence."
        ),
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
POPULATION_DOCUMENTATION = (
    'population says who is analysed: "randomised" for everyone randomised, in the arm they '
    'were assigned to (intention to treat), or "per_protocol" when participants excluded '
    "after randomisation are left out, with the arm sizes counting those analysed. "
    'randomisation_test needs "randomised" and refuses "per_protocol". Other tests take '
    "either, and their claims say which population the bound covers."
)
RANDOMISATION_PARAMETERS = (
    ("randomisation", "string", True),
    ("strata", "list", True),
    ("block_size", "integer", True),
    ("population", "string", True),
)
# Shared by every two-arm model module, so a file that loads several gets one copy.
ASSIGNMENT = _constructor(
    "assignment",
    (("n_control", "integer"), ("n_treatment", "integer"), *RANDOMISATION_PARAMETERS),
    "Assignment",
    _assignment,
    documentation="How participants are assigned to the two arms: the two arm sizes and, "
    "when declared, how the assignment was randomised. One assignment can be shared by "
    f"several outcomes measured on the same participants. {RANDOMISATION_DOCUMENTATION} "
    f"{POPULATION_DOCUMENTATION}",
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
    + f"{RANDOMISATION_DOCUMENTATION} {POPULATION_DOCUMENTATION}",
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


NAME_DOCUMENTATION = (
    'name labels the outcome, such as "response". One name is one outcome: models that '
    "share it must agree on its kind and better. A family, sequence or graph that asks the "
    "same question of a named outcome twice, the same test of the same null on the same "
    "participants, is refused."
)


def _outcome_piece_constructor(outcome) -> Constructor:
    repeated = (("measurements", "integer", True),) if outcome.repeatable else ()
    return _constructor(
        outcome_constructor_name(outcome.key),
        (("better", "string", True), *repeated, ("name", "string", True)),
        "Outcome",
        _outcome_piece(outcome.key),
        documentation=f"The {outcome.key} outcome measured on each participant. Combine "
        f"it with an assignment in two_arm(...). {BETTER_DOCUMENTATION}"
        + (f" {MEASUREMENTS_DOCUMENTATION}" if outcome.repeatable else "")
        + f" {NAME_DOCUMENTATION}",
    )


def _shorthand_note(outcome) -> str:
    return (
        f"Shorthand for two_arm(assignment=assignment(n_control, n_treatment, population), "
        f"outcome={outcome_constructor_name(outcome.key)}(better, name)); population and name "
        "mean the same as there."
    )


# The one-call model constructors: arm sizes, and the assignment's and outcome's optional
# declarations that fit in one call. Randomisation and repeated measurements need the pieces.
SHORTHAND_PARAMETERS = (
    ("n_control", "integer"),
    ("n_treatment", "integer"),
    ("better", "string", True),
    ("population", "string", True),
    ("name", "string", True),
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
        SHORTHAND_PARAMETERS,
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


STUDY_NAMES = (("exposure", "string", True), ("outcome", "string", True))
STUDY_SCALES = (("exposure_scale", "string", True), ("outcome_scale", "string", True))
STUDY_NAMES_DOCUMENTATION = (
    'exposure and outcome name what is studied, such as exposure="smoking"; claims use the names.'
)


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
                    SHORTHAND_PARAMETERS,
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
            "models.observational",
            (
                _constructor(
                    "cross_sectional",
                    (
                        ("n", "integer"),
                        *STUDY_NAMES,
                        *STUDY_SCALES,
                        ("survey", "string", True),
                        ("clusters", "integer", True),
                    ),
                    "CrossSectionalStudy",
                    _cross_sectional,
                    documentation="A cross-sectional study: n participants sampled from one "
                    "population, with exposure and outcome measured at the same time. Only n "
                    "is fixed, not how many are exposed. It measures prevalence, not "
                    "incidence. " + STUDY_NAMES_DOCUMENTATION,
                ),
                _constructor(
                    "cohort",
                    (
                        ("exposed", "integer", True),
                        ("unexposed", "integer", True),
                        ("n", "integer", True),
                        *STUDY_NAMES,
                        *STUDY_SCALES,
                    ),
                    "CohortStudy",
                    _cohort,
                    documentation="A cohort study: participants followed from exposure to "
                    "outcome. Give exposed and unexposed when the groups were sampled in fixed "
                    "numbers, or n when one population was sampled and exposure measured. "
                    + STUDY_NAMES_DOCUMENTATION,
                ),
                _constructor(
                    "case_control",
                    (
                        ("cases", "integer"),
                        ("controls", "integer"),
                        *STUDY_NAMES,
                        ("exposure_scale", "string", True),
                    ),
                    "CaseControlStudy",
                    _case_control,
                    documentation="A case-control study: cases with the outcome and controls "
                    "without it, sampled in fixed numbers and asked about past exposure. It "
                    "estimates odds ratios only, never risk or prevalence, because the design "
                    "fixed how many have the outcome. " + STUDY_NAMES_DOCUMENTATION,
                ),
                _constructor(
                    "person_time_cohort",
                    (*STUDY_NAMES, ("exposure_scale", "string", True)),
                    "PersonTimeStudy",
                    _person_time_cohort,
                    documentation="A cohort followed over person-time, counting events in the "
                    "exposed and unexposed. It measures incidence rates; no group size is "
                    "fixed. " + STUDY_NAMES_DOCUMENTATION,
                ),
                _constructor(
                    "observed_events",
                    (
                        ("model", PersonTimeStudyIR),
                        ("exposed_events", "integer"),
                        ("exposed_time", "number"),
                        ("unexposed_events", "integer"),
                        ("unexposed_time", "number"),
                    ),
                    "ObservedEvents",
                    _observed_events,
                    documentation="Events and person-time, such as person-years, in the exposed "
                    "and unexposed groups of a person-time cohort.",
                ),
                _constructor(
                    "matched_case_control",
                    (("pairs", "integer"), *STUDY_NAMES, ("exposure_scale", "string", True)),
                    "MatchedStudy",
                    _matched_case_control,
                    documentation="A 1:1 matched case-control study: each case matched to one "
                    "control on chosen characteristics. Its tests and intervals use the "
                    "pairs where exactly one was exposed; unmatched analyses refuse it. "
                    + STUDY_NAMES_DOCUMENTATION,
                ),
                _constructor(
                    "observed_pairs",
                    (("model", MatchedStudyIR), *((cell, "integer") for cell in PAIR_CELLS)),
                    "MatchedPairs",
                    _observed_pairs,
                    documentation="The observed pairs of a matched study: both exposed, only "
                    "the case, only the control, or neither. They must add up to the pairs.",
                ),
                _constructor(
                    "observed_table",
                    (("model", ObservationalStudyIR), *((cell, "integer") for cell in CELLS)),
                    "AssociationTable",
                    _observed_table,
                    documentation="The observed 2x2 table: exposed and unexposed cases, who "
                    "have the outcome, and noncases. It must fit what the design fixed: a "
                    "cohort's group sizes, a case-control study's numbers of cases and "
                    "controls, or the total.",
                ),
                _constructor(
                    "no_association",
                    (("model", ObservationalStudyIR),),
                    "AssociationNull",
                    _no_association,
                    documentation="Null: no association between the study's exposure and "
                    "outcome, an odds ratio of 1. For a cohort, equal risk with and without "
                    "exposure; for a case-control study, exposure as common among cases as "
                    "among controls; for a cross-sectional study, equal prevalence.",
                ),
                TYPE_I,
            ),
        ),
        Module(
            "tests.association",
            (
                _constructor(
                    "fisher_exact",
                    (("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")),
                    "AssociationAnalysis",
                    _fisher_exact,
                    documentation="Fisher's exact test of no association in an observational "
                    "2x2 study. Lean proves its level for every design: with group sizes "
                    "fixed by a cohort or case-control study, and with only the total fixed, "
                    "by averaging over the number exposed. The bound concerns association, "
                    "not an effect of the exposure.",
                ),
                _constructor(
                    "rate_test",
                    (("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")),
                    "RateAnalysis",
                    _rate_test,
                    documentation="The exact test of equal incidence rates: given the total "
                    "events, a two-sided binomial test of the exposed share at the exposed "
                    "share of person-time. Lean proves its level for every rate and any "
                    "person-time, given the total and on average over it.",
                ),
                _constructor(
                    "rate_result",
                    (("analysis", RateAnalysisIR), ("events", ObservedEventsIR)),
                    "ResultClaim",
                    _rate_result,
                    documentation="Claim about the exact p-value and decision of the rate test "
                    "for the observed events, with the test's Type I bound.",
                ),
                _constructor(
                    "mcnemar",
                    (("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")),
                    "MatchedAnalysis",
                    _mcnemar,
                    documentation="McNemar's exact test of no association within matched "
                    "pairs: given the discordant pairs, a two-sided binomial test at one half. "
                    "Lean proves its level given the number of discordant pairs and on "
                    "average over it.",
                ),
                _constructor(
                    "matched_result",
                    (("analysis", MatchedAnalysisIR), ("pairs", MatchedPairsIR)),
                    "ResultClaim",
                    _matched_result,
                    documentation="Claim about the exact p-value and decision of McNemar's "
                    "test for the observed pairs, with the test's Type I bound.",
                ),
                _constructor(
                    "association_result",
                    (("analysis", AssociationAnalysisIR), ("table", AssociationTableIR)),
                    "ResultClaim",
                    _association_result,
                    documentation="Claim about the exact p-value and decision of Fisher's "
                    "test for the observed table, with the test's Type I bound. For a design "
                    "that fixed only the total, the p-value is given the number exposed.",
                ),
                TYPE_I,
            ),
        ),
        Module(
            "estimation.observational",
            (
                _constructor(
                    "rate_ratio",
                    (("events", ObservedEventsIR), ("level", "level")),
                    "IntervalClaim",
                    _rate_ratio,
                    documentation="Interval for the incidence rate ratio of a person-time "
                    "cohort, from the exact interval for the exposed share of events.",
                ),
                *(
                    _constructor(
                        measure,
                        (
                            ("model", ObservationalStudyIR),
                            ("cases", "integer"),
                            ("level", "level"),
                            ("group", "string", True),
                        ),
                        "IntervalClaim",
                        _proportion(measure),
                        documentation=f"The {words} with its exact interval. Only a "
                        f"{designs[0].replace('_', '-')} study estimates it. For a cohort that "
                        'sampled groups separately, group="exposed" or "unexposed" says which.',
                    )
                    for measure, (words, designs) in PROPORTIONS.items()
                ),
                _constructor(
                    "conditional_odds_ratio",
                    (("pairs", MatchedPairsIR), ("level", "level")),
                    "IntervalClaim",
                    _conditional_odds_ratio,
                    documentation="Interval for the conditional odds ratio of a matched "
                    "study, the odds that the case is the exposed one in a discordant pair, "
                    "from the exact interval for that probability.",
                ),
            )
            + tuple(
                _constructor(
                    measure,
                    (("table", AssociationTableIR), ("level", "level")),
                    "IntervalClaim",
                    _effect_interval(measure),
                    documentation=f"Interval for the {words} at the given confidence level, "
                    "from exact intervals for each group's probability; valid for every pair "
                    "of probabilities, and conservative. "
                    + {
                        "odds": "Any design: for a case-control study it is the odds ratio "
                        "of exposure, which equals that of the outcome.",
                        "ratio": f"Only a {designs[0].replace('_', '-')} study estimates it.",
                        "difference": f"Only a {designs[0].replace('_', '-')} study estimates it.",
                    }[kind],
                )
                for measure, (words, kind, designs) in MEASURES.items()
            ),
        ),
        *(
            Module(
                name,
                (*(_cited_association_constructor(m) for m in group), TYPE_I),
            )
            for name, group in (
                ("tests.regression", REGRESSION),
                ("tests.correlation", CORRELATION),
                ("tests.survey", SURVEY),
            )
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
                    (
                        ("p_control", "number"),
                        ("p_treatment", "number"),
                        ("icc", "number", True),
                        ("cluster_size_cv", "number", True),
                    ),
                    "Rates",
                    _rates,
                    documentation="A planning point: one success probability per arm. "
                    "It is an input for power, not the null and not an established fact. "
                    "A test of cluster proportions also needs icc, the intracluster "
                    "correlation, and simulate(...) takes cluster_size_cv, how much cluster "
                    "sizes vary.",
                ),
                _constructor(
                    "mean_difference",
                    (
                        ("value", "number"),
                        ("sd", "number"),
                        ("icc", "number", True),
                        ("cluster_size_cv", "number", True),
                        ("sd_treatment", "number", True),
                        ("skewness", "number", True),
                    ),
                    "MeanDifference",
                    _mean_difference,
                    documentation="A planning point for a continuous outcome: the true mean "
                    "difference, treatment minus control, and the standard deviation of one "
                    "participant's outcome on the analysed scale. For a mixed model, sd is the "
                    "effective standard deviation of the contrast. A test of cluster means "
                    "also needs icc, the intracluster correlation: the share of the variance "
                    "that lies between clusters; simulate(...) also takes cluster_size_cv, the "
                    "coefficient of variation of cluster sizes. To simulate a two-sample "
                    "t-test in another scenario, give sd_treatment, the treatment arm's SD "
                    "(sd is then the control arm's), or skewness, for a gamma-shaped outcome. "
                    "All are planning inputs.",
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
                    "correlation",
                    (
                        ("value", "number"),
                        ("skewness", "number", True),
                        ("exposure_skewness", "number", True),
                    ),
                    "Correlation",
                    _correlation,
                    documentation="A planning point for two continuous variables: their "
                    "correlation, strictly between -1 and 1. For pearson_correlation. To "
                    "simulate skewed data, give skewness (of the outcome's error) or "
                    "exposure_skewness. Planning inputs, not established facts.",
                ),
                _constructor(
                    "outcome_means",
                    (
                        ("unexposed", "number"),
                        ("exposed", "number"),
                        ("sd", "number"),
                        ("exposed_share", "number", True),
                        ("design_effect", "number", True),
                    ),
                    "OutcomeMeans",
                    _outcome_means,
                    documentation="A planning point for a measured outcome by a yes-or-no "
                    "exposure, for linear_association or survey_linear: the outcome's mean "
                    "without and with the exposure, and its standard deviation about them. A "
                    "study that fixes only its total also needs exposed_share; a survey of a "
                    "complex sample, design_effect. Planning inputs, not established facts.",
                ),
                _constructor(
                    "odds_per_sd",
                    (
                        ("odds_ratio", "number"),
                        ("baseline", "number"),
                        ("exposure_r2", "number", True),
                        ("design_effect", "number", True),
                    ),
                    "OddsPerSd",
                    _odds_per_sd,
                    documentation="A planning point for logistic_association with a measured "
                    "exposure: the odds ratio per standard deviation of the exposure, the "
                    "outcome's probability at the exposure's mean, and optionally exposure_r2, "
                    "the share of the exposure's variance the covariates explain. A survey test "
                    "of a complex sample also takes design_effect. Planning inputs, not "
                    "established facts.",
                ),
                _constructor(
                    "slope",
                    (
                        ("value", "number"),
                        ("exposure_sd", "number"),
                        ("residual_sd", "number"),
                        ("exposure_r2", "number", True),
                        ("design_effect", "number", True),
                        ("skewness", "number", True),
                        ("exposure_skewness", "number", True),
                    ),
                    "Slope",
                    _slope,
                    documentation="A planning point for linear_association with a continuous "
                    "exposure: the change in the outcome's mean per unit of exposure, the "
                    "exposure's standard deviation, the outcome's standard deviation about the "
                    "regression, and optionally exposure_r2, the share of the exposure's "
                    "variance the covariates explain. A survey test of a complex sample also "
                    "takes design_effect. To simulate skewed data, give skewness (of the "
                    "residual) or exposure_skewness. All are planning inputs.",
                ),
                _constructor(
                    "exponential_survival",
                    (
                        ("hazard_ratio", "number"),
                        ("control_median", "number"),
                        ("accrual", "number"),
                        ("follow_up", "number"),
                        ("dropout", "number", True),
                        ("dropout_time", "number", True),
                        ("effect_delay", "number", True),
                    ),
                    "ExponentialSurvival",
                    _exponential_survival,
                    documentation="A planning point for a survival outcome given by its "
                    "times: the hazard ratio, treatment over control; the control arm's median "
                    "time to the event; participants entering steadily over accrual and "
                    "followed for follow_up after it; and optionally the probability of "
                    "dropping out by dropout_time. Times are exponential and in one unit, such "
                    "as months. The arm sizes then give the expected events, so arm sizes can "
                    "be searched. simulate(...) also takes effect_delay: the hazard ratio "
                    "applies only from that time after entry. All are planning inputs.",
                ),
                _constructor(
                    "risks",
                    (
                        ("unexposed", "number"),
                        ("exposed", "number", True),
                        ("risk_ratio", "number", True),
                        ("exposed_share", "number", True),
                    ),
                    "Risks",
                    _risks,
                    documentation="A planning point for a cohort: the risk of the outcome "
                    "without exposure, and with it, given as exposed or as risk_ratio, exposed "
                    "over unexposed. A cohort of one population, declared with n, also needs "
                    "exposed_share, the probability that a participant is exposed. A planning "
                    "input, not an established fact.",
                ),
                _constructor(
                    "outcome_prevalence",
                    (
                        ("unexposed", "number"),
                        ("exposed", "number", True),
                        ("prevalence_ratio", "number", True),
                        ("exposed_share", "number"),
                        ("design_effect", "number", True),
                    ),
                    "OutcomePrevalence",
                    _outcome_prevalence,
                    documentation="A planning point for a cross-sectional study: the prevalence "
                    "of the outcome without exposure, and with it, given as exposed or as "
                    "prevalence_ratio, and exposed_share, the probability that a participant is "
                    "exposed. A survey test of a complex sample also takes design_effect. A "
                    "planning input, not an established fact.",
                ),
                _constructor(
                    "exposure_prevalence",
                    (
                        ("controls", "number"),
                        ("cases", "number", True),
                        ("odds_ratio", "number", True),
                    ),
                    "ExposurePrevalence",
                    _exposure_prevalence,
                    documentation="A planning point for a case-control study: the share of "
                    "controls who were exposed, and of cases, given as cases or as odds_ratio, "
                    "the odds of exposure among cases over the odds among controls. A planning "
                    "input, not an established fact.",
                ),
                _constructor(
                    "discordant_pairs",
                    (("share", "number"), ("odds_ratio", "number")),
                    "DiscordantPairs",
                    _discordant_pairs,
                    documentation="A planning point for a 1:1 matched study: the probability "
                    "that a pair is discordant, with exactly one of the two exposed, and the "
                    "conditional odds ratio. A planning input, not an established fact.",
                ),
                _constructor(
                    "incidence_rates",
                    (
                        ("rate_ratio", "number"),
                        ("exposed_time", "number"),
                        ("unexposed_time", "number"),
                        ("events", "integer", True),
                    ),
                    "IncidenceRates",
                    _incidence_rates,
                    documentation="A planning point for a person-time cohort: the rate ratio, "
                    "exposed over unexposed, the expected person-time in each group, of which "
                    "only the exposed share matters, and the total number of events power is "
                    "calculated for. Leave events out to search them with event_counts.",
                ),
                _constructor(
                    "proportion",
                    (
                        ("value", "number"),
                        ("design_effect", "number", True),
                        ("population_size", "integer", True),
                    ),
                    "SingleProportion",
                    _single_proportion,
                    documentation="A planning point for one proportion, such as a prevalence or "
                    "a cumulative incidence: its value, strictly between 0 and 1. For the normal "
                    "interval of a survey, design_effect and population_size, the number in the "
                    "population sampled, for a finite population correction. A planning input, "
                    "not an established fact.",
                ),
                _constructor(
                    "precision_target",
                    (
                        ("at", PlanningPointIR),
                        ("level", "level"),
                        ("margin_of_error", "number", True),
                        ("relative_margin_of_error", "number", True),
                        ("assurance", "number", True),
                    ),
                    "PrecisionTarget",
                    _precision_target,
                    documentation="Require an interval at the given level to be narrow enough at "
                    "the planning point: its margin of error, half its width, at most "
                    "margin_of_error, or its relative margin of error at most "
                    "relative_margin_of_error, a fraction of the planning value. For a ratio the "
                    "relative margin r asks that the lower limit be at least (1 - r) times the "
                    "estimate, on the log scale. Without assurance, the interval is taken at the "
                    "counts the point expects; with it, the chance that the interval is narrow "
                    "enough must be at least assurance.",
                ),
                _constructor(
                    "planned_interval",
                    (
                        ("model", EstimableModelIR),
                        ("measure", "string"),
                        ("method", "string", True),
                        ("group", "string", True),
                    ),
                    "PlannedInterval",
                    _planned_interval,
                    documentation="The interval a study plans to report, for a precision target: "
                    "response_rate for one arm, difference for a two-arm trial, prevalence, "
                    "cumulative_incidence, risk or prevalence ratios and differences and "
                    "odds_ratio for observational studies, conditional_odds_ratio for matched "
                    'pairs and rate_ratio for person-time. method="exact" (the default) is '
                    'StatClaim\'s own exact interval; method="normal" is the usual large-sample '
                    "interval, and allows a survey's design effect and a finite population. For "
                    "a cohort that sampled two groups, group says whose cumulative incidence.",
                ),
                _constructor(
                    "interval_sizes",
                    (
                        ("interval", PlannedIntervalIR),
                        ("min_size", "integer"),
                        ("max_size", "integer"),
                        ("ratio", "integer", True),
                    ),
                    "IntervalCandidates",
                    _interval_sizes,
                    documentation="Sizes for a planned interval, in the design's own units: the "
                    "participants of one group or population; for two fixed groups, the first "
                    "(exposed, cases, or the control arm of a trial) with ratio of the other for "
                    "each; or the pairs or events.",
                ),
                _constructor(
                    "power_target",
                    (
                        ("at", PlanningPointIR),
                        ("minimum", "number"),
                        ("maximum_typeI", "level"),
                        ("nulls", NullScenariosIR, True),
                        ("rejecting", "string", True),
                    ),
                    "PowerTarget",
                    _power_target,
                    documentation="Require power of at least minimum at one planning point, "
                    "and a Type I error bound of at most maximum_typeI under the null. "
                    "Power at this point is not a guarantee for other alternatives. For a "
                    "design whose level is not proved, nulls lists where simulate(...) judges "
                    "its Type I error. For a family, rejecting says whether power means "
                    'rejecting "any" endpoint or "all" of them.',
                ),
                _constructor(
                    "endpoint_points",
                    (("at", "list"), ("correlation", "number")),
                    "EndpointPoints",
                    _endpoint_points,
                    documentation="A planning point for a family: one point per member, in "
                    "order (binomial_rates for Fisher's test, mean_difference for a t-test), "
                    "and the correlation between endpoints measured on the same participants, "
                    "from 0 for independent endpoints to below 1. Planning inputs.",
                ),
                _constructor(
                    "null_scenarios",
                    (("at", "list"),),
                    "NullScenarios",
                    _null_scenarios,
                    documentation="Points at the null, such as mean_difference(value=0, "
                    "sd=10), at which simulate(...) judges the Type I error of a design whose "
                    "level is not proved. Planning inputs; the error at other points is not "
                    "claimed.",
                ),
                _constructor(
                    "meets",
                    (("analysis", PlannableIR), ("target", TargetIR)),
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
                    "cluster_counts",
                    (
                        ("analysis", TwoArmTestIR),
                        ("cluster_size", "integer"),
                        ("min_per_arm", "integer"),
                        ("max_per_arm", "integer"),
                    ),
                    "ClusterCandidates",
                    _cluster_counts,
                    documentation="Cluster-randomised trials for a test of cluster summaries: "
                    "min_per_arm to max_per_arm clusters in each arm, each of cluster_size "
                    "participants. Each keeps the analysis's null, test and alpha.",
                ),
                _constructor(
                    "cluster_sizes",
                    (
                        ("analysis", TwoArmTestIR),
                        ("min_size", "integer"),
                        ("max_size", "integer"),
                    ),
                    "ClusterCandidates",
                    _cluster_sizes,
                    documentation="Cluster-randomised trials for a test of cluster summaries: "
                    "the declared clusters per arm, with min_size to max_size participants in "
                    "each cluster. Each keeps the analysis's null, test and alpha. With few "
                    "clusters, no number of participants may be enough.",
                ),
                _constructor(
                    "cohort_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_exposed", "integer"),
                        ("max_exposed", "integer"),
                        ("unexposed_per_exposed", "integer", True),
                    ),
                    "GroupCandidates",
                    _group_sizes("cohort"),
                    documentation="Designs of a cohort that samples its exposed and unexposed "
                    "groups: n exposed and unexposed_per_exposed * n unexposed (1 unless "
                    "given), for n within the inclusive bounds. Each keeps the analysis's "
                    "study, null and alpha.",
                ),
                _constructor(
                    "case_control_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_cases", "integer"),
                        ("max_cases", "integer"),
                        ("controls_per_case", "integer", True),
                    ),
                    "GroupCandidates",
                    _group_sizes("case_control"),
                    documentation="Designs of a case-control study: n cases and "
                    "controls_per_case * n controls (1 unless given), for n within the "
                    "inclusive bounds. Each keeps the analysis's study, null and alpha.",
                ),
                _constructor(
                    "total_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_n", "integer"),
                        ("max_n", "integer"),
                    ),
                    "TotalCandidates",
                    _total_sizes,
                    documentation="Cross-sectional studies, or cohorts of one population, with "
                    "min_n to max_n participants, keeping the analysis's study, null and alpha. "
                    "For Fisher's test, sample_size certifies a sufficient total and "
                    "smallest_sample_size is not offered; for a cited test with a power "
                    "formula, both are calculated.",
                ),
                _constructor(
                    "matched_sizes",
                    (
                        ("analysis", PlannableIR),
                        ("min_pairs", "integer"),
                        ("max_pairs", "integer"),
                    ),
                    "CountCandidates",
                    _count_sizes("pairs", MAX_PLANNED_PAIRS),
                    documentation="Matched studies with min_pairs to max_pairs pairs, keeping "
                    "the analysis's null and alpha: McNemar's test, or a conditional logistic "
                    "regression.",
                ),
                _constructor(
                    "event_counts",
                    (
                        ("analysis", PlannableIR),
                        ("min_events", "integer"),
                        ("max_events", "integer"),
                    ),
                    "CountCandidates",
                    _count_sizes("events", MAX_EVENTS),
                    documentation="Totals of min_events to max_events events for the rate "
                    "test or a Poisson rate regression, keeping its null and alpha. The planning "
                    "point gives no events.",
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
                    (("candidates", CandidateSpaceIR), ("target", TargetIR)),
                    "PlanningClaim",
                    _sizing(False),
                    documentation="Claim that some candidate meets the target. The search is "
                    "ascending; a sufficient size is not claimed to be the smallest possible.",
                ),
                _constructor(
                    "smallest_sample_size",
                    (("candidates", CandidateSpaceIR), ("target", TargetIR)),
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
            "designs.adaptive",
            (
                _constructor(
                    "blinded_reestimation",
                    (
                        ("analysis", CitedAnalysisIR),
                        ("interim_per_arm", "integer"),
                        ("difference", "number"),
                        ("power", "number"),
                        ("max_per_arm", "integer"),
                    ),
                    "Reestimation",
                    _reestimation,
                    documentation="Student's t-test whose size per arm is re-estimated after "
                    "interim_per_arm per arm, from the variance of all outcomes with the arms "
                    "pooled, so no one sees the groups. The new size gives power at the planned "
                    "difference; it is never below the analysis's size per arm nor above "
                    "max_per_arm. Its Type I error is not proved: simulate(...) judges it at "
                    "the target's null scenarios.",
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
