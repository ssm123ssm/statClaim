"""The typed objects a .stat program elaborates to: models, designs, analyses, claims."""

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, ClassVar, cast
from typing import Literal as Choice

from statclaim.association import (
    AssociationResult,
    AssociationTable,
    AssociationTest,
    EffectInterval,
    null_statement,
)
from statclaim.composition import Component, Composition
from statclaim.design import Design
from statclaim.family import Endpoint, FisherFamily
from statclaim.incidence import (
    ObservedEvents,
    ProportionEstimate,
    RateRatioInterval,
    RateResult,
    RateTest,
)
from statclaim.language.core import (
    LANGUAGE_VERSION,
    LocatedValue,
)
from statclaim.language_contracts import (
    FARRINGTON_MANNING_CONTRACT,
    FISHER_CONTRACT,
    MARGIN_CONTRACT,
    ONE_SIDED_FISHER_CONTRACT,
    SCORE_CONTRACT,
    WALD_CONTRACT,
    HypothesisContract,
)
from statclaim.language_syntax import (
    Span,
    deferring,
)
from statclaim.matched import (
    MatchedInterval,
    MatchedPairs,
    MatchedResult,
    MatchedTest,
)
from statclaim.methods import NULL_FORMS, OUTCOMES, SHARP_NULL
from statclaim.methods.assumptions import (
    ACCOUNTS_FOR,
    HIGHER_IS_BETTER,
    LOWER_IS_BETTER,
    POPULATION_COVERED,
)
from statclaim.methods.core import Assumption, CitedMethod, Guarantee
from statclaim.methods.observational import (
    ObservationalMethod,
)
from statclaim.observational_planning import (
    AssociationPowerPlan,
    MatchedPowerPlan,
    RatePowerPlan,
    TotalPowerPlan,
)
from statclaim.planning import (
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
    RandomisationTest,
    groups_of,
)


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
            # cluster_assignment(...) declares the clusters of both arms together.
            assert self.clusters_control is not None and self.clusters_treatment is not None
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
        # Read only once the randomisation is declared: randomisation_test refuses an
        # assignment without one. None would fail in groups_of as an unknown scheme.
        scheme = cast(str, self.randomisation)
        return groups_of(units, treated, scheme, self.strata, self.block_size)


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
        # The elaborator checks the same contract first; when it is deferred, so is this.
        if not self.contract.accepts(self.plan, self.hypothesis) and not deferring(
            "hypothesis_mismatch", "model_mismatch"
        ):
            raise ValueError(
                "A Fisher analysis requires its design's equal-proportions null."
                if self.alternative == "two_sided"
                else "This analysis requires a null of the form p_treatment - p_control <= value."
            )

    def margin_test(self, target=None, observed=None, sizes=None) -> MarginTest:
        """The exact difference test, optionally with a planning target or observed counts."""
        # Fisher's and the difference test's contracts give an exact test a binomial model.
        model = cast(ModelIR, self.plan.model)
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
        # Fisher's and the difference test's contracts give an exact test a binomial model.
        model = cast(ModelIR, self.plan.model)
        return Design(
            model.n_control,
            model.n_treatment,
            self.plan.stopping,
            self.alpha,
            self.alternative,
        )


@dataclass(frozen=True)
class ProportionZAnalysisIR(LevelTestIR):
    plan: PlanIR
    hypothesis: HypothesisIR
    alpha: Fraction
    squared_cutoff: Fraction

    test: ClassVar[str]
    contract: ClassVar[HypothesisContract]


@dataclass(frozen=True)
class WaldAnalysisIR(ProportionZAnalysisIR):
    test = "wald_test"
    contract = WALD_CONTRACT


@dataclass(frozen=True)
class ScoreAnalysisIR(ProportionZAnalysisIR):
    test = "score_test"
    contract = SCORE_CONTRACT


@dataclass(frozen=True)
class FarringtonManningAnalysisIR(LevelTestIR):
    plan: PlanIR
    hypothesis: HypothesisIR
    alpha: Fraction
    squared_cutoff: Fraction

    test = "farrington_manning"
    contract = FARRINGTON_MANNING_CONTRACT


# Every null hypothesis: the classes derived from NullIR.
type AnyNullIR = HypothesisIR | OutcomeNullIR | SharpNullIR | AssociationNullIR


@dataclass(frozen=True)
class CitedAnalysisIR(TwoArmTestIR, LevelTestIR):
    """An analysis whose guarantee is cited from the literature, not proved in Lean.

    Its power, when its method has a formula, is an approximate calculation only.
    """

    plan: PlanIR
    hypothesis: AnyNullIR
    alpha: Fraction
    method: CitedMethod

    @property
    def guarantee(self) -> Guarantee:
        return self.method.guarantee(self.alpha, self.hypothesis.statement)

    @property
    def assumptions(self) -> tuple[Assumption, ...]:
        """The method's assumptions, the direction of benefit when the file leaves it out,
        and for a declared test, what it must do for the declared design."""
        # The observational design check gives a test of randomised arms a two-arm model.
        model = cast(TwoArmModelIR, self.plan.model)
        vouched = (
            tuple(ACCOUNTS_FOR[feature] for feature in model.features)
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
            if population is None:
                return
            for condition in POPULATION_COVERED.get(population, ()):
                if condition not in found:
                    found.append(condition)

    visit(subject)
    return tuple(found)


def direction_assumptions(null: AnyNullIR) -> tuple[Assumption, ...]:
    """A one-sided null takes a side. If the model does not declare it, it is assumed."""
    favours = NULL_FORMS[null.predicate][1].favours if null.predicate in NULL_FORMS else None
    if favours is None:
        return ()
    # no_association is not among NULL_FORMS, so only a two-arm model's null takes a side.
    assert not isinstance(null, AssociationNullIR)
    if null.model.better is not None:
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
        # randomisation_test reads the design's assignment, which only a two-arm model has.
        assert isinstance(model, TwoArmModelIR)
        unit, units, treated = model.assignment.randomised_units
        return RandomisationTest(
            units,
            treated,
            self.alpha,
            unit,
            OUTCOMES[model.outcome].constructor,
            model.n_control,
            model.n_treatment,
            # randomisation_test refuses an assignment that does not declare it.
            cast(str, model.assignment.randomisation),
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
        # Every design but case-control, whose groups are fixed, declares n.
        return sum(groups) if groups is not None else self.n  # type: ignore[attr-defined]


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
        # cohort(...) refuses exposed without unexposed.
        return None if self.exposed is None else (cast(int, self.unexposed), self.exposed)


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
        # fisher_exact refuses a design that is not an observational study.
        assert isinstance(model, ObservationalStudyIR)
        groups = model.groups
        return AssociationTest(
            model.design,
            self.alpha,
            groups,
            # Every design but case-control, whose groups are fixed, declares n.
            None if groups is not None else model.n,  # type: ignore[attr-defined]
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
            # Every design but case-control, whose groups are fixed, declares n.
            None if model.groups is not None else model.n,  # type: ignore[attr-defined]
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
        # mcnemar refuses a design that is not a matched study.
        assert isinstance(model, MatchedStudyIR)
        return MatchedTest(model.pairs, self.alpha, model.exposure, model.outcome)


@dataclass(frozen=True)
class AsymptoticMcNemarAnalysisIR(LevelTestIR):
    plan: PlanIR
    hypothesis: AssociationNullIR
    alpha: Fraction
    squared_cutoff: Fraction

    test = "mcnemar_asymptotic"


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
        # rate_test refuses a design that is not a person-time cohort.
        assert isinstance(model, PersonTimeStudyIR)
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
            # Every design but case-control, whose groups are fixed, declares n.
            return self.model.n  # type: ignore[attr-defined]
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

    # Each member is an analysis or another combination.
    analyses: tuple[tuple[str, Any], ...]
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
    """One question tested at several looks: with the error level split across them
    (alpha_spending), or with boundaries from an error-spending function that use the
    correlation between looks (group_sequential). Its power is summed exactly for Fisher's
    test and simulated for tests with a simulation model for looks."""

    mode: str = "sequential"
    # For group_sequential: the spending function, and the largest level each look may use.
    spending: str | None = None
    limits: tuple[Fraction, ...] = ()

    def lower(self) -> Composition:
        return Composition(
            self.alpha,
            tuple(_component(name, analysis) for name, analysis in self.analyses),
            self.mode,
            self.limits,
        )

    @property
    def final(self):
        """The last look: the whole study."""
        return self.analyses[-1][1]


# A member of a family, sequence, graph or design with looks (analyses._members): a single
# test, or another combination.
type MemberIR = AnalysisIR | CitedAnalysisIR | RandomisationAnalysisIR | ComposedFamilyIR


def _component(name: str, analysis: MemberIR) -> Component:
    if isinstance(analysis, SequentialIR):
        # A design with interim looks counts as one test of its null at its overall level.
        inner = analysis.lower()
        rules = inner.rules
        return Component(
            name,
            analysis.alpha,
            inner.scope,
            rules.grade,
            rules.contract + (f" version {rules.version}" if rules.grade == "cited" else ""),
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
    # Callers first check that the point is the design's own kind (points.GROUP_POINTS).
    point = cast(ExposurePrevalenceIR, point)
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
        model = self.analysis.plan.model
        # blinded_reestimation(...) takes a t-test, which reads a two-arm model's sizes.
        assert isinstance(model, TwoArmModelIR)
        return model.n_control


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
        if self.margin is not None:
            return self.margin
        # precision_target(...) takes margin_of_error or relative_margin_of_error.
        assert self.relative is not None
        return self.relative


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
            # A single-arm analysis is planned at response_rate(...): checks._check_point.
            cast(RateIR, target.at).value,
            target.minimum,
            target.maximum_typeI,
        )


@dataclass(frozen=True)
class OneSampleScoreAnalysisIR(LevelTestIR):
    model: OneArmModelIR
    null_rate: Fraction
    alpha: Fraction
    squared_cutoff: Fraction

    @property
    def guarantee(self) -> Guarantee:
        return Guarantee(
            "type_I_error",
            "at_most",
            self.alpha,
            f"response rate = {self.null_rate}",
            "finite_sample",
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
        # Each analysis is planned at its own kind of point: checks._check_point.
        target = self.target
        if isinstance(self.analysis, AssociationAnalysisIR):
            model = self.analysis.plan.model
            # fisher_exact refuses a design that is not an observational study.
            assert isinstance(model, ObservationalStudyIR)
            if model.groups is None:
                # A study that fixes only its total is planned with exposed_share.
                total = cast(RisksIR | OutcomePrevalenceIR, target.at)
                return TotalPowerPlan(
                    self.analysis.lower(),
                    *group_probabilities(total),
                    cast(Fraction, total.exposed_share),
                    target.minimum,
                    target.maximum_typeI,
                )
            return AssociationPowerPlan(
                self.analysis.lower(),
                *group_probabilities(target.at),
                target.minimum,
                target.maximum_typeI,
            )
        if isinstance(self.analysis, MatchedAnalysisIR):
            pairs = cast(DiscordantPairsIR, target.at)
            return MatchedPowerPlan(
                self.analysis.lower(),
                pairs.share,
                pairs.odds_ratio,
                target.minimum,
                target.maximum_typeI,
            )
        if isinstance(self.analysis, RateAnalysisIR):
            rates = cast(IncidenceRatesIR, target.at)
            return RatePowerPlan(
                self.analysis.lower(),
                rates.exposed_time,
                rates.unexposed_time,
                rates.rate_ratio,
                # meets(...) refuses incidence_rates without events.
                cast(int, rates.events),
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
                cast(RateIR, target.at).value,
                target.minimum,
                target.maximum_typeI,
            )
        # calculate(...) lowers only exact analyses (plan_kinds.KINDS); Fisher's test is left.
        fisher, point = cast(AnalysisIR, self.analysis), cast(RatesIR, target.at)
        return PowerPlan(
            fisher.lower(),
            point.p_control,
            point.p_treatment,
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
class LookCandidatesIR(CandidateSpaceIR):
    """Designs with the declared looks' test, null and allocation whose looks' sizes per
    control arm are searched freely: every increasing choice from min_per_arm to max_per_arm
    in steps of step. Each candidate keeps the declared levels (alpha_spending) or takes its
    own spending boundaries (group_sequential). The criterion ranks the candidates that meet
    the target."""

    design: "SequentialIR"
    min_per_arm: int
    max_per_arm: int
    step: int
    criterion: str

    @property
    def analysis(self) -> "SequentialIR":
        return self.design


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

    analysis: AssociationAnalysisIR | CitedAssociationIR
    min_size: int
    max_size: int
    ratio: int = 1


@dataclass(frozen=True)
class TotalCandidatesIR(CandidateSpaceIR):
    """Cross-sectional studies, or cohorts of one population, of min_n to max_n participants.
    Each keeps the analysis's study, null and alpha."""

    analysis: AssociationAnalysisIR | CitedAssociationIR
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
    # What the claim is about: an analysis, a family, a planning subject or a result.
    subject: Any
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
                OneSampleScoreAnalysisIR,
                AssociationAnalysisIR,
                MatchedAnalysisIR,
                RateAnalysisIR,
                CitedAssociationIR,
            ),
        ):
            return subject.guarantee
        if isinstance(subject, ComposedFamilyIR):
            return subject.lower().guarantee
        if self.kind == "typeI" and isinstance(
            subject,
            (
                AnalysisIR,
                ProportionZAnalysisIR,
                FarringtonManningAnalysisIR,
                AsymptoticMcNemarAnalysisIR,
            ),
        ):
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
        # The canonical form is built from these objects, so it is imported when used.
        from statclaim.language.normalize import normalize

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


def planned_analysis(subject: Any) -> Any:
    """The analysis a planning claim is about."""
    if isinstance(subject, FeasibilityIR):
        return subject.analysis
    return subject.candidates.analysis
