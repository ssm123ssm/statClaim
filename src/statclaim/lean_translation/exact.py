"""Exact tests in translated programs: what each one's Type I claim states. Trusted, like
`denote.py`; how each claim is proved is in `prove.py`. Milestone 5 of
docs/proposals/lean-translation.md.

Each exact module proves its guarantee for one kind of test. A test of two proportions
in a fixed design is stated as a Type I claim on its module's analysis, and a test of
association with fixed groups as Fisher's claim on two binomial counts: the bridge from
the association module to the core objects. Randomisation, rate, matched and
cross-sectional tests are stated as their module states them, as a bound under the law
of the declared assignment or sample, for every parameter under the null.

The corpus check derives the statement each test's certificate template checks today
from the translated claim (test 5; `scripts/check_lean_translation.py`).

A result for observed data is stated in parts, one for each theorem its template checks
today: the counts, the p-value Python reports, the decision and the test's guarantee. A
mistake in Python's computation makes a part false, and its proof fails.
"""

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

from statclaim import plan_kinds
from statclaim.association import AssociationTest
from statclaim.fisher import fisher_exact
from statclaim.incidence import tails_at
from statclaim.language import (
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationResultIR,
    DifferenceIntervalIR,
    EffectIntervalIR,
    FeasibilityIR,
    IntervalIR,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedResultIR,
    ObservationIR,
    OneArmCandidatesIR,
    OneSampleObservationIR,
    ProportionIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateRatioIR,
    RateResultIR,
    TotalCandidatesIR,
    TwoStageCandidatesIR,
    TwoStageObservationIR,
    group_probabilities,
    planned_analysis,
)
from statclaim.lean_translation import statements as S
from statclaim.lean_translation.emit import rational
from statclaim.matched import MatchedTest, tails
from statclaim.observational_planning import (
    MatchedPowerPlan,
    RatePowerPlan,
    TotalPowerPlan,
    search_events,
    search_groups,
    search_pairs,
    search_totals,
)
from statclaim.planning import (
    OneSamplePlan,
    margin_grid,
    search_equal_arms,
    search_one_sample,
    search_two_stage,
)
from statclaim.planning import _lean_design as lean_design

MODULES = "StatClaim.Modules"
EXACT = (AssociationAnalysisIR, RandomisationAnalysisIR, RateAnalysisIR, MatchedAnalysisIR)


@dataclass
class ExactAnalysis:
    """An exact test: its Type I claim, and what its proof needs."""

    name: str
    kind: str  # one_sided, margin, groups, mixture, randomisation, rate or matched
    level: str  # its SignificanceLevel
    statement: str
    test: Any  # the validated test, whose numbers the proof checks
    names: dict[str, str] = field(default_factory=dict)  # the definitions it states


def is_exact(ir: object) -> bool:
    """Whether a value is an exact test this module states."""
    if isinstance(ir, AnalysisIR):
        return ir.alternative in ("greater", "margin")
    return isinstance(ir, EXACT)


def stopping(ir: object) -> str:
    plan = getattr(ir, "plan", None)
    return getattr(plan, "stopping", "fixed")


def level(alpha: Fraction) -> str:
    return f"⟨{rational(alpha)}, by norm_num, by norm_num⟩"


def bound(level_name: str) -> str:
    return f"({level_name}.value : ℝ)"


def randomisation(test: Any, level: str) -> S.Theorem:
    """Every statistic and all outcomes under the sharp null, at the declared assignment."""
    draws = str(test.draws) if test.draws else ""
    if test.grouped:
        groups = "[" + ", ".join(f"({size}, {treated})" for size, treated in test.groups) + "]"
        return S.randomisation_typeI(P, level, draws, groups=groups)
    return S.randomisation_typeI(P, level, draws, units=str(test.units), treated=str(test.treated))


# Results and intervals -------------------------------------------------------------------
@dataclass
class ExactResult:
    """A result or interval for observed data, in parts: the theorems its certificate
    claims, from statements.py, and what the proof renders."""

    kind: str  # the template whose proofs prove it
    theorems: list[S.Theorem]
    source: Any  # what the template renders: the proof's material, not trusted
    definitions: str = ""  # a plan's definitions, which its theorems name

    @property
    def parts(self) -> list[tuple[str, str]]:
        return [(theorem.part, theorem.proposition()) for theorem in self.theorems]

    def statement(self) -> str:
        return " ∧\n    ".join(f"({statement})" for _, statement in self.parts)


# Within a translated program, names in StatClaim are written in full.
P = S.PROGRAM


def program_point(value: Fraction) -> str:
    return f"({S.point(P, *value.as_integer_ratio())})"


def result(subject: ObservationIR, analysis: Any) -> ExactResult:
    """The observed counts of a test of two proportions: the p-value and the decision
    Python reports, and the test's guarantee."""
    ir = subject.analysis
    xc, xt = subject.control_successes, subject.treatment_successes
    level = ir.alpha.as_integer_ratio()
    if ir.alternative == "margin":
        test: Any = ir.margin_test(observed=(xc, xt))
        sizes, thresholds = analysis.names["sizes"], analysis.names["thresholds"]
        assert list(test.thresholds) == list(analysis.test.thresholds)
        grid, shift = margin_grid(test.margin)
        up, down = max(shift, 0), max(-shift, 0)
        # The margin as a whole number of grid steps, as the margin module counts it.
        stated = f"(((({up} : ℕ) : ℚ) - (({down} : ℕ) : ℚ)) / (({grid} : ℕ) : ℚ))"
        module = f"({MODULES}.DifferenceTest.analysis {sizes} {thresholds} {stated})"
        error = test.maximum_typeI if test.has_target else test.alpha
        theorems = [
            S.analysis_sizes(sizes, test.n_control, test.n_treatment),
            S.analysis_typeI(module, S.ratio(*error.as_integer_ratio())),
        ]
        if test.has_target:
            (a, d), (b, e) = test.p_control.as_integer_ratio(), test.p_treatment.as_integer_ratio()
            rates = f"{a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide)"
            power = test.minimum_power.as_integer_ratio()
            theorems.append(S.margin_power(P, module, rates, power))
        verdict = "true" if test.reject_null else "false"
        theorems.append(S.margin_decision(P, test.n_treatment, thresholds, xc, xt, verdict))
        return ExactResult("margin_result", theorems, test)
    design = ir.lower()
    found = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=xc,
        treatment_successes=xt,
        alpha=design.alpha,
        alternative=design.alternative,
    )
    nc, nt, total = design.n_control, design.n_treatment, xc + xt
    value = found.p_value.as_integer_ratio()
    truth = "True" if found.reject_null else "False"
    if ir.alternative == "greater":
        theorems = [
            S.counts(nc, nt, xc, xt),
            S.one_sided_p_value(P, nc, nt, total, xc, value),
            S.one_sided_decision(P, nc, nt, total, xc, level, truth),
            S.analysis_typeI(analysis.name, f"({analysis.level}.value : ℝ)"),
        ]
    else:
        theorems = [
            S.counts(nc, nt, xc, xt),
            S.support(P, nc, nt, total, found.support_min, found.support_max),
            S.p_value(P, nc, nt, total, xc, value),
            S.table_probability(
                P, nc, nt, total, xc, found.observed_table_probability.as_integer_ratio()
            ),
            S.fisher_decision(P, nc, nt, xc, xt, level, truth),
            S.fisher_typeI(P, nc, nt, level),
        ]
    return ExactResult("fisher_result", theorems, (design, found))


def other_result(subject: object, analysis: Any) -> ExactResult:
    """The other results and the intervals."""
    found: Any = subject.lower()  # type: ignore[attr-defined]
    if isinstance(subject, AssociationResultIR):
        return association_result(found, analysis)
    if isinstance(subject, RateResultIR):
        return rate_result(found, analysis)
    if isinstance(subject, MatchedResultIR):
        return matched_result(found, analysis)
    if isinstance(subject, OneSampleObservationIR):
        return one_sample_result(found)
    if isinstance(subject, TwoStageObservationIR):
        return stage_result(found)
    if isinstance(subject, (IntervalIR, ProportionIR)):
        binomial = found if isinstance(subject, IntervalIR) else found.binomial
        return binomial_interval(binomial)
    if isinstance(subject, DifferenceIntervalIR):
        return difference_interval(found)
    if isinstance(subject, EffectIntervalIR):
        return effect_interval(found)
    if isinstance(subject, RateRatioIR):
        return rate_ratio(found)
    assert isinstance(subject, MatchedIntervalIR)
    return matched_interval(found)


RESULTS = (
    AssociationResultIR,
    RateResultIR,
    MatchedResultIR,
    OneSampleObservationIR,
    TwoStageObservationIR,
)
INTERVALS = (
    IntervalIR,
    ProportionIR,
    DifferenceIntervalIR,
    EffectIntervalIR,
    RateRatioIR,
    MatchedIntervalIR,
)


def association_result(found: Any, analysis: Any) -> ExactResult:
    test, fisher, value = found.test, found.fisher, f"{analysis.level}.value"
    first, second, x, y = found.table.conditional
    an, ad = test.alpha.as_integer_ratio()
    truth = "True" if fisher.reject_null else "False"
    if test.groups is not None:
        groups = analysis.names["groups"]
        g1, g2 = f"{groups}.nControl", f"{groups}.nTreatment"
        theorems = [S.groups_sizes(g1, g2, test.groups), S.groups_typeI(P, g1, g2, value)]
    else:
        n = str(test.n)
        theorems = [
            S.total_size(n, test.n),
            S.mixture_law(P, n),
            S.mixture_typeI(P, n, value),
        ]
    if found.table.fixed_groups:
        table = f"({x}, {y})"
        region = f"{P.root}fisherRejectionRegionAt {first} {second} (({an} : ℚ) / {ad})"
    else:
        table = f"({found.table.exposed}, ({x}, {y}))"
        region = f"{P.modules}Association.mixtureRejection {test.n} (({an} : ℚ) / {ad})"
    theorems += [
        S.p_value(P, first, second, x + y, x, fisher.p_value.as_integer_ratio()),
        S.table_probability(
            P, first, second, x + y, x, fisher.observed_table_probability.as_integer_ratio()
        ),
        S.association_decision(P, table, region, truth),
    ]
    return ExactResult("association_result", theorems, found)


def rate_result(found: Any, analysis: Any) -> ExactResult:
    events, value = found.events, f"{analysis.level}.value"
    n, x = events.total, events.exposed_events
    upper, lower, _ = tails_at(n, x, events.share)
    truth = "True" if found.reject_null else "False"
    theorems = [
        S.rate_typeI(P, value),
        S.tails(P, n, events.share.as_integer_ratio(), x, upper, lower),
        S.rate_decision(P, n, x, program_point(events.share), value, truth),
    ]
    return ExactResult("rate_result", theorems, found)


def matched_result(found: Any, analysis: Any) -> ExactResult:
    pairs, value = str(found.test.pairs), f"{analysis.level}.value"
    d, x = found.observed.discordant, found.observed.case_exposed
    upper, lower = tails(d, x)
    truth = "True" if found.reject_null else "False"
    theorems = [
        S.pairs_size(pairs, found.test.pairs),
        S.pairs_law(P, pairs),
        S.pairs_typeI(P, pairs, value),
        S.tails(P, d, (1, 2), x, upper, lower),
        S.pairs_decision(P, d, x, pairs, value, truth),
    ]
    return ExactResult("matched_result", theorems, found)


def one_sample_result(found: Any) -> ExactResult:
    n, k, c = found.n, found.responses, found.critical
    rate, level = found.null_rate.as_integer_ratio(), found.alpha.as_integer_ratio()
    theorems = [
        S.one_sample_p_value(P, n, k, rate, found.p_value.as_integer_ratio()),
        S.one_sample_critical(P, n, rate, level, c),
        S.one_sample_decision(c, k, found.reject_null),
        S.one_sample_typeI(P, n, c, rate, level),
    ]
    return ExactResult("one_sample_result", theorems, found)


def stage_result(found: Any) -> ExactResult:
    design = f"({MODULES}.{lean_design(found.design)})"
    theorems = [S.stage_interim(design, found.first, found.continued)]
    if found.second is not None:
        rejected = found.decision == "reject_null"
        theorems.append(S.stage_decision(design, found.first, found.second, rejected))
    bound = found.error_bound.as_integer_ratio()
    theorems.append(S.stage_typeI(P, design, program_point(found.null_rate), bound))
    return ExactResult("stage_result", theorems, found)


def tail_of(found: Any) -> str:
    return S.ratio(*found.tail_level.as_integer_ratio())


def binomial_interval(found: Any) -> ExactResult:
    n, tail = found.n, tail_of(found)
    lower, upper = found.lower.as_integer_ratio(), found.upper.as_integer_ratio()
    theorems = [
        S.binomial_coverage(P, n, tail),
        S.binomial_interval(P, n, found.responses, tail, lower, upper),
    ]
    return ExactResult("binomial_interval", theorems, found)


def ends(found: Any) -> list[tuple[int, ...]]:
    """Each arm's lower and upper endpoint, as numerators and denominators."""
    return [
        (*arm.lower.as_integer_ratio(), *arm.upper.as_integer_ratio())
        for arm in (found.control, found.treatment)
    ]


def difference_interval(found: Any) -> ExactResult:
    n, m = found.n_control, found.n_treatment
    x, y = found.control_successes, found.treatment_successes
    tail = tail_of(found.control)
    control, treatment = ends(found)
    theorems = [
        S.joint_coverage(P, found.level.as_integer_ratio(), n, m, tail),
        S.difference_interval(P, n, m, x, y, tail, control, treatment),
    ]
    return ExactResult("difference_interval", theorems, found)


def effect_interval(found: Any) -> ExactResult:
    first, second, x, y = found.table.conditional
    tail = tail_of(found.groups.control)
    level = found.level.as_integer_ratio()
    if found.table.fixed_groups:
        coverage = S.joint_coverage(P, level, first, second, tail, ("a", "b"))
    else:
        coverage = S.mixture_coverage(P, level, str(found.table.n), tail)
    arms = S.two_arms(P, first, second, x, y, tail)
    control, treatment = ends(found.groups)
    theorems = [coverage, S.effect_interval(P, found.kind, arms, control, treatment)]
    return ExactResult("effect_interval", theorems, found)


def rate_ratio(found: Any) -> ExactResult:
    binomial = found.binomial
    tail = tail_of(binomial)
    lower, upper = binomial.lower.as_integer_ratio(), binomial.upper.as_integer_ratio()
    scale = f" * {S.ratio(*found.scale.as_integer_ratio())}"
    n, x = found.events.total, found.events.exposed_events
    theorems = [
        S.rate_coverage(P, found.level.as_integer_ratio(), tail),
        S.odds_interval(P, n, x, tail, lower, upper, scale),
    ]
    return ExactResult("rate_ratio", theorems, found)


def matched_interval(found: Any) -> ExactResult:
    binomial = found.binomial
    tail = tail_of(binomial)
    lower, upper = binomial.lower.as_integer_ratio(), binomial.upper.as_integer_ratio()
    d, x = found.observed.discordant, found.observed.case_exposed
    theorems = [
        S.pairs_coverage(P, found.level.as_integer_ratio(), str(found.observed.pairs), tail),
        S.odds_interval(P, d, x, tail, lower, upper, ""),
    ]
    return ExactResult("matched_interval", theorems, found)


# Planning ---------------------------------------------------------------------------------
# The kinds of analysis whose plans have exact power, checked by a template.
EXACT_PLANS = ("fisher", "one_sample", "two_stage", "association", "matched", "rate")


def planned(subject: Any) -> tuple[str, Any]:
    """The plan a planning claim is about, as `verify` finds it: a declared design, or the
    design a sample-size search selects. The kind names the template that checks it."""
    analysis = planned_analysis(subject)
    kind = plan_kinds.kind_of(analysis).name
    if kind not in EXACT_PLANS:
        raise ValueError(f"Plans of the {kind} kind have no exact power to prove.")
    if isinstance(subject, FeasibilityIR):
        plan = subject.lower()
    else:
        plan = searched(subject, analysis, kind)
    return PLAN_TEMPLATES[type(plan).__name__], plan


def searched(subject: Any, analysis: Any, kind: str) -> Any:
    """The design a sample-size search selects, or None."""
    target, candidates = subject.target, subject.candidates
    if kind == "association" and isinstance(candidates, TotalCandidatesIR):
        test = analysis.lower()
        bounds = (candidates.min_n, candidates.max_n)
        first: Any = TotalPowerPlan(
            AssociationTest(test.design, test.alpha, None, bounds[0], test.exposure, test.outcome),
            *group_probabilities(target.at),
            target.at.exposed_share,
            target.minimum,
            target.maximum_typeI,
            "sample_size",
            bounds,
        )
        return search_totals(first, *bounds)[0]
    if kind == "association":
        return search_groups(
            analysis.lower(),
            *group_probabilities(target.at),
            target.minimum,
            target.maximum_typeI,
            candidates.min_size,
            candidates.max_size,
            subject.minimal,
            candidates.ratio,
        )[0]
    if kind in ("matched", "rate"):
        bounds = (candidates.min_size, candidates.max_size)
        point = target.at
        if isinstance(analysis, MatchedAnalysisIR):
            test = analysis.lower()
            first = MatchedPowerPlan(
                MatchedTest(bounds[0], test.alpha, test.exposure, test.outcome),
                point.share,
                point.odds_ratio,
                target.minimum,
                target.maximum_typeI,
                "sample_size",
                bounds,
                subject.minimal,
            )
            return search_pairs(first, *bounds, subject.minimal)[0]
        first = RatePowerPlan(
            analysis.lower(),
            point.exposed_time,
            point.unexposed_time,
            point.rate_ratio,
            bounds[0],
            target.minimum,
            target.maximum_typeI,
            "sample_size",
            bounds,
            subject.minimal,
        )
        return search_events(first, *bounds, subject.minimal)[0]
    if isinstance(candidates, TwoStageCandidatesIR):
        return search_two_stage(
            candidates.null_rate,
            target.at.value,
            target.minimum,
            target.maximum_typeI,
            candidates.max_total,
            candidates.criterion,
        )[0]
    if isinstance(candidates, OneArmCandidatesIR):
        first = candidates.analysis.plan(target, candidates.min_n)
        return search_one_sample(first, candidates.min_n, candidates.max_n, subject.minimal)[0]
    return search_equal_arms(
        candidates.analysis.alpha,
        target.at.p_control,
        target.at.p_treatment,
        target.minimum,
        target.maximum_typeI,
        candidates.min_per_arm,
        candidates.max_per_arm,
        subject.minimal,
        candidates.ratio,
        candidates.analysis.alternative,
    )[0]


# The template that checks each kind of plan.
PLAN_TEMPLATES = {
    "PowerPlan": "power_plan",
    "TwoStagePlan": "policy_plan",
    "OneSamplePlan": "policy_plan",
    "AssociationPowerPlan": "association_plan",
    "TotalPowerPlan": "total_plan",
    "MatchedPowerPlan": "matched_plan",
    "RatePowerPlan": "rate_plan",
    "NoneType": "none",
}


def met(plan: Any) -> str | None:
    """Why `verify` would issue no certificate for the plan, or None."""
    if plan is None:
        return "No candidate in the search meets the target, so nothing is claimed."
    calculation = plan.evaluate()
    if not calculation["typeI_target_met"]:
        return "The test's level exceeds the requested Type I bound."
    if not calculation["power_target_met"]:
        return "The plan's power falls short of the target, so verify issues no certificate."
    design = getattr(plan, "design", None)
    if getattr(design, "stopping", "fixed") != "fixed":
        return "A plan's power is exact for a fixed design; this design stops on the data."
    return None


def two_points(first: Fraction, second: Fraction) -> str:
    return f"({S.point(P, *first.as_integer_ratio())}) ({S.point(P, *second.as_integer_ratio())})"


def plan_claim(kind: str, plan: Any, space: str) -> ExactResult:
    """A plan's claim: the theorems its certificate claims, naming the definitions it
    declares in `space`."""
    error = S.ratio(*plan.maximum_typeI.as_integer_ratio())
    power = plan.minimum_power.as_integer_ratio()
    minimal = getattr(plan, "minimal", False)
    if kind == "power_plan":
        design = plan.design
        nc, nt = design.n_control, design.n_treatment
        module = "FisherOneSided" if design.alternative == "greater" else "FisherPower"
        (a, d), (b, e) = plan.p_control.as_integer_ratio(), plan.p_treatment.as_integer_ratio()
        rates = f"{a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide)"
        level = design.alpha.as_integer_ratio()
        definitions = S.fisher_plan_definitions(P, module, nc, nt, level, rates)
        analysis, planning = f"{space}.declaredAnalysis", f"{space}.planningPoint"
        theorems = [
            S.analysis_sizes(f"{space}.declaredSizes", nc, nt),
            S.analysis_typeI(analysis, error),
            S.fisher_power(analysis, planning, power),
        ]
        if minimal:
            theorems.append(
                S.fisher_smaller(
                    P,
                    module,
                    plan.search[0],
                    nc,
                    plan.ratio,
                    planning,
                    f"{space}.declaredLevel",
                    power,
                )
            )
        return ExactResult(kind, theorems, plan, definitions)
    if kind == "policy_plan":
        rate = plan.null_rate.as_integer_ratio()
        alternative = plan.alternative_rate.as_integer_ratio()
        designed = f"{space}.declaredDesign"
        if isinstance(plan, OneSamplePlan):
            module, term, analysis = "OneSampleBinomial", f"⟨{plan.n}, {plan.critical}⟩", "analysis"
            shape = f"{designed}.n = {plan.n} ∧ {designed}.critical = {plan.critical}"
        else:
            module, term = "TwoStageBinomial", f"{MODULES}.{lean_design(plan)}"
            analysis = "analysisAtMost"
            shape = f"{designed}.nFirst = {plan.n_first} ∧ {designed}.nSecond = {plan.n_second}"
        definitions = S.policy_definitions(P, module, term, rate, analysis)
        theorems = [
            S.policy_stages(shape),
            S.analysis_typeI(f"{space}.declaredAnalysis", error),
            S.policy_power(P, f"{space}.declaredAnalysis", alternative, power),
        ]
        if minimal:
            level = plan.alpha.as_integer_ratio()
            maximum = plan.maximum_typeI.as_integer_ratio()
            theorems += [
                S.one_sample_critical(P, plan.n, rate, level, plan.critical),
                S.policy_smaller(
                    P, plan.search[0], plan.n, rate, level, maximum, alternative, power
                ),
            ]
        return ExactResult(kind, theorems, plan, definitions)
    level = f"{space}.declaredLevel.value"
    definitions = S.level_definition(P, plan.test.alpha.as_integer_ratio())
    if kind == "association_plan":
        first, second = plan.test.groups
        rates = two_points(plan.p_first, plan.p_second)
        theorems = [
            S.groups_sizes(str(first), str(second), (first, second)),
            S.groups_typeI(P, str(first), str(second), level, error),
            S.groups_power(P, str(first), str(second), rates, level, power),
        ]
        if minimal:
            theorems.append(
                S.groups_smaller(P, plan.search[0], second, plan.ratio, rates, level, power)
            )
    elif kind == "matched_plan":
        n = plan.test.pairs
        rates = two_points(plan.discordant, plan.case_share)
        theorems = [
            S.pairs_typeI(P, str(n), level, error),
            S.pairs_power(P, n, rates, level, power),
        ]
        if minimal:
            theorems.append(S.pairs_smaller(P, plan.search[0], n, rates, level, power))
    elif kind == "rate_plan":
        n = plan.events
        alternative = f"({S.point(P, *plan.event_share.as_integer_ratio())})"
        null = f"({S.point(P, *plan.share.as_integer_ratio())})"
        theorems = [
            S.rate_typeI(P, level, error),
            S.events_power(P, n, alternative, null, level, power),
        ]
        if minimal:
            theorems.append(S.events_smaller(P, plan.search[0], n, alternative, null, level, power))
    else:
        n = plan.test.n
        share = f"({S.point(P, *plan.exposed_share.as_integer_ratio())})"
        theorems = [
            S.total_size(str(n), n),
            S.mixture_typeI(P, str(n), level, error),
            S.total_power(P, n, share, two_points(plan.p_first, plan.p_second), level, power),
        ]
    return ExactResult(kind, theorems, plan, definitions)
