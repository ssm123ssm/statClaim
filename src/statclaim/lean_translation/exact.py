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

from statclaim.fisher import fisher_exact
from statclaim.incidence import tails_at
from statclaim.language import (
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationResultIR,
    DifferenceIntervalIR,
    EffectIntervalIR,
    IntervalIR,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedResultIR,
    ObservationIR,
    OneSampleObservationIR,
    ProportionIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateRatioIR,
    RateResultIR,
    TwoStageObservationIR,
)
from statclaim.lean_translation import statements as S
from statclaim.lean_translation.emit import rational
from statclaim.matched import tails
from statclaim.planning import _lean_design as lean_design
from statclaim.planning import margin_grid

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
