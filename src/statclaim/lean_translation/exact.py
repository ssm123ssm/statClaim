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


def randomisation(test, level_name: str) -> str:
    """Every statistic and all outcomes under the sharp null, at the declared assignment."""
    value = f"({level_name}.value : ℚ)"
    if test.grouped:
        groups = "[" + ", ".join(f"({size}, {treated})" for size, treated in test.groups) + "]"
        assignment = (
            f"{MODULES}.Randomisation.GroupedAssignment ({groups} : {MODULES}.Randomisation.Groups)"
        )
        record, outcomes = "Record", f"{assignment} → Record"
        sharp = "∀ first second, outcomes first = outcomes second"
        law = f"{MODULES}.Randomisation.groupedLaw {groups}"
        rejection = (
            f"{MODULES}.Randomisation.uniformRejection ({MODULES}.Randomisation.groupedSplits "
            f"{groups}) statistic outcomes {value}"
        )
    else:
        units, treated = test.units, test.treated
        assignment = f"{MODULES}.Randomisation.Assignment {units}"
        record = "Value"
        outcomes = f"{MODULES}.Randomisation.PotentialOutcomes {units} Value"
        sharp = f"{MODULES}.Randomisation.SharpNull outcomes"
        law = f"{MODULES}.Randomisation.law {units} {treated}"
        rejection = (
            f"{MODULES}.Randomisation.rejection {units} {treated} statistic outcomes {value}"
        )
    observed = "Record" if test.grouped else f"(Fin {test.units} → Value)"
    statistic = f"{assignment} → {observed} → Statistic"
    if test.draws:
        # The observed assignment and the draws are independent, each with the design's law.
        law = f"MeasureTheory.Measure.pi (fun _ : Fin ({test.draws} + 1) => {law})"
        rejection = (
            f"{MODULES}.Randomisation.drawnRejection {test.draws} statistic outcomes {value}"
        )
    return (
        f"∀ {{{record} : Type}} {{Statistic : Type}} [LinearOrder Statistic]\n"
        f"      (statistic : {statistic})\n"
        f"      (outcomes : {outcomes}),\n"
        f"      ({sharp}) →\n"
        f"      ({law}).real\n"
        f"        ({rejection}) ≤ {bound(level_name)}"
    )


# Results ----------------------------------------------------------------------------------
@dataclass
class ExactResult:
    """A result for observed data: its parts, each named after the theorem its template
    checks today, and what the proof renders."""

    kind: str  # fisher_result or margin_result
    parts: list[tuple[str, str]]  # (name, statement)
    source: Any  # what the template renders: the proof's material, not trusted

    def statement(self) -> str:
        return " ∧\n    ".join(f"({statement})" for _, statement in self.parts)


def result(subject: ObservationIR, analysis: Any) -> ExactResult:
    """The observed counts of a test of two proportions: the p-value and the decision
    Python reports, and the test's guarantee."""
    ir = subject.analysis
    xc, xt = subject.control_successes, subject.treatment_successes
    numerator, denominator = ir.alpha.as_integer_ratio()
    if ir.alternative == "margin":
        test: Any = ir.margin_test(observed=(xc, xt))
        sizes, thresholds = analysis.names["sizes"], analysis.names["thresholds"]
        assert list(test.thresholds) == list(analysis.test.thresholds)
        grid, shift = margin_grid(test.margin)
        up, down = max(shift, 0), max(-shift, 0)
        # The margin as a whole number of grid steps, as the margin module counts it.
        stated = f"(((({up} : ℕ) : ℚ) - (({down} : ℕ) : ℚ)) / (({grid} : ℕ) : ℚ))"
        module = f"({MODULES}.DifferenceTest.analysis {sizes} {thresholds} {stated})"
        bound_n, bound_d = (
            test.maximum_typeI if test.has_target else test.alpha
        ).as_integer_ratio()
        parts = [
            (
                "sizes",
                f"{sizes}.nControl = {test.n_control} ∧ {sizes}.nTreatment = {test.n_treatment} ∧ "
                f"0 < {sizes}.nControl ∧ 0 < {sizes}.nTreatment",
            ),
            (
                "typeI",
                f"({module}.typeIClaim ((({bound_n} : ℕ) : ℝ) / (({bound_d} : ℕ) : ℝ))).statement",
            ),
        ]
        if test.has_target:
            power_n, power_d = test.minimum_power.as_integer_ratio()
            (a, d), (b, e) = (
                test.p_control.as_integer_ratio(),
                test.p_treatment.as_integer_ratio(),
            )
            point = f"{a} {d} {b} {e} (by decide) (by decide) (by decide) (by decide)"
            parts.append(
                (
                    "power",
                    f"({module}.powerClaim\n      (fun parameter => parameter = "
                    f"{MODULES}.FisherPower.ratePoint {point})\n"
                    f"      ((({power_n} : ℕ) : ℝ) / (({power_d} : ℕ) : ℝ))).statement",
                )
            )
        verdict = "true" if test.reject_null else "false"
        parts.append(
            (
                "decision",
                f"{MODULES}.DifferenceTest.rejects {test.n_treatment} {thresholds} {xc} {xt} = "
                f"{verdict}",
            )
        )
        return ExactResult("margin_result", parts, test)
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
    p_n, p_d = found.p_value.as_integer_ratio()
    truth = "True" if found.reject_null else "False"
    counts = ("counts", f"0 < {nc} ∧ 0 < {nt} ∧ {xc} ≤ {nc} ∧ {xt} ≤ {nt}")
    level = f"(({numerator} : ℚ) / {denominator})"
    if ir.alternative == "greater":
        lower = f"{MODULES}.FisherOneSided.lowerPValue {nc} {nt} {total} {xc}"
        parts = [
            counts,
            ("p_value", f"{lower} = ({p_n} : ℚ) / {p_d}"),
            ("decision", f"({lower} ≤ ({numerator} : ℚ) / {denominator}) ↔ {truth}"),
            ("typeI", f"({analysis.name}.typeIClaim ({analysis.level}.value : ℝ)).statement"),
        ]
    else:
        t_n, t_d = found.observed_table_probability.as_integer_ratio()
        region = f"StatClaim.fisherRejectionRegionAt {nc} {nt} {level}"
        parts = [
            counts,
            (
                "support",
                f"∀ (k : ℕ), k ∈ StatClaim.hypergeometricSupport {nc} {nt} {total} ↔\n"
                f"      {found.support_min} ≤ k ∧ k ≤ {found.support_max}",
            ),
            (
                "p_value",
                f"StatClaim.hypergeometricPValue {nc} {nt} {total} {xc} = ({p_n} : ℚ) / {p_d}",
            ),
            (
                "table_probability",
                f"StatClaim.hypergeometricMass {nc} {nt} {total} {xc} = ({t_n} : ℚ) / {t_d}",
            ),
            ("decision", f"(({xc}, {xt}) ∈ {region}) ↔ {truth}"),
            (
                "typeI",
                f"∀ (p : unitInterval), (StatClaim.fisherNullLaw {nc} {nt} p).real ({region}) ≤\n"
                f"      (({numerator} : ℝ) / {denominator})",
            ),
        ]
    return ExactResult("fisher_result", parts, (design, found))


def ratio(numerator: int, denominator: int) -> str:
    """A rational as the templates write it in ℝ."""
    return f"((({numerator} : ℕ) : ℝ) / (({denominator} : ℕ) : ℝ))"


def point(value: Fraction) -> str:
    numerator, denominator = value.as_integer_ratio()
    return f"(StatClaim.ratPoint {numerator} {denominator} (by decide) (by decide))"


def confidence(n: object, tail: str, count: object) -> str:
    return f"{MODULES}.BinomialInterval.confidenceSet {n} {tail} {count}"


def odds(value: str) -> str:
    return f"{MODULES}.Association.odds {value}"


def other_result(subject: object, analysis: Any) -> ExactResult:
    """The other results and the intervals: each part as its template states it."""
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
    test, fisher, level = found.test, found.fisher, analysis.level
    first, second, x, y = found.table.conditional
    p_n, p_d = fisher.p_value.as_integer_ratio()
    t_n, t_d = fisher.observed_table_probability.as_integer_ratio()
    an, ad = test.alpha.as_integer_ratio()
    truth = "True" if fisher.reject_null else "False"
    parts: list[tuple[str, str]]
    if test.groups is not None:
        groups = analysis.names["groups"]
        g1, g2 = test.groups
        parts = [
            (
                "sizes",
                f"{groups}.nControl = {g1} ∧ {groups}.nTreatment = {g2} ∧ "
                f"0 < {groups}.nControl ∧ 0 < {groups}.nTreatment",
            ),
            (
                "typeI",
                f"∀ (p : unitInterval), (StatClaim.fisherNullLaw {groups}.nControl "
                f"{groups}.nTreatment p).real\n      (StatClaim.fisherRejectionRegionAt "
                f"{groups}.nControl {groups}.nTreatment {level}.value) ≤ ({level}.value : ℝ)",
            ),
        ]
    else:
        n = test.n
        parts = [
            ("size", f"{n} = {n} ∧ 0 < {n}"),
            (
                "law",
                f"∀ (q p : unitInterval), {MODULES}.Association.mixtureLaw {n} q p Set.univ = 1",
            ),
            ("typeI", analysis.statement),
        ]
    if found.table.fixed_groups:
        membership = (
            f"(({x}, {y}) ∈ StatClaim.fisherRejectionRegionAt {first} {second} (({an} : ℚ) / {ad}))"
        )
    else:
        membership = (
            f"(({found.table.exposed}, ({x}, {y})) ∈ {MODULES}.Association.mixtureRejection "
            f"{test.n} (({an} : ℚ) / {ad}))"
        )
    parts += [
        (
            "p_value",
            f"StatClaim.hypergeometricPValue {first} {second} {x + y} {x} = ({p_n} : ℚ) / {p_d}",
        ),
        (
            "table_probability",
            f"StatClaim.hypergeometricMass {first} {second} {x + y} {x} = ({t_n} : ℚ) / {t_d}",
        ),
        ("decision", f"{membership} ↔ {truth}"),
    ]
    return ExactResult("association_result", parts, found)


def rate_result(found: Any, analysis: Any) -> ExactResult:
    events, level = found.events, analysis.level
    n, x = events.total, events.exposed_events
    a, d = events.share.as_integer_ratio()
    upper, lower, _ = tails_at(n, x, events.share)
    truth = "True" if found.reject_null else "False"
    parts = [
        ("typeI", analysis.statement),
        (
            "tails",
            f"{MODULES}.OneSampleBinomial.tailNumerator {n} {a} {d} {x} = {upper} ∧\n"
            f"      {MODULES}.BinomialInterval.lowerNumerator {n} {a} {d} {x} = {lower}",
        ),
        (
            "decision",
            f"(({n}, {x}) ∈ {MODULES}.Incidence.given (fun n => {MODULES}.Incidence.rejectionAt "
            f"{point(events.share)} n\n      ({level}.value : ℝ))) ↔ {truth}",
        ),
    ]
    return ExactResult("rate_result", parts, found)


def matched_result(found: Any, analysis: Any) -> ExactResult:
    pairs, level = found.test.pairs, analysis.level
    d, x = found.observed.discordant, found.observed.case_exposed
    upper, lower = tails(d, x)
    truth = "True" if found.reject_null else "False"
    parts = [
        ("size", f"{pairs} = {pairs} ∧ 0 < {pairs}"),
        ("law", f"∀ (δ π : unitInterval), {MODULES}.Matched.pairsLaw {pairs} δ π Set.univ = 1"),
        ("typeI", analysis.statement),
        (
            "tails",
            f"{MODULES}.OneSampleBinomial.tailNumerator {d} 1 2 {x} = {upper} ∧\n"
            f"      {MODULES}.BinomialInterval.lowerNumerator {d} 1 2 {x} = {lower}",
        ),
        (
            "decision",
            f"(({d}, {x}) ∈ {MODULES}.Matched.pairsRejection {pairs} ({level}.value : ℝ)) ↔ "
            f"{truth}",
        ),
    ]
    return ExactResult("matched_result", parts, found)


def one_sample_result(found: Any) -> ExactResult:
    n, k, c = found.n, found.responses, found.critical
    a, d = found.null_rate.as_integer_ratio()
    an, ad = found.alpha.as_integer_ratio()
    p_n, p_d = found.p_value.as_integer_ratio()
    rate = point(found.null_rate)
    parts = [
        (
            "p_value",
            f"(({MODULES}.OneSampleBinomial.policy ⟨{n}, {k}⟩).law {rate}).real\n"
            f"      {{count | {k} ≤ count}} = {ratio(p_n, p_d)}",
        ),
        ("critical", f"{MODULES}.OneSampleBinomial.criticalValue {n} {a} {d} {an} {ad} = {c}"),
        ("decision", f"{c} ≤ {k}" if found.reject_null else f"¬ {c} ≤ {k}"),
        (
            "typeI",
            f"(({MODULES}.OneSampleBinomial.analysis ⟨{n}, {c}⟩ {rate}).typeIClaim\n"
            f"      {ratio(an, ad)}).statement",
        ),
    ]
    return ExactResult("one_sample_result", parts, found)


def stage_result(found: Any) -> ExactResult:
    design = f"({MODULES}.{lean_design(found.design)})"
    b_n, b_d = found.error_bound.as_integer_ratio()
    stages = f"{MODULES}.TwoStageBinomial.Design"
    continued = "true" if found.continued else "false"
    parts = [("interim", f"{stages}.continues {design} {found.first} = {continued}")]
    if found.second is not None:
        rejected = "true" if found.decision == "reject_null" else "false"
        parts.append(
            ("decision", f"{stages}.rejects {design} {found.first} {found.second} = {rejected}")
        )
    parts.append(
        (
            "typeI",
            f"(({MODULES}.TwoStageBinomial.analysisAtMost {design} {point(found.null_rate)})"
            f".typeIClaim\n      {ratio(b_n, b_d)}).statement",
        )
    )
    return ExactResult("stage_result", parts, found)


def binomial_interval(found: Any) -> ExactResult:
    n, x = found.n, found.responses
    tail = ratio(*found.tail_level.as_integer_ratio())
    parts = [
        (
            "coverage",
            f"∀ (p : unitInterval), 1 - 2 * {tail} ≤\n"
            f"      (ProbabilityTheory.binomial {n} p).real\n"
            f"        {{count | p ∈ {confidence(n, tail, 'count')}}}",
        ),
        (
            "interval",
            f"∀ (p : unitInterval) (member : p ∈ {confidence(n, tail, x)}),\n"
            f"      {point(found.lower)} ≤ p ∧ p ≤ {point(found.upper)}",
        ),
    ]
    return ExactResult("binomial_interval", parts, found)


def ends(found: Any) -> tuple[tuple[int, int, int, int], tuple[int, int, int, int]]:
    """Each arm's lower and upper endpoint, as numerators and denominators."""
    control, treatment = (
        (*arm.lower.as_integer_ratio(), *arm.upper.as_integer_ratio())
        for arm in (found.control, found.treatment)
    )
    return control, treatment


def joint_coverage(level: Fraction, n: int, m: int, tail: str, x: str, y: str) -> str:
    return (
        f"∀ (pc pt : unitInterval), {ratio(*level.as_integer_ratio())} ≤ "
        f"(StatClaim.productBinomial {n} {m} pc pt).real\n"
        f"      ({{{x} | pc ∈ {confidence(n, tail, x)}}} ×ˢ\n"
        f"        {{{y} | pt ∈ {confidence(m, tail, y)}}})"
    )


def difference(control: tuple[int, ...], treatment: tuple[int, ...]) -> str:
    cln, cld, cun, cud = control
    tln, tld, tun, tud = treatment
    return (
        f"(({tln} : ℕ) : ℝ) / (({tld} : ℕ) : ℝ) - (({cun} : ℕ) : ℝ) / (({cud} : ℕ) : ℝ) ≤\n"
        "        (pt : ℝ) - (pc : ℝ) ∧\n"
        "      (pt : ℝ) - (pc : ℝ) ≤\n"
        f"        (({tun} : ℕ) : ℝ) / (({tud} : ℕ) : ℝ) - (({cln} : ℕ) : ℝ) / (({cld} : ℕ) : ℝ)"
    )


def difference_interval(found: Any) -> ExactResult:
    n, m = found.n_control, found.n_treatment
    x, y = found.control_successes, found.treatment_successes
    tail = ratio(*found.control.tail_level.as_integer_ratio())
    control, treatment = ends(found)
    parts = [
        ("coverage", joint_coverage(found.level, n, m, tail, "x", "y")),
        (
            "interval",
            f"∀ (pc pt : unitInterval)\n      (control : pc ∈ {confidence(n, tail, x)})\n"
            f"      (treatment : pt ∈ {confidence(m, tail, y)}),\n"
            f"      {difference(control, treatment)}",
        ),
    ]
    return ExactResult("difference_interval", parts, found)


def effect_interval(found: Any) -> ExactResult:
    groups = found.groups
    first, second, x, y = found.table.conditional
    tail = ratio(*groups.control.tail_level.as_integer_ratio())
    control, treatment = ends(groups)
    cln, cld, cun, cud = control
    tln, tld, tun, tud = treatment
    if found.table.fixed_groups:
        coverage = joint_coverage(found.level, first, second, tail, "a", "b")
    else:
        n = found.table.n
        coverage = (
            f"∀ (q pc pt : unitInterval),\n      {ratio(*found.level.as_integer_ratio())} ≤\n"
            f"      ({MODULES}.Association.mixture {n} q (fun k => StatClaim.productBinomial "
            f"({n} - k) k pc pt)).real\n"
            f"        ({MODULES}.Association.given {n} (fun k =>\n"
            f"          {{a | pc ∈ {confidence(f'({n} - k)', tail, 'a')}}} ×ˢ\n"
            f"            {{b | pt ∈ {confidence('k', tail, 'b')}}}))"
        )
    hypotheses = (
        f"(pc pt : unitInterval)\n      (control : pc ∈ {confidence(first, tail, x)})\n"
        f"      (treatment : pt ∈ {confidence(second, tail, y)})"
    )
    if found.kind == "difference":
        statement = difference(control, treatment)
    elif found.kind == "ratio":
        hypotheses += "\n      (positive : 0 < (pc : ℝ))"
        statement = f"{ratio(tln, tld)} / {ratio(cun, cud)} ≤ (pt : ℝ) / pc"
        if cln > 0:
            statement += f" ∧\n      (pt : ℝ) / pc ≤ {ratio(tun, tud)} / {ratio(cln, cld)}"
    else:
        hypotheses += (
            "\n      (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1)"
        )
        effect = f"{odds('pt')} / {odds('pc')}"
        statement = (
            f"{odds(ratio(tln, tld))} / {odds(ratio(cun, cud))} ≤ {effect}"
            if cun < cud
            else f"0 ≤ {effect}"
        )
        if cln > 0 and tun < tud:
            statement += f" ∧\n      {effect} ≤ {odds(ratio(tun, tud))} / {odds(ratio(cln, cld))}"
    parts = [("coverage", coverage), ("interval", f"∀ {hypotheses},\n      {statement}")]
    return ExactResult("effect_interval", parts, found)


def single_odds(lower: tuple[int, int], upper: tuple[int, int], scale: str) -> str:
    """Bounds on an odds, times a scale, from bounds on a share. No upper bound at one."""
    statement = f"{odds(ratio(*lower))}{scale} ≤ {odds('π')}{scale}"
    if upper[0] < upper[1]:
        statement += f" ∧\n      {odds('π')}{scale} ≤ {odds(ratio(*upper))}{scale}"
    return statement


def rate_ratio(found: Any) -> ExactResult:
    binomial = found.binomial
    n, x = found.events.total, found.events.exposed_events
    tail = ratio(*binomial.tail_level.as_integer_ratio())
    scale = f" * {ratio(*found.scale.as_integer_ratio())}"
    lower, upper = binomial.lower.as_integer_ratio(), binomial.upper.as_integer_ratio()
    parts = [
        (
            "coverage",
            f"∀ (total : NNReal) (π : unitInterval), "
            f"{ratio(*found.level.as_integer_ratio())} ≤ "
            f"({MODULES}.Incidence.ratesLaw total π).real\n"
            f"      ({MODULES}.Incidence.given (fun n =>\n"
            f"        {{x | π ∈ {confidence('n', tail, 'x')}}}))",
        ),
        (
            "interval",
            f"∀ (π : unitInterval)\n      (member : π ∈ {confidence(n, tail, x)}) "
            f"(below : (π : ℝ) < 1),\n      {single_odds(lower, upper, scale)}",
        ),
    ]
    return ExactResult("rate_ratio", parts, found)


def matched_interval(found: Any) -> ExactResult:
    binomial = found.binomial
    pairs = found.observed.pairs
    d, x = found.observed.discordant, found.observed.case_exposed
    tail = ratio(*binomial.tail_level.as_integer_ratio())
    lower, upper = binomial.lower.as_integer_ratio(), binomial.upper.as_integer_ratio()
    parts = [
        (
            "coverage",
            f"∀ (δ π : unitInterval), {ratio(*found.level.as_integer_ratio())} ≤ "
            f"({MODULES}.Matched.pairsLaw {pairs} δ π).real\n"
            f"      ({MODULES}.Association.given {pairs}\n"
            f"        (fun d => {{x | π ∈ {confidence('d', tail, 'x')}}}))",
        ),
        (
            "interval",
            f"∀ (π : unitInterval)\n      (member : π ∈ {confidence(d, tail, x)}) "
            f"(below : (π : ℝ) < 1),\n      {single_odds(lower, upper, '')}",
        ),
    ]
    return ExactResult("matched_interval", parts, found)
