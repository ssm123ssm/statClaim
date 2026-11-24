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
from statclaim.language import (
    AnalysisIR,
    AssociationAnalysisIR,
    MatchedAnalysisIR,
    ObservationIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
)
from statclaim.lean_translation.emit import rational
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
