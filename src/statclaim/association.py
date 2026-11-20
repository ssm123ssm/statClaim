"""Fisher's exact test of no association in an observational 2×2 study.

The design decides what the sampling fixed. A cohort study fixes how many exposed and
unexposed participants are followed, and a case-control study how many cases and
controls are sampled: the table then holds two independent binomial counts, and Fisher's
theorem applies with the groups in place of arms. A cross-sectional study, or a cohort
that does not fix how many are exposed, fixes only the total: given the number exposed
the test has level alpha, so averaged over it the test does too. Lean proves both once
(StatClaim.Modules.Association); a certificate instantiates them for the declared sizes.

Exposure was not assigned, so a bound on Type I error concerns association only.
"""

import re
from dataclasses import dataclass
from fractions import Fraction

from statclaim.fisher import (
    FisherResult,
    fisher_exact,
    fraction_record,
    parse_alpha,
    validate_alpha,
)
from statclaim.planning import MAX_ONE_ARM, DifferenceInterval, _audit
from statclaim.randomisation import PRESPECIFIED

ASSOCIATION_KIND = "statclaim_association_certificate"
RESULT_KIND = "statclaim_association_result_certificate"
INTERVAL_KIND = "statclaim_effect_interval_certificate"
TEST_ID = "fisher_exact"
TEST_VERSION = "0.1.0"
NULL_ID = "no_association"
DESIGNS = ("cross_sectional", "cohort", "case_control")
# Participants in one study. Certificates only compare these sizes with zero.
MAX_PARTICIPANTS = 1_000_000
# Participants in an observed table: its exact p-value is checked term by term.
MAX_TABLE = 4_000
# The four cells of a 2x2 table, in the order a, b, c, d.
CELLS = ("exposed_cases", "exposed_noncases", "unexposed_cases", "unexposed_noncases")
NAME = re.compile(r"[A-Za-z][A-Za-z0-9 _'()-]{0,59}")

# The null of each design, as a formula and in words. All say: odds ratio 1.
NULL_STATEMENTS = {
    "cohort": "risk_exposed = risk_unexposed",
    "case_control": "exposure_cases = exposure_controls",
    "cross_sectional": "prevalence_exposed = prevalence_unexposed",
    "matched_case_control": "conditional_odds_ratio = 1",
    "person_time_cohort": "rate_exposed = rate_unexposed",
}

# Bound into certificates and derivations; methods/identify.py recognises each one.
COHORT_GROUPS = (
    "The exposed and unexposed groups were sampled separately, in the declared numbers, "
    "before outcomes occurred."
)
CASE_CONTROL_GROUPS = (
    "Cases and controls were sampled separately, in the declared numbers, without regard "
    "to exposure."
)
RANDOM_SAMPLE = (
    "Participants were sampled independently from one population, in the declared number; "
    "how many are exposed is not fixed."
)
INDEPENDENT_OUTCOMES = (
    "Participants' outcomes are independent of one another, and within each group everyone "
    "has the same probability of the outcome."
)
INDEPENDENT_EXPOSURES = (
    "Participants' exposures are independent of one another, and among cases, as among "
    "controls, everyone has the same probability of having been exposed."
)
SOURCE_POPULATION = (
    "Controls come from the population that gave rise to the cases; otherwise the null "
    "concerns the groups sampled, not that population."
)
COHORT_NULL = (
    "The error bound is under the null of no association: the same risk of the outcome with "
    "and without exposure, for every common risk."
)
CASE_CONTROL_NULL = (
    "The error bound is under the null of no association: exposure as common among cases as "
    "among controls, an odds ratio of 1."
)
CROSS_SECTIONAL_NULL = (
    "The error bound is under the null of no association: exposure and outcome independent, "
    "so the outcome is as common with exposure as without it."
)
NOT_CAUSAL = (
    "The bound concerns association, not an effect of the exposure: exposure was not "
    "assigned, so confounding is not excluded."
)
GROUP_THEOREMS = ["checked_sizes", "checked_typeI"]
MIXTURE_THEOREMS = ["checked_size", "checked_law", "checked_typeI"]
GROUP_THEOREM = "StatClaim.Modules.Association.groups_typeI_le_alpha"
MIXTURE_THEOREM = "StatClaim.Modules.Association.mixture_typeI_le_alpha"


def null_statement(design: str) -> str:
    return NULL_STATEMENTS[design]


@dataclass(frozen=True)
class AssociationTest:
    """Fisher's exact test of no association for one declared observational study.

    `groups` is (unexposed, exposed) for a cohort and (controls, cases) for a case-control
    study, when the design fixes them; otherwise `n` is the total.
    """

    design: str
    alpha: Fraction
    groups: tuple[int, int] | None = None
    n: int | None = None
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        validate_alpha(self.alpha)
        if self.design not in DESIGNS:
            raise ValueError(f"Unknown observational design {self.design!r}.")
        if (self.groups is None) == (self.n is None):
            raise ValueError("Declare either the two group sizes or the total, not both.")
        if self.design == "case_control" and self.groups is None:
            raise ValueError("A case-control study fixes the numbers of cases and controls.")
        if self.design == "cross_sectional" and self.n is None:
            raise ValueError("A cross-sectional study fixes only the total.")
        sizes = self.groups if self.groups is not None else (self.n,)
        if len(sizes) not in (1, 2) or any(type(s) is not int or s < 1 for s in sizes):
            raise ValueError("Each declared size must be a positive whole number.")
        if sum(sizes) > MAX_PARTICIPANTS:
            raise ValueError(f"At most {MAX_PARTICIPANTS} participants are supported.")
        for name in (self.exposure, self.outcome):
            if not isinstance(name, str) or not NAME.fullmatch(name):
                raise ValueError("Exposure and outcome names are short plain words.")

    @property
    def fixed_groups(self) -> bool:
        return self.groups is not None

    @property
    def total(self) -> int:
        return sum(self.groups) if self.groups is not None else self.n

    def describe(self) -> str:
        if self.design == "case_control":
            controls, cases = self.groups
            return f"{cases} cases of {self.outcome} and {controls} controls"
        if self.groups is not None:
            unexposed, exposed = self.groups
            return f"{exposed} exposed to {self.exposure} and {unexposed} not"
        kind = "cross-sectional sample" if self.design == "cross_sectional" else "cohort"
        return f"a {kind} of {self.n}, with the number exposed to {self.exposure} not fixed"


def association_payload(test: AssociationTest) -> dict:
    design = {
        "kind": test.design,
        "exposure": test.exposure,
        "outcome": test.outcome,
        "stopping": "fixed",
    }
    if test.groups is not None:
        design["groups"] = list(test.groups)
    else:
        design["n"] = test.n
    return {
        "schema_version": 1,
        "scope": "association_test",
        "design": design,
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": NULL_ID,
            "alpha": str(test.alpha),
        },
    }


def parse_association_payload(payload: dict) -> AssociationTest:
    design, analysis = payload["design"], payload["analysis"]
    groups = design.get("groups")
    test = AssociationTest(
        design["kind"],
        parse_alpha(analysis["alpha"]),
        tuple(groups) if isinstance(groups, list) else groups,
        design.get("n"),
        design["exposure"],
        design["outcome"],
    )
    if payload != association_payload(test):
        raise ValueError("Bound association-test inputs are inconsistent.")
    return test


def association_assumptions(test: AssociationTest) -> tuple[str, ...]:
    """How the study sampled, independence, the prespecified analysis and the null."""
    if test.design == "case_control":
        return (
            CASE_CONTROL_GROUPS,
            INDEPENDENT_EXPOSURES,
            SOURCE_POPULATION,
            PRESPECIFIED,
            CASE_CONTROL_NULL,
        )
    sampled = COHORT_GROUPS if test.groups is not None else RANDOM_SAMPLE
    null = CROSS_SECTIONAL_NULL if test.design == "cross_sectional" else COHORT_NULL
    return (sampled, INDEPENDENT_OUTCOMES, PRESPECIFIED, null)


def association_theorems(test: AssociationTest) -> list[str]:
    return GROUP_THEOREMS if test.fixed_groups else MIXTURE_THEOREMS


def general_theorem(test: AssociationTest) -> str:
    return GROUP_THEOREM if test.fixed_groups else MIXTURE_THEOREM


def null_words(test: AssociationTest) -> str:
    exposure, outcome = test.exposure, test.outcome
    if test.design == "case_control":
        return f"{exposure} is as common among cases of {outcome} as among controls (odds ratio 1)"
    noun = "prevalence" if test.design == "cross_sectional" else "risk"
    return f"the {noun} of {outcome} is the same with and without {exposure}"


def association_claims(test: AssociationTest) -> list[str]:
    alpha, exposure, outcome = test.alpha, test.exposure, test.outcome
    test_words = f"Fisher's exact test of no association between {exposure} and {outcome}"
    if test.design == "case_control":
        controls, cases = test.groups
        return [
            f"The numbers of cases ({cases}) and controls ({controls}) that the design fixes "
            "are Lean checked.",
            f"{test_words} has Type I error at most {alpha} whenever {null_words(test)}, for "
            "every common probability of exposure in [0, 1].",
        ]
    if test.groups is not None:
        unexposed, exposed = test.groups
        return [
            f"The group sizes that the cohort fixes, {exposed} exposed to {exposure} and "
            f"{unexposed} not, are Lean checked.",
            f"{test_words} has Type I error at most {alpha} whenever {null_words(test)}, for "
            f"every common risk in [0, 1].",
        ]
    return [
        f"The sample size, {test.n}, is Lean checked; how many are exposed is not fixed, and "
        "the law of the table under no association is a probability law.",
        f"Given the number exposed, {test_words} rejects with probability at most {alpha}; "
        f"averaged over the number exposed, its Type I error is at most {alpha} whenever "
        f"{null_words(test)}, for every probability of exposure and every common probability "
        f"of {outcome} in [0, 1].",
    ]


def render_association_proof(test: AssociationTest, input_sha256: str) -> str:
    """Only validated integers and one rational level enter the template; the exposure and
    outcome names never do."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    numerator, denominator = test.alpha.as_integer_ratio()
    header = f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- An observational {test.design.replace("_", "-")} study. The theorem covers every probability
-- under no association; nothing here depends on observed data.
namespace StatClaimCertificate
open StatClaim StatClaim.Modules

def declaredLevel : SignificanceLevel :=
  ⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩
"""
    if test.groups is not None:
        first, second = test.groups
        body = f"""
-- The two groups the design fixes: (unexposed, exposed) or (controls, cases).
def firstGroup : ℕ := {first}
def secondGroup : ℕ := {second}

theorem checked_sizes : firstGroup = {first} ∧ secondGroup = {second} ∧ 0 < firstGroup ∧
    0 < secondGroup := by decide

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw firstGroup secondGroup p).real
        (fisherRejectionRegionAt firstGroup secondGroup declaredLevel.value) ≤
      (declaredLevel.value : ℝ) :=
  Association.groups_typeI_le_alpha firstGroup secondGroup p declaredLevel.value
    declaredLevel.nonnegative
"""
    else:
        body = f"""
-- Only the total is fixed; the number exposed is binomial.
def sampleSize : ℕ := {test.n}

theorem checked_size : sampleSize = {test.n} ∧ 0 < sampleSize := by decide

theorem checked_law (q p : unitInterval) :
    Association.mixtureLaw sampleSize q p Set.univ = 1 :=
  Association.mixtureLaw_univ sampleSize q p

theorem checked_typeI (q p : unitInterval) :
    (Association.mixtureLaw sampleSize q p).real
        (Association.mixtureRejection sampleSize declaredLevel.value) ≤
      (declaredLevel.value : ℝ) :=
  Association.mixture_typeI_le_alpha sampleSize q p declaredLevel.value
    declaredLevel.nonnegative
"""
    return f"""{header}{body}
end StatClaimCertificate
{_audit(association_theorems(test), input_sha256)}"""


# Observed tables -------------------------------------------------------------------------
@dataclass(frozen=True)
class AssociationTable:
    """An observed 2x2 table of one declared observational study. Cases have the outcome.

    The table must fit what the design fixed: a cohort's group sizes, a case-control
    study's numbers of cases and controls, or the total.
    """

    design: str
    cells: tuple[int, int, int, int]
    groups: tuple[int, int] | None = None
    n: int | None = None
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        AssociationTest(
            self.design, Fraction(1, 20), self.groups, self.n, self.exposure, self.outcome
        )
        if len(self.cells) != 4 or any(type(c) is not int or c < 0 for c in self.cells):
            raise ValueError("Each cell of the table is a whole number, zero or more.")
        problem = table_problem(self.design, self.groups, self.n, self.cells)
        if problem:
            raise ValueError(problem)

    @property
    def fixed_groups(self) -> bool:
        return self.groups is not None

    @property
    def conditional(self) -> tuple[int, int, int, int]:
        """The two groups the test and intervals compare, given the table's margins:
        (first size, second size, first count, second count). For a cohort or a survey the
        groups are unexposed and exposed, counting cases; for a case-control study they are
        controls and cases, counting the exposed."""
        a, b, c, d = self.cells
        if self.design == "case_control":
            return (b + d, a + c, b, a)
        return (c + d, a + b, c, a)

    @property
    def exposed(self) -> int:
        a, b, _, _ = self.cells
        return a + b

    def named(self) -> dict:
        return dict(zip(CELLS, self.cells, strict=True))

    def describe(self) -> str:
        a, b, c, d = self.cells
        return (
            f"{a} exposed and {c} unexposed cases of {self.outcome}; {b} exposed and {d} "
            "unexposed without it"
        )


def table_problem(design, groups, n, cells) -> str | None:
    """Why a table does not fit what the design fixed, or None when it fits."""
    a, b, c, d = cells
    total = a + b + c + d
    if total > MAX_TABLE:
        return f"An observed table may have at most {MAX_TABLE} participants."
    if design == "case_control":
        controls, cases = groups
        if (a + c, b + d) != (cases, controls):
            return (
                f"The table has {a + c} cases and {b + d} controls; the study sampled {cases} "
                f"cases and {controls} controls."
            )
        return None
    if groups is not None:
        unexposed, exposed = groups
        if (a + b, c + d) != (exposed, unexposed):
            return (
                f"The table has {a + b} exposed and {c + d} unexposed; the cohort followed "
                f"{exposed} exposed and {unexposed} unexposed."
            )
        return None
    if total != n:
        return f"The table has {total} participants; the study sampled {n}."
    if a + b == 0 or c + d == 0:
        return (
            "The table needs at least one exposed and one unexposed participant: with "
            "everyone in one group there is nothing to compare."
        )
    return None


def table_record(table: AssociationTable) -> dict:
    design = {
        "kind": table.design,
        "exposure": table.exposure,
        "outcome": table.outcome,
        "stopping": "fixed",
    }
    if table.groups is not None:
        design["groups"] = list(table.groups)
    else:
        design["n"] = table.n
    return design


def _table_from(design: dict, cells: dict) -> AssociationTable:
    groups = design.get("groups")
    return AssociationTable(
        design["kind"],
        tuple(cells[name] for name in CELLS),
        tuple(groups) if isinstance(groups, list) else groups,
        design.get("n"),
        design["exposure"],
        design["outcome"],
    )


@dataclass(frozen=True)
class AssociationResult:
    """Fisher's exact test applied to an observed table: its p-value and decision."""

    test: AssociationTest
    table: AssociationTable

    def __post_init__(self):
        same = (
            self.test.design,
            self.test.groups,
            self.test.n,
            self.test.exposure,
            self.test.outcome,
        )
        table = (self.table.design, self.table.groups, self.table.n, self.table.exposure)
        if same[:4] != table or same[4] != self.table.outcome:
            raise ValueError("The table belongs to another study than the test.")

    @property
    def fisher(self) -> FisherResult:
        first, second, x, y = self.table.conditional
        return fisher_exact(
            n_control=first,
            n_treatment=second,
            control_successes=x,
            treatment_successes=y,
            alpha=self.test.alpha,
        )

    def evaluate(self) -> dict:
        result = self.fisher
        return {
            **self.table.named(),
            "p_value": fraction_record(result.p_value),
            "observed_table_probability": fraction_record(result.observed_table_probability),
            "alpha": fraction_record(self.test.alpha),
            "reject_null": result.reject_null,
            "test": TEST_ID,
        }


def result_payload(result: AssociationResult) -> dict:
    fisher = result.fisher
    payload = association_payload(result.test)
    payload["scope"] = "association_result"
    payload["table"] = result.table.named()
    payload["result"] = {
        "p_value": str(fisher.p_value),
        "observed_table_probability": str(fisher.observed_table_probability),
        "support": [fisher.support_min, fisher.support_max],
        "reject_null": fisher.reject_null,
    }
    return payload


def parse_result_payload(payload: dict) -> AssociationResult:
    test_payload = {k: v for k, v in payload.items() if k not in ("table", "result")}
    test_payload["scope"] = "association_test"
    test = parse_association_payload(test_payload)
    result = AssociationResult(test, _table_from(payload["design"], payload["table"]))
    if payload != result_payload(result):
        raise ValueError("Bound association-result inputs are inconsistent.")
    return result


def result_claims(result: AssociationResult) -> list[str]:
    fisher = result.fisher
    decision = "rejects" if fisher.reject_null else "does not reject"
    given = (
        ""
        if result.table.fixed_groups
        else f", given the {result.table.exposed} exposed in the table"
    )
    return [
        f"For the observed table ({result.table.describe()}), the exact two-sided p-value "
        f"equals the Lean Fisher definition{given}: {fisher.p_value} "
        f"(about {float(fisher.p_value):.4g}).",
        f"The observed table's probability and support equal the Lean definitions, and the "
        f"test {decision} no association at level {result.test.alpha}, as membership in the "
        "formal rejection event says.",
        association_claims(result.test)[-1],
    ]


def result_assumptions(result: AssociationResult) -> tuple[str, ...]:
    return (*association_assumptions(result.test), TABLE_MATCHES)


TABLE_MATCHES = "The supplied table describes the declared study."
RESULT_THEOREMS = ["checked_p_value", "checked_table_probability", "checked_decision"]


def _result_checks(result: AssociationResult) -> str:
    fisher = result.fisher
    first, second, x, y = result.table.conditional
    total = x + y
    numerator, denominator = fisher.p_value.as_integer_ratio()
    table_num, table_den = fisher.observed_table_probability.as_integer_ratio()
    an, ad = result.test.alpha.as_integer_ratio()
    truth = "True" if fisher.reject_null else "False"
    if result.table.fixed_groups:
        membership = f"(({x}, {y}) ∈ fisherRejectionRegionAt {first} {second} (({an} : ℚ) / {ad}))"
        unfold = ""
    else:
        k = result.table.exposed
        membership = (
            f"(({k}, ({x}, {y})) ∈ Association.mixtureRejection sampleSize (({an} : ℚ) / {ad}))"
        )
        unfold = (
            "  simp only [Association.mixtureRejection, Association.given, Set.mem_setOf_eq,\n"
            "    sampleSize, Finset.mem_coe]\n"
            f"  rw [show {result.table.n} - {k} = {first} from rfl]\n"
            f"  refine (and_iff_right (by decide : {k} ≤ {result.table.n})).trans ?_\n"
        )
    return f"""
-- The observed table: {x} of {first} and {y} of {second}, given its margins.
theorem checked_p_value : hypergeometricPValue {first} {second} {total} {x} =
    ({numerator} : ℚ) / {denominator} := by
  apply hypergeometricPValue_eq_of_cross_product {first} {second} {total} {x}
    {numerator} {denominator} (by decide) (by decide)
  decide +kernel

theorem checked_table_probability : hypergeometricMass {first} {second} {total} {x} =
    ({table_num} : ℚ) / {table_den} := by
  apply hypergeometricMass_eq_of_cross_product {first} {second} {total} {x}
    {table_num} {table_den} (by decide) (by decide)
  decide +kernel

theorem checked_decision : {membership} ↔ {truth} := by
{unfold}  simp only [fisherRejectionRegionAt, Finset.mem_filter, binomialCountSupport,
    Finset.mem_product, Finset.mem_range]
  rw [checked_p_value]
  norm_num
"""


def render_result_proof(result: AssociationResult, input_sha256: str) -> str:
    """The design's Type I theorem and the checked p-value and decision for the table."""
    design = render_association_proof(result.test, input_sha256)
    head, _, _ = design.partition("\nend StatClaimCertificate")
    theorems = association_theorems(result.test) + RESULT_THEOREMS
    return (
        head.replace(
            "namespace StatClaimCertificate",
            "set_option maxRecDepth 8192\n"
            "set_option maxHeartbeats 2000000\n\nnamespace StatClaimCertificate",
            1,
        )
        + _result_checks(result)
        + f"\nend StatClaimCertificate\n{_audit(theorems, input_sha256)}"
    )


# Effect measures -------------------------------------------------------------------------
# What each design can estimate. A case-control study fixed how many have the outcome, so
# only odds ratios; a cohort measures risk over follow-up; a survey measures prevalence.
MEASURES = {
    "odds_ratio": ("odds ratio", "odds", ("cross_sectional", "cohort", "case_control")),
    "risk_ratio": ("risk ratio", "ratio", ("cohort",)),
    "risk_difference": ("risk difference", "difference", ("cohort",)),
    "prevalence_ratio": ("prevalence ratio", "ratio", ("cross_sectional",)),
    "prevalence_difference": ("prevalence difference", "difference", ("cross_sectional",)),
}
ODDS_IDENTITY = (
    "The odds ratio of exposure between cases and controls equals the odds ratio of the "
    "outcome between exposed and unexposed in the source population; this holds when "
    "cases and controls are sampled without regard to exposure."
)
INTERVAL_LEVEL = "The confidence level was chosen before the data were seen."
INTERVAL_THEOREMS = ["checked_coverage", "checked_interval"]


def not_estimable(measure: str, design: str) -> str | None:
    """Why a design cannot estimate a measure, with what it can estimate instead."""
    words, _, designs = MEASURES[measure]
    if design in designs:
        return None
    if design == "case_control":
        return (
            f"A case-control study fixed how many have the outcome, so it cannot estimate "
            f"risk or prevalence, or the {words}. Use odds_ratio; when the outcome is rare "
            "in the population, the odds ratio approximates the risk ratio."
        )
    if design == "cross_sectional":
        return (
            f"A cross-sectional study measures prevalence, not risk, so it has no {words}. "
            f"Use {measure.replace('risk', 'prevalence')} or odds_ratio."
        )
    return (
        f"A cohort measures risk over follow-up, not prevalence at one time, so it has no "
        f"{words}. Use {measure.replace('prevalence', 'risk')} or odds_ratio."
    )


def _odds(value: Fraction) -> Fraction:
    return value / (1 - value)


@dataclass(frozen=True)
class EffectInterval:
    """An interval for an effect measure, from exact intervals for each group's
    probability. Both hold together with at least the requested level; the measure then
    lies between the values at the ends. Valid for every pair of probabilities, and wide.
    """

    measure: str
    table: AssociationTable
    level: Fraction

    def __post_init__(self):
        if self.measure not in MEASURES:
            raise ValueError(f"Unknown effect measure {self.measure!r}.")
        reason = not_estimable(self.measure, self.table.design)
        if reason:
            raise ValueError(reason)
        first, second, _, _ = self.table.conditional
        if max(first, second) > MAX_ONE_ARM:
            raise ValueError(f"Exact intervals support up to {MAX_ONE_ARM} per group.")
        _ = self.groups  # constructing the groups validates the level

    @property
    def groups(self) -> DifferenceInterval:
        first, second, x, y = self.table.conditional
        return DifferenceInterval(first, second, x, y, self.level)

    @property
    def kind(self) -> str:
        return MEASURES[self.measure][1]

    @property
    def bounds(self) -> tuple[Fraction, Fraction | None]:
        """The interval; None for an upper end without a finite bound."""
        groups = self.groups
        c, t = groups.control, groups.treatment
        if self.kind == "difference":
            return groups.lower, groups.upper
        if self.kind == "ratio":
            return t.lower / c.upper, (t.upper / c.lower if c.lower > 0 else None)
        lower = Fraction(0) if c.upper == 1 else _odds(t.lower) / _odds(c.upper)
        upper = _odds(t.upper) / _odds(c.lower) if c.lower > 0 and t.upper < 1 else None
        return lower, upper

    @property
    def estimate(self) -> Fraction | None:
        first, second, x, y = self.table.conditional
        if self.kind == "difference":
            return Fraction(y, second) - Fraction(x, first)
        if self.kind == "ratio":
            return Fraction(y * first, second * x) if x else None
        a, b = y, second - y
        c, d = x, first - x
        return Fraction(a * d, b * c) if b * c else None

    def evaluate(self) -> dict:
        lower, upper = self.bounds
        estimate = self.estimate
        return {
            "measure": self.measure,
            **self.table.named(),
            "level": fraction_record(self.level),
            "arm_level": fraction_record(self.groups.arm_level),
            "estimate": fraction_record(estimate) if estimate is not None else None,
            "lower": fraction_record(lower),
            "upper": fraction_record(upper) if upper is not None else None,
            "method": "two_exact_intervals",
        }


def interval_payload(interval: EffectInterval) -> dict:
    lower, upper = interval.bounds
    return {
        "schema_version": 1,
        "scope": "effect_interval",
        "design": table_record(interval.table),
        "table": interval.table.named(),
        "interval": {
            "measure": interval.measure,
            "level": str(interval.level),
            "arm_level": str(interval.groups.arm_level),
            "lower": str(lower),
            "upper": None if upper is None else str(upper),
        },
    }


def parse_interval_payload(payload: dict) -> EffectInterval:
    table = _table_from(payload["design"], payload["table"])
    interval = EffectInterval(
        payload["interval"]["measure"], table, Fraction(payload["interval"]["level"])
    )
    if payload != interval_payload(interval):
        raise ValueError("Bound effect-interval inputs are inconsistent.")
    return interval


def _number(value: Fraction) -> str:
    return f"{float(value):.4g}"


def interval_claims(interval: EffectInterval) -> list[str]:
    words = MEASURES[interval.measure][0]
    table = interval.table
    lower, upper = interval.bounds
    probabilities = (
        "probabilities of exposure among cases and controls"
        if table.design == "case_control"
        else f"probabilities of {table.outcome} with and without {table.exposure}"
    )
    coverage = (
        f"For every pair of true {probabilities}, both groups' exact confidence sets contain "
        f"them with probability at least {interval.level}."
    )
    if not table.fixed_groups:
        coverage = (
            f"With the number exposed random, for every probability of exposure and every pair "
            f"of true {probabilities}, both groups' exact confidence sets contain them with "
            f"probability at least {interval.level}, averaged over the number exposed."
        )
    span = (
        f"[{_number(lower)}, {_number(upper)}]"
        if upper is not None
        else (f"[{_number(lower)}, no finite upper bound)")
    )
    condition = {
        "difference": "",
        "ratio": ", for any positive probability in the reference group",
        "odds": ", for probabilities strictly between 0 and 1 in the reference group and "
        "below 1 in the other",
    }[interval.kind]
    return [
        coverage,
        f"For the observed table ({table.describe()}), whenever both sets contain the true "
        f"probabilities, the {words} lies within {span}{condition}.",
    ]


def interval_assumptions(interval: EffectInterval) -> tuple[str, ...]:
    test = AssociationTest(
        interval.table.design,
        Fraction(1, 20),
        interval.table.groups,
        interval.table.n,
        interval.table.exposure,
        interval.table.outcome,
    )
    sampling = tuple(
        a for a in association_assumptions(test) if a not in NULLS and a != PRESPECIFIED
    )
    extra = (ODDS_IDENTITY,) if interval.table.design == "case_control" else ()
    return (*sampling, *extra, INTERVAL_LEVEL, TABLE_MATCHES)


NULLS = {COHORT_NULL, CASE_CONTROL_NULL, CROSS_SECTIONAL_NULL}


def render_interval_proof(interval: EffectInterval, input_sha256: str) -> str:
    """Coverage is a general theorem; the endpoints for this table are kernel checked."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    groups = interval.groups
    first, second, x, y = interval.table.conditional
    an, ad = groups.control.tail_level.as_integer_ratio()
    ln, ld = interval.level.as_integer_ratio()
    tail = f"((({an} : ℕ) : ℝ) / (({ad} : ℕ) : ℝ))"
    ends, checks = [], []
    for arm in (groups.control, groups.treatment):
        (lower_n, lower_d), (upper_n, upper_d) = (
            arm.lower.as_integer_ratio(),
            arm.upper.as_integer_ratio(),
        )
        ends.append((lower_n, lower_d, upper_n, upper_d))
        checks.append("(Or.inl rfl)" if lower_n == 0 else "(Or.inr (by decide +kernel))")
        checks.append("(Or.inl rfl)" if upper_n == upper_d else "(Or.inr (by decide +kernel))")
    (cln, cld, cun, cud), (tln, tld, tun, tud) = ends
    endpoints = " ".join(
        f"{num} {den} (by decide) (by decide)"
        for num, den in ((cln, cld), (cun, cud), (tln, tld), (tun, tud))
    )
    arguments = (
        f"{first} {second} {x} {y} {an} {ad} (by decide)\n    {endpoints}\n    {' '.join(checks)}"
    )
    r = lambda num, den: f"((({num} : ℕ) : ℝ) / (({den} : ℕ) : ℝ))"  # noqa: E731
    if interval.table.fixed_groups:
        law = f"(productBinomial {first} {second} pc pt)"
        events = (
            f"({{a | pc ∈ BinomialInterval.confidenceSet {first} {tail} a}} ×ˢ\n"
            f"        {{b | pt ∈ BinomialInterval.confidenceSet {second} {tail} b}})"
        )
        coverage = f"""theorem checked_coverage (pc pt : unitInterval) :
    ((({ln} : ℕ) : ℝ) / (({ld} : ℕ) : ℝ)) ≤ {law}.real
      {events} := by
  have joint := BinomialInterval.joint_coverage {first} {second} {tail} (by positivity)
    (by norm_num) pc pt
  exact le_trans (by norm_num) joint"""
    else:
        n = interval.table.n
        coverage = f"""def sampleSize : ℕ := {n}

theorem checked_coverage (q pc pt : unitInterval) :
    ((({ln} : ℕ) : ℝ) / (({ld} : ℕ) : ℝ)) ≤
      (Association.mixture sampleSize q (fun k => productBinomial (sampleSize - k) k pc pt)).real
        (Association.given sampleSize (fun k =>
          {{a | pc ∈ BinomialInterval.confidenceSet (sampleSize - k) {tail} a}} ×ˢ
            {{b | pt ∈ BinomialInterval.confidenceSet k {tail} b}})) := by
  have joint := Association.mixture_joint_coverage sampleSize {tail} (by positivity)
    (by norm_num) q pc pt
  exact le_trans (by norm_num) joint"""
    hypotheses = (
        f"(pc pt : unitInterval)\n"
        f"    (control : pc ∈ BinomialInterval.confidenceSet {first} {tail} {x})\n"
        f"    (treatment : pt ∈ BinomialInterval.confidenceSet {second} {tail} {y})"
    )
    if interval.kind == "difference":
        statement = (
            f"{r(tln, tld)} - {r(cun, cud)} ≤ (pt : ℝ) - (pc : ℝ) ∧\n"
            f"      (pt : ℝ) - (pc : ℝ) ≤ {r(tun, tud)} - {r(cln, cld)}"
        )
        body = f"  exact BinomialInterval.difference_contains {arguments} pc pt control treatment"
    elif interval.kind == "ratio":
        hypotheses += "\n    (positive : 0 < (pc : ℝ))"
        lower = f"{r(tln, tld)} / {r(cun, cud)} ≤ (pt : ℝ) / pc"
        bound = f"Association.ratio_contains {arguments} pc pt control treatment positive"
        if cln > 0:
            statement = f"{lower} ∧\n      (pt : ℝ) / pc ≤ {r(tun, tud)} / {r(cln, cld)}"
            body = f"  have bound := {bound}\n  exact ⟨bound.1, bound.2 (by decide)⟩"
        else:
            statement = lower
            body = f"  exact ({bound}).1"
    else:
        hypotheses += (
            "\n    (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1)"
        )
        ratio = "Association.odds pt / Association.odds pc"
        lower = (
            f"Association.odds {r(tln, tld)} / Association.odds {r(cun, cud)} ≤ {ratio}"
            if cun < cud
            else f"0 ≤ {ratio}"
        )
        bound = (
            f"Association.odds_ratio_contains {arguments} pc pt control treatment positive "
            "below treatedBelow"
        )
        lower_proof = "bound.2.1 (by decide)" if cun < cud else "bound.1"
        if cln > 0 and tun < tud:
            statement = (
                f"{lower} ∧\n      {ratio} ≤ Association.odds {r(tun, tud)} / "
                f"Association.odds {r(cln, cld)}"
            )
            body = (
                f"  have bound := {bound}\n"
                f"  exact ⟨{lower_proof}, bound.2.2 (by decide) (by decide)⟩"
            )
        else:
            statement = lower
            body = f"  have bound := {bound}\n  exact {lower_proof}"
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical interval SHA-256: {input_sha256}
-- Coverage is a general theorem; the endpoints for this table are confirmed by the kernel.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

{coverage}

theorem checked_interval {hypotheses} :
    {statement} := by
{body}

end StatClaimCertificate
{_audit(INTERVAL_THEOREMS, input_sha256)}"""
