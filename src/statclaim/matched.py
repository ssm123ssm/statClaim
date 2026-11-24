"""McNemar's exact test and the conditional odds ratio for 1:1 matched case-control studies.

Each pair is one case and one control matched on chosen characteristics. Only discordant
pairs, where exactly one of the two was exposed, carry information. Given `d` of them,
the number in which the case is the exposed one is binomial; no association within pairs
makes its probability one half. Lean proves the test's level given `d`, and on average
over `d` (StatClaim.Modules.Matched); a certificate instantiates it for the declared
number of pairs. The interval for that probability gives one for the conditional odds
ratio, its odds.
"""

import re
from dataclasses import dataclass
from fractions import Fraction
from math import comb

from statclaim.association import NAME, SOURCE_POPULATION
from statclaim.fisher import fraction_record, parse_alpha, validate_alpha
from statclaim.lean_translation import statements as S
from statclaim.lean_translation.statements import CERTIFICATE as C
from statclaim.planning import MAX_ONE_ARM, BinomialInterval, _audit
from statclaim.randomisation import PRESPECIFIED

MATCHED_KIND = "statclaim_matched_certificate"
MATCHED_RESULT_KIND = "statclaim_matched_result_certificate"
MATCHED_INTERVAL_KIND = "statclaim_matched_interval_certificate"
TEST_ID = "mcnemar_exact"
TEST_VERSION = "0.1.0"
NULL_STATEMENT = "conditional_odds_ratio = 1"
MAX_PAIRS = 1_000_000
# Discordant pairs in an observed table: its binomial tails are checked term by term.
MAX_DISCORDANT = MAX_ONE_ARM
PAIR_CELLS = ("both_exposed", "case_exposed_only", "control_exposed_only", "neither_exposed")

# Bound into certificates and derivations; methods/identify.py recognises each one.
PAIRS_SAMPLED = (
    "Each case was matched to one control on the declared characteristics, and the pairs "
    "were sampled independently of one another, in the declared number."
)
WITHIN_PAIRS = (
    "In every discordant pair the case has the same probability of being the exposed one: "
    "one conditional odds ratio for all pairs."
)
MATCHED_NULL = (
    "The error bound is under the null of no association within pairs: in a discordant "
    "pair the case is as likely as the control to be the exposed one, a conditional odds "
    "ratio of 1."
)
PAIRS_MATCH = "The supplied pairs describe the declared study."
INTERVAL_LEVEL = "The confidence level was chosen before the data were seen."
GENERAL_THEOREM = "StatClaim.Modules.Matched.typeI"
DESIGN_THEOREMS = ["checked_size", "checked_law", "checked_typeI"]
RESULT_THEOREMS = ["checked_tails", "checked_decision"]
INTERVAL_THEOREMS = ["checked_coverage", "checked_interval"]


def _name(value: str) -> None:
    if not isinstance(value, str) or not NAME.fullmatch(value):
        raise ValueError("Exposure and outcome names are short plain words.")


@dataclass(frozen=True)
class MatchedTest:
    """McNemar's exact test of no association within pairs, for one declared study."""

    pairs: int
    alpha: Fraction
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        validate_alpha(self.alpha)
        if type(self.pairs) is not int or not 1 <= self.pairs <= MAX_PAIRS:
            raise ValueError(f"The number of pairs must be a whole number from 1 to {MAX_PAIRS}.")
        _name(self.exposure)
        _name(self.outcome)


@dataclass(frozen=True)
class MatchedPairs:
    """Observed pairs, classified by who was exposed."""

    pairs: int
    cells: tuple[int, int, int, int]
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        MatchedTest(self.pairs, Fraction(1, 20), self.exposure, self.outcome)
        if len(self.cells) != 4 or any(type(c) is not int or c < 0 for c in self.cells):
            raise ValueError("Each count of pairs is a whole number, zero or more.")
        problem = pairs_problem(self.pairs, self.cells)
        if problem:
            raise ValueError(problem)

    @property
    def discordant(self) -> int:
        _, b, c, _ = self.cells
        return b + c

    @property
    def case_exposed(self) -> int:
        return self.cells[1]

    def named(self) -> dict:
        return dict(zip(PAIR_CELLS, self.cells, strict=True))

    def describe(self) -> str:
        both, b, c, neither = self.cells
        return (
            f"{b} pairs with only the case exposed and {c} with only the control, of "
            f"{self.discordant} discordant; {both} with both and {neither} with neither"
        )


def pairs_problem(pairs: int, cells) -> str | None:
    total = sum(cells)
    if total != pairs:
        return f"The observed pairs add up to {total}; the study matched {pairs}."
    if cells[1] + cells[2] > MAX_DISCORDANT:
        return f"At most {MAX_DISCORDANT} discordant pairs are supported."
    return None


def matched_payload(test: MatchedTest) -> dict:
    return {
        "schema_version": 1,
        "scope": "matched_test",
        "design": {
            "kind": "matched_case_control",
            "pairs": test.pairs,
            "exposure": test.exposure,
            "outcome": test.outcome,
            "stopping": "fixed",
        },
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": "no_association",
            "alpha": str(test.alpha),
        },
    }


def parse_matched_payload(payload: dict) -> MatchedTest:
    design = payload["design"]
    test = MatchedTest(
        design["pairs"],
        parse_alpha(payload["analysis"]["alpha"]),
        design["exposure"],
        design["outcome"],
    )
    if payload != matched_payload(test):
        raise ValueError("Bound matched-test inputs are inconsistent.")
    return test


def matched_assumptions(test: MatchedTest | None = None) -> tuple[str, ...]:
    return (PAIRS_SAMPLED, WITHIN_PAIRS, SOURCE_POPULATION, PRESPECIFIED, MATCHED_NULL)


def null_words(test: MatchedTest) -> str:
    return (
        f"the case of {test.outcome} is as likely as its control to be the one exposed to "
        f"{test.exposure} in a discordant pair"
    )


def matched_claims(test: MatchedTest) -> list[str]:
    return [
        f"The number of pairs, {test.pairs}, is Lean checked; how many are discordant is not "
        "fixed, and the law of the pairs is a probability law.",
        f"Given the number of discordant pairs, McNemar's exact test of no association "
        f"between {test.exposure} and {test.outcome} rejects with probability at most "
        f"{test.alpha}; averaged over that number, its Type I error is at most {test.alpha} "
        f"whenever {null_words(test)}, for every probability that a pair is discordant.",
    ]


def _level(alpha: Fraction) -> str:
    numerator, denominator = alpha.as_integer_ratio()
    return f"""def declaredLevel : SignificanceLevel :=
  ⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩"""


def _design_body(test: MatchedTest) -> str:
    return f"""
def pairs : ℕ := {test.pairs}
{_level(test.alpha)}

{S.pairs_size("pairs", test.pairs).header()} := by decide

{S.pairs_law(C, "pairs").header()} :=
  Matched.pairsLaw_univ pairs δ π

{S.pairs_typeI(C, "pairs", "declaredLevel.value").header()} :=
  Matched.typeI pairs δ _ (by exact_mod_cast declaredLevel.nonnegative)
"""


def _header(input_sha256: str, what: str) -> str:
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- A 1:1 matched case-control study. {what}
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules
"""


def render_matched_proof(test: MatchedTest, input_sha256: str) -> str:
    """Only validated integers and one rational level enter the template."""
    return (
        _header(input_sha256, "The theorem covers every law under no association.")
        + _design_body(test)
        + f"\nend StatClaimCertificate\n{_audit(DESIGN_THEOREMS, input_sha256)}"
    )


# Observed pairs ---------------------------------------------------------------------------
def tails(discordant: int, case_exposed: int) -> tuple[int, int]:
    """Numerators of the upper and lower tails of the binomial law at one half; the
    denominator is 2 to the power of the number of discordant pairs."""
    weights = [comb(discordant, k) for k in range(discordant + 1)]
    return sum(weights[case_exposed:]), sum(weights[: case_exposed + 1])


@dataclass(frozen=True)
class MatchedResult:
    """McNemar's exact test applied to the observed pairs: its p-value and decision."""

    test: MatchedTest
    observed: MatchedPairs

    def __post_init__(self):
        if (self.test.pairs, self.test.exposure, self.test.outcome) != (
            self.observed.pairs,
            self.observed.exposure,
            self.observed.outcome,
        ):
            raise ValueError("The pairs belong to another study than the test.")

    @property
    def doubled_tail(self) -> Fraction:
        """Twice the smaller tail; the test rejects when this is at most alpha."""
        d = self.observed.discordant
        upper, lower = tails(d, self.observed.case_exposed)
        return Fraction(2 * min(upper, lower), 2**d)

    @property
    def p_value(self) -> Fraction:
        return min(Fraction(1), self.doubled_tail)

    @property
    def reject_null(self) -> bool:
        return self.doubled_tail <= self.test.alpha

    def evaluate(self) -> dict:
        return {
            **self.observed.named(),
            "discordant_pairs": self.observed.discordant,
            "p_value": fraction_record(self.p_value),
            "alpha": fraction_record(self.test.alpha),
            "reject_null": self.reject_null,
            "test": TEST_ID,
        }


def result_payload(result: MatchedResult) -> dict:
    payload = matched_payload(result.test)
    payload["scope"] = "matched_result"
    payload["pairs"] = result.observed.named()
    payload["result"] = {"p_value": str(result.p_value), "reject_null": result.reject_null}
    return payload


def _pairs_from(design: dict, cells: dict) -> MatchedPairs:
    return MatchedPairs(
        design["pairs"],
        tuple(cells[name] for name in PAIR_CELLS),
        design["exposure"],
        design["outcome"],
    )


def parse_result_payload(payload: dict) -> MatchedResult:
    design_payload = {k: v for k, v in payload.items() if k not in ("pairs", "result")}
    design_payload["scope"] = "matched_test"
    result = MatchedResult(
        parse_matched_payload(design_payload), _pairs_from(payload["design"], payload["pairs"])
    )
    if payload != result_payload(result):
        raise ValueError("Bound matched-result inputs are inconsistent.")
    return result


def result_claims(result: MatchedResult) -> list[str]:
    decision = "rejects" if result.reject_null else "does not reject"
    return [
        f"For the observed pairs ({result.observed.describe()}), both binomial tails at one "
        f"half equal the Lean definitions; the exact two-sided p-value is {result.p_value} "
        f"(about {float(result.p_value):.4g}).",
        f"The test {decision} no association within pairs at level {result.test.alpha}, as "
        "membership in the formal rejection event says.",
        matched_claims(result.test)[-1],
    ]


def result_assumptions(result: MatchedResult) -> tuple[str, ...]:
    return (*matched_assumptions(result.test), PAIRS_MATCH)


def render_result_proof(result: MatchedResult, input_sha256: str) -> str:
    d, x = result.observed.discordant, result.observed.case_exposed
    upper, lower = tails(d, x)
    an, ad = result.test.alpha.as_integer_ratio()
    truth = "True" if result.reject_null else "False"
    checks = f"""
-- The observed pairs: {x} of {d} discordant pairs with the case exposed.
{S.tails(C, d, (1, 2), x, upper, lower).header()} := by
  constructor <;> decide +kernel

{S.pairs_decision(C, d, x, "pairs", "declaredLevel.value", truth).header()} := by
  simp only [Matched.pairsRejection, Association.given, Set.mem_ofPred_eq, Matched.rejection,
    Matched.half, pairs]
  rw [BinomialInterval.upper_tail_ratPoint, BinomialInterval.lower_tail_ratPoint,
    checked_tails.1, checked_tails.2,
    Incidence.twice_min_le_iff {upper} {lower} (2 ^ {d}) {an} {ad} _ (by positivity) (by decide)
      (by norm_num [declaredLevel])]
  decide +kernel
"""
    return (
        _header(input_sha256, "These observed pairs and the declared test.")
        + _design_body(result.test)
        + checks
        + f"\nend StatClaimCertificate\n{_audit(DESIGN_THEOREMS + RESULT_THEOREMS, input_sha256)}"
    )


# The conditional odds ratio ---------------------------------------------------------------
def _odds(value: Fraction) -> Fraction:
    return value / (1 - value)


@dataclass(frozen=True)
class MatchedInterval:
    """An interval for the conditional odds ratio, the odds of the case being the exposed
    one in a discordant pair, from the exact interval for that probability."""

    observed: MatchedPairs
    level: Fraction

    def __post_init__(self):
        if not isinstance(self.level, Fraction) or not 0 < self.level < 1:
            raise ValueError("The confidence level must lie strictly between 0 and 1.")
        if self.observed.discordant == 0:
            raise ValueError(
                "No pair is discordant, so the pairs carry no information about the odds ratio."
            )

    @property
    def binomial(self) -> BinomialInterval:
        return BinomialInterval(self.observed.discordant, self.observed.case_exposed, self.level)

    @property
    def bounds(self) -> tuple[Fraction, Fraction | None]:
        interval = self.binomial
        upper = _odds(interval.upper) if interval.upper < 1 else None
        return _odds(interval.lower), upper

    @property
    def estimate(self) -> Fraction | None:
        _, b, c, _ = self.observed.cells
        return Fraction(b, c) if c else None

    def evaluate(self) -> dict:
        lower, upper = self.bounds
        estimate = self.estimate
        return {
            "measure": "conditional_odds_ratio",
            **self.observed.named(),
            "level": fraction_record(self.level),
            "arm_level": fraction_record(self.level),
            "estimate": fraction_record(estimate) if estimate is not None else None,
            "lower": fraction_record(lower),
            "upper": fraction_record(upper) if upper is not None else None,
            "method": "exact_interval_discordant_pairs",
        }


def interval_payload(interval: MatchedInterval) -> dict:
    lower, upper = interval.bounds
    return {
        "schema_version": 1,
        "scope": "matched_interval",
        "design": {
            "kind": "matched_case_control",
            "pairs": interval.observed.pairs,
            "exposure": interval.observed.exposure,
            "outcome": interval.observed.outcome,
            "stopping": "fixed",
        },
        "pairs": interval.observed.named(),
        "interval": {
            "measure": "conditional_odds_ratio",
            "level": str(interval.level),
            "lower": str(lower),
            "upper": None if upper is None else str(upper),
        },
    }


def parse_interval_payload(payload: dict) -> MatchedInterval:
    interval = MatchedInterval(
        _pairs_from(payload["design"], payload["pairs"]), Fraction(payload["interval"]["level"])
    )
    if payload != interval_payload(interval):
        raise ValueError("Bound matched-interval inputs are inconsistent.")
    return interval


def interval_claims(interval: MatchedInterval) -> list[str]:
    lower, upper = interval.bounds
    span = (
        f"[{float(lower):.4g}, {float(upper):.4g}]"
        if upper is not None
        else f"[{float(lower):.4g}, no finite upper bound)"
    )
    return [
        f"With the number of discordant pairs random, for every probability that the case is "
        f"the exposed one, the exact confidence set contains it with probability at least "
        f"{interval.level}, averaged over that number.",
        f"For the observed pairs ({interval.observed.describe()}), whenever the set contains "
        f"it, the conditional odds ratio lies within {span}, for probabilities below 1.",
    ]


def interval_assumptions(interval: MatchedInterval) -> tuple[str, ...]:
    return (PAIRS_SAMPLED, WITHIN_PAIRS, SOURCE_POPULATION, INTERVAL_LEVEL, PAIRS_MATCH)


def render_interval_proof(interval: MatchedInterval, input_sha256: str) -> str:
    binomial = interval.binomial
    d, x = interval.observed.discordant, interval.observed.case_exposed
    an, ad = binomial.tail_level.as_integer_ratio()
    ln, ld = interval.level.as_integer_ratio()
    (lower_n, lower_d), (upper_n, upper_d) = (
        binomial.lower.as_integer_ratio(),
        binomial.upper.as_integer_ratio(),
    )
    tail = f"((({an} : ℕ) : ℝ) / (({ad} : ℕ) : ℝ))"
    lower_check = "(Or.inl rfl)" if lower_n == 0 else "(Or.inr (by decide +kernel))"
    upper_check = "(Or.inl rfl)" if upper_n == upper_d else "(Or.inr (by decide +kernel))"
    claimed = S.odds_interval(C, d, x, tail, (lower_n, lower_d), (upper_n, upper_d), "")
    body = "  exact bound.1" if upper_n == upper_d else "  exact ⟨bound.1, bound.2 (by decide)⟩"
    header = _header(input_sha256, "Coverage is a general theorem; the endpoints are checked.")
    return f"""{header}
def pairs : ℕ := {interval.observed.pairs}

{S.pairs_coverage(C, (ln, ld), "pairs", tail).header()} := by
  have covered := Matched.pairs_coverage pairs {tail} (by positivity) δ π
  exact le_trans (by norm_num) covered

{claimed.header()} := by
  have bound := Matched.odds_contains {d} {x} {an} {ad} (by decide)
    {lower_n} {lower_d} (by decide) (by decide) {upper_n} {upper_d} (by decide) (by decide)
    {lower_check} {upper_check} π member below
{body}

end StatClaimCertificate
{_audit(INTERVAL_THEOREMS, input_sha256)}"""
