"""Prevalence, cumulative incidence and incidence rates in observational studies.

Prevalence and cumulative incidence are single proportions: the exact interval of
StatClaim.Modules.BinomialInterval, with coverage proved for every true proportion. A
cross-sectional study measures prevalence; a cohort measures cumulative incidence, the
risk over its follow-up.

Incidence rates need person-time. In a person-time cohort events occur at a constant rate
in each group, so the total number of events is Poisson and, given it, the exposed share
is binomial (StatClaim.Modules.Incidence). Equal rates make that share the exposed share
of person-time: the exact test of that share, given the total, has level alpha for every
total, so on average too. The rate ratio is the odds of the share times the ratio of
unexposed to exposed person-time, so the exact interval for the share gives one for it.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import comb

from statclaim.association import NAME
from statclaim.fisher import fraction_record, validate_alpha
from statclaim.planning import MAX_ONE_ARM, BinomialInterval
from statclaim.randomisation import PRESPECIFIED

RATE_KIND = "statclaim_rate_test_certificate"
TEST_ID = "conditional_rate_test"
TEST_VERSION = "0.1.0"
NULL_STATEMENT = "rate_exposed = rate_unexposed"
# Events in an observed table: binomial tails at the person-time share are checked term by
# term, with that share's numerator and denominator as large as the person-time needs.
MAX_EVENTS = 500
MAX_TIME_DIGITS = 12
PROPORTIONS = {
    "prevalence": ("prevalence", ("cross_sectional",)),
    "cumulative_incidence": ("cumulative incidence", ("cohort",)),
}

# Bound into certificates; methods/identify.py recognises each one.
RANDOM_SAMPLE = (
    "Participants were sampled independently from one population, in the declared number."
)
COMMON_RISK = (
    "Participants' outcomes are independent of one another, with one common probability of "
    "the outcome."
)
COUNT_LEVEL = "The confidence level was chosen before the data were seen."
COUNT_MATCHES = "The supplied count describes the declared study."
POISSON_EVENTS = (
    "In each group events occur independently at one constant rate over its person-time, so "
    "the counts are Poisson: the total is Poisson and, given it, the exposed share is binomial."
)
PERSON_TIME = (
    "Person-time is measured without error and does not depend on the events, and follow-up "
    "ends without regard to them."
)
RATE_NULL = (
    "The error bound is under the null of no association: the same incidence rate with and "
    "without exposure, for every common rate."
)
EVENTS_MATCH = "The supplied events and person-time describe the declared study."
RATE_THEOREM = "StatClaim.Modules.Incidence.typeI"


def _name(value: str) -> None:
    if not isinstance(value, str) or not NAME.fullmatch(value):
        raise ValueError("Exposure and outcome names are short plain words.")


def proportion_not_estimable(measure: str, design: str) -> str | None:
    words, designs = PROPORTIONS[measure]
    if design in designs:
        return None
    if design in ("case_control", "matched_case_control"):
        return (
            f"A case-control study fixed how many have the outcome, so it cannot estimate the "
            f"{words} or any risk; only odds ratios."
        )
    if design == "person_time_cohort":
        return (
            f"A person-time cohort measures incidence rates, not the {words}. Use rate_ratio "
            "with observed_events."
        )
    if measure == "prevalence":
        return (
            "A cohort measures risk over follow-up, not prevalence at one time. Use "
            "cumulative_incidence."
        )
    return "A cross-sectional study measures prevalence, not risk over follow-up. Use prevalence."


# Prevalence and cumulative incidence -------------------------------------------------------
@dataclass(frozen=True)
class ProportionEstimate:
    """Prevalence or cumulative incidence with its exact interval."""

    measure: str
    design: str
    n: int
    cases: int
    level: Fraction
    exposure: str = "exposure"
    outcome: str = "outcome"
    group: str | None = None

    def __post_init__(self):
        if self.measure not in PROPORTIONS:
            raise ValueError(f"Unknown proportion {self.measure!r}.")
        reason = proportion_not_estimable(self.measure, self.design)
        if reason:
            raise ValueError(reason)
        if self.group not in (None, "exposed", "unexposed"):
            raise ValueError('group is "exposed" or "unexposed".')
        _name(self.exposure)
        _name(self.outcome)
        _ = self.binomial  # constructing the interval validates the counts and level

    @property
    def binomial(self) -> BinomialInterval:
        return BinomialInterval(self.n, self.cases, self.level)

    def who(self) -> str:
        if self.group is None:
            return f"{self.n} participants"
        return f"the {self.n} {self.group}" + (
            f" to {self.exposure}" if self.group == "exposed" else ""
        )

    def evaluate(self) -> dict:
        interval = self.binomial
        return {
            "measure": self.measure,
            "n": self.n,
            "cases": self.cases,
            "level": fraction_record(self.level),
            "arm_level": fraction_record(self.level),
            "estimate": fraction_record(Fraction(self.cases, self.n)),
            "lower": fraction_record(interval.lower),
            "upper": fraction_record(interval.upper),
            "method": "exact_binomial_interval",
        }


def proportion_assumptions(estimate: ProportionEstimate) -> tuple[str, ...]:
    return (RANDOM_SAMPLE, COMMON_RISK, COUNT_LEVEL, COUNT_MATCHES)


# Incidence rates ---------------------------------------------------------------------------
@dataclass(frozen=True)
class RateTest:
    """The conditional exact test of equal incidence rates in a person-time cohort."""

    alpha: Fraction
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        validate_alpha(self.alpha)
        _name(self.exposure)
        _name(self.outcome)


def _time(value: Fraction) -> None:
    if not isinstance(value, Fraction) or value <= 0:
        raise ValueError("Person-time must be a positive exact number.")
    if max(len(str(value.numerator)), len(str(value.denominator))) > MAX_TIME_DIGITS:
        raise ValueError(f"Person-time may have at most {MAX_TIME_DIGITS} digits.")


@dataclass(frozen=True)
class ObservedEvents:
    """Events and person-time in the exposed and unexposed groups of a cohort."""

    exposed_events: int
    exposed_time: Fraction
    unexposed_events: int
    unexposed_time: Fraction
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        for count in (self.exposed_events, self.unexposed_events):
            if type(count) is not int or count < 0:
                raise ValueError("Events are whole numbers, zero or more.")
        _time(self.exposed_time)
        _time(self.unexposed_time)
        if self.total > MAX_EVENTS:
            raise ValueError(f"At most {MAX_EVENTS} events in all are supported.")
        _name(self.exposure)
        _name(self.outcome)

    @property
    def total(self) -> int:
        return self.exposed_events + self.unexposed_events

    @property
    def share(self) -> Fraction:
        """The exposed share of person-time: the exposed share of events under the null."""
        return self.exposed_time / (self.exposed_time + self.unexposed_time)

    def named(self) -> dict:
        return {
            "exposed_events": self.exposed_events,
            "exposed_time": str(self.exposed_time),
            "unexposed_events": self.unexposed_events,
            "unexposed_time": str(self.unexposed_time),
        }

    def describe(self) -> str:
        return (
            f"{self.exposed_events} events in {show(self.exposed_time)} exposed and "
            f"{self.unexposed_events} in {show(self.unexposed_time)} unexposed person-time units"
        )


def show(value: Fraction) -> str:
    """An exact number in decimals when it has a short decimal form, else as a fraction."""
    for places in range(7):
        scaled = value * 10**places
        if scaled.denominator == 1:
            return f"{float(value):.{places}f}" if places else str(scaled.numerator)
    return str(value)


def tails_at(total: int, exposed: int, share: Fraction) -> tuple[int, int, int]:
    """Numerators of the upper and lower binomial tails at the share, and their common
    denominator, the share's denominator to the power of the total."""
    a, d = share.as_integer_ratio()
    weights = [comb(total, k) * a**k * (d - a) ** (total - k) for k in range(total + 1)]
    return sum(weights[exposed:]), sum(weights[: exposed + 1]), d**total


@dataclass(frozen=True)
class RateResult:
    """The conditional exact test applied to observed events: p-value and decision."""

    test: RateTest
    events: ObservedEvents

    def __post_init__(self):
        if (self.test.exposure, self.test.outcome) != (self.events.exposure, self.events.outcome):
            raise ValueError("The events belong to another study than the test.")

    @property
    def doubled_tail(self) -> Fraction:
        upper, lower, denominator = tails_at(
            self.events.total, self.events.exposed_events, self.events.share
        )
        return Fraction(2 * min(upper, lower), denominator)

    @property
    def p_value(self) -> Fraction:
        return min(Fraction(1), self.doubled_tail)

    @property
    def reject_null(self) -> bool:
        return self.doubled_tail <= self.test.alpha

    def evaluate(self) -> dict:
        return {
            **self.events.named(),
            "events": self.events.total,
            "p_value": fraction_record(self.p_value),
            "alpha": fraction_record(self.test.alpha),
            "reject_null": self.reject_null,
            "test": TEST_ID,
        }


def _odds(value: Fraction) -> Fraction:
    return value / (1 - value)


@dataclass(frozen=True)
class RateRatioInterval:
    """An interval for the incidence rate ratio from the exact interval for the exposed share
    of events, given their total."""

    events: ObservedEvents
    level: Fraction

    def __post_init__(self):
        if not isinstance(self.level, Fraction) or not 0 < self.level < 1:
            raise ValueError("The confidence level must lie strictly between 0 and 1.")
        if self.events.total == 0:
            raise ValueError("No events were observed, so there is no information on the rates.")
        if self.events.total > MAX_ONE_ARM:
            raise ValueError(f"At most {MAX_ONE_ARM} events are supported.")

    @property
    def binomial(self) -> BinomialInterval:
        return BinomialInterval(self.events.total, self.events.exposed_events, self.level)

    @property
    def scale(self) -> Fraction:
        """Unexposed over exposed person-time: the rate ratio is the share's odds times this."""
        return self.events.unexposed_time / self.events.exposed_time

    @property
    def bounds(self) -> tuple[Fraction, Fraction | None]:
        interval = self.binomial
        upper = _odds(interval.upper) * self.scale if interval.upper < 1 else None
        return _odds(interval.lower) * self.scale, upper

    @property
    def estimate(self) -> Fraction | None:
        events = self.events
        if events.unexposed_events == 0:
            return None
        return (Fraction(events.exposed_events) / events.exposed_time) / (
            Fraction(events.unexposed_events) / events.unexposed_time
        )

    def evaluate(self) -> dict:
        lower, upper = self.bounds
        estimate = self.estimate
        return {
            "measure": "rate_ratio",
            **self.events.named(),
            "level": fraction_record(self.level),
            "arm_level": fraction_record(self.level),
            "estimate": fraction_record(estimate) if estimate is not None else None,
            "lower": fraction_record(lower),
            "upper": fraction_record(upper) if upper is not None else None,
            "method": "exact_interval_exposed_share",
        }


def rate_assumptions(test: RateTest | None = None) -> tuple[str, ...]:
    return (POISSON_EVENTS, PERSON_TIME, PRESPECIFIED, RATE_NULL)


def rate_null_words(test: RateTest) -> str:
    return f"the incidence rate of {test.outcome} is the same with and without {test.exposure}"


def rate_result_assumptions(result: RateResult) -> tuple[str, ...]:
    return (*rate_assumptions(result.test), EVENTS_MATCH)


def rate_ratio_assumptions(interval: RateRatioInterval) -> tuple[str, ...]:
    return (POISSON_EVENTS, PERSON_TIME, COUNT_LEVEL, EVENTS_MATCH)
