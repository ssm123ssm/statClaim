"""Nonrandomized, probability-ordered, two-sided Fisher exact test.

All probability comparisons and the rejection decision use exact integers and
fractions. See docs/exact-test-spec.md for the sampling model and proof scope.
"""

from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb

ALPHA = Fraction(1, 20)
TEST_ID = "fisher_exact_two_sided_probability_ordered"
TEST_VERSION = "0.2.0"


def validate_alpha(alpha: Fraction) -> None:
    if not isinstance(alpha, Fraction) or not 0 <= alpha <= 1:
        raise ValueError("alpha must be an exact Fraction between zero and one.")


def parse_alpha(value: str) -> Fraction:
    if not isinstance(value, str):
        raise ValueError('alpha must be an exact string, for example "1/20" or "0.05".')
    try:
        alpha = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError("Invalid exact alpha.") from error
    validate_alpha(alpha)
    return alpha


def fraction_record(value: Fraction) -> dict:
    """Preserve the exact value and provide a display-only decimal approximation."""
    with localcontext() as context:
        context.prec = 18
        decimal = str(Decimal(value.numerator) / Decimal(value.denominator))
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "fraction": str(value),
        "decimal_approximation": decimal,
    }


@dataclass(frozen=True)
class FisherResult:
    n_control: int
    n_treatment: int
    control_successes: int
    treatment_successes: int
    p_value: Fraction
    observed_table_probability: Fraction
    support_min: int
    support_max: int

    alpha: Fraction = ALPHA

    @property
    def reject_null(self) -> bool:
        """Decision of the fixed-sample rule at the declared exact threshold."""
        return self.p_value <= self.alpha

    def to_dict(self) -> dict:
        return {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "alternative": "two_sided",
            "table": {
                "columns": ["success", "failure"],
                "control": [self.control_successes, self.n_control - self.control_successes],
                "treatment": [
                    self.treatment_successes,
                    self.n_treatment - self.treatment_successes,
                ],
            },
            "conditioned_on": {
                "total_successes": self.control_successes + self.treatment_successes
            },
            "control_success_support": {"min": self.support_min, "max": self.support_max},
            "p_value": fraction_record(self.p_value),
            "observed_table_probability": fraction_record(self.observed_table_probability),
            "alpha": fraction_record(self.alpha),
            "p_value_le_alpha": self.reject_null,
        }


def fisher_exact(
    *,
    n_control: int,
    n_treatment: int,
    control_successes: int,
    treatment_successes: int,
    alpha: Fraction = ALPHA,
) -> FisherResult:
    """Compute the exact test for positive arm sizes and integer success counts.

    Conditions on both arm sizes and the pooled success count. Ties in table
    probability are included exactly, without a floating-point tolerance.
    This function computes a statistic; it does not check sampling assumptions
    or invoke Lean.
    """
    validate_alpha(alpha)
    for name, value in (("n_control", n_control), ("n_treatment", n_treatment)):
        if type(value) is not int or value <= 0:
            raise ValueError(f"{name} must be a positive integer.")
    for name, value, size in (
        ("control_successes", control_successes, n_control),
        ("treatment_successes", treatment_successes, n_treatment),
    ):
        if type(value) is not int or not 0 <= value <= size:
            raise ValueError(f"{name} must be an integer between 0 and {size}.")

    total_successes = control_successes + treatment_successes
    lower = max(0, total_successes - n_treatment)
    upper = min(n_control, total_successes)
    denominator = comb(n_control + n_treatment, total_successes)
    observed_weight = comb(n_control, control_successes) * comb(n_treatment, treatment_successes)
    weight = comb(n_control, lower) * comb(n_treatment, total_successes - lower)
    extreme_weight = 0
    for successes in range(lower, upper + 1):
        if weight <= observed_weight:
            extreme_weight += weight
        if successes < upper:
            # Exact ratio of neighboring binomial-coefficient products. The
            # denominator is positive within the interior of the support.
            weight = (
                weight
                * (n_control - successes)
                * (total_successes - successes)
                // ((successes + 1) * (n_treatment - total_successes + successes + 1))
            )
    return FisherResult(
        n_control=n_control,
        n_treatment=n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
        p_value=Fraction(extreme_weight, denominator),
        observed_table_probability=Fraction(observed_weight, denominator),
        support_min=lower,
        support_max=upper,
        alpha=alpha,
    )
