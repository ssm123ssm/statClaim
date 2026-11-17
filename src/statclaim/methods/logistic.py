"""Logistic regression for a yes-or-no outcome. Guarantees are cited, not proved."""

from fractions import Fraction

from statclaim.methods.assumptions import (
    ENOUGH_EVENTS,
    FIXED_SIZES,
    INDEPENDENT_PARTICIPANTS,
    LOGIT_LINEAR,
    NULL_IS_ZERO_COEFFICIENT,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import CitedMethod, MethodModule
from statclaim.methods.power import TWO_PROPORTIONS

COX = (
    "Cox, D. R. (1958). The regression analysis of binary sequences. Journal of the Royal "
    "Statistical Society B 20(2), 215-242."
)
HOSMER = (
    "Hosmer, D. W., Lemeshow, S. and Sturdivant, R. X. (2013). Applied Logistic Regression, "
    "3rd ed. Wiley."
)

_COMMON = dict(
    module="tests.logistic",
    version=1,
    outcome="binary",
    scope="asymptotic",
    limit="the numbers of responders and non-responders grow",
    assumptions=(
        INDEPENDENT_PARTICIPANTS,
        FIXED_SIZES,
        SINGLE_ANALYSIS,
        LOGIT_LINEAR,
        NULL_IS_ZERO_COEFFICIENT,
        ENOUGH_EVENTS,
    ),
    references=(COX, HOSMER),
    min_per_arm=2,
    min_total=4,
    power=TWO_PROPORTIONS,
)

MODULE = MethodModule(
    "tests.logistic",
    "A Wald or likelihood-ratio test of the treatment coefficient in a logistic regression "
    "with covariates. The compiler checks the null and the sampling plan. The Type I "
    "guarantee is cited and is a large-sample approximation. The one-sided test supports a "
    "zero difference only: a margin on the proportion scale is not a statement about the "
    "coefficient.",
    (
        CitedMethod(
            key="logistic_regression",
            title="Two-sided test of the treatment coefficient in a logistic regression",
            null="equal_proportions",
            relation="equals",
            **_COMMON,
        ),
        CitedMethod(
            key="logistic_regression_one_sided",
            title="One-sided test of the treatment coefficient in a logistic regression",
            null="proportion_difference_at_most",
            relation="at_most",
            null_value=Fraction(0),
            **_COMMON,
        ),
    ),
)
