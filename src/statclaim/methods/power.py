"""Approximate power formulas for cited tests. Each is a normal approximation.

A formula sees plain numbers: the planning point, the arm sizes, the null's value,
alpha and whether the test is one-sided. A one-sided test uses alpha. A two-sided
test uses alpha/2 and ignores rejections in the direction away from the planning
point, as R's power.t.test and power.prop.test do by default.
"""

import math
from statistics import NormalDist

from statclaim.methods.assumptions import (
    AT_RISK_SHARES,
    NORMAL_APPROXIMATION_POWER,
    PLANNING_EVENTS,
    PLANNING_SD,
    PROPORTIONAL_HAZARDS,
    UNADJUSTED_PROPORTIONS,
)
from statclaim.methods.core import PowerFormula, PowerResult

_NORMAL = NormalDist()

CHOW = (
    "Chow, S.-C., Shao, J. and Wang, H. (2008). Sample Size Calculations in Clinical "
    "Research, 2nd ed. Chapman and Hall/CRC. Chapter 3."
)
JULIOUS = (
    "Julious, S. A. (2004). Sample sizes for clinical trials with normal data. Statistics in "
    "Medicine 23(12), 1921-1986."
)
FLEISS = (
    "Fleiss, J. L., Levin, B. and Paik, M. C. (2003). Statistical Methods for Rates and "
    "Proportions, 3rd ed. Wiley. Chapter 4."
)
R_POWER_PROP = "R Core Team. power.prop.test, in the stats package of R."
SCHOENFELD_1981 = (
    "Schoenfeld, D. (1981). The asymptotic properties of nonparametric tests for comparing "
    "survival distributions. Biometrika 68(1), 316-319."
)
SCHOENFELD_1983 = (
    "Schoenfeld, D. A. (1983). Sample-size formula for the proportional-hazards regression "
    "model. Biometrics 39(2), 499-503."
)


def _quantile(alpha: float, one_sided: bool) -> float:
    return _NORMAL.inv_cdf(1 - (alpha if one_sided else alpha / 2))


def _side(shift: float) -> str:
    return "above" if shift >= 0 else "below"


def two_means(point, n_control, n_treatment, null_value, alpha, one_sided) -> PowerResult:
    """A difference of two means with the standard deviation treated as known."""
    se = point["sd"] * math.sqrt(1 / n_control + 1 / n_treatment)
    z = _quantile(alpha, one_sided)
    if one_sided:
        # Null: difference <= null_value. Reject when the estimate is above the margin + z SE.
        shift = point["value"] - null_value
        return PowerResult(_NORMAL.cdf(shift / se - z), null_value + z * se, "above", se)
    shift = point["value"]
    sign = 1 if shift >= 0 else -1
    return PowerResult(_NORMAL.cdf(abs(shift) / se - z), sign * z * se, _side(shift), se)


def two_proportions(point, n_control, n_treatment, null_value, alpha, one_sided) -> PowerResult:
    """A difference of two proportions: pooled variance under the null, unpooled at the point.

    With equal arms this is R's power.prop.test without a continuity correction.
    """
    if null_value != 0:
        raise ValueError("The two-proportion formula supports a zero difference only.")
    p_c, p_t = point["p_control"], point["p_treatment"]
    pooled = (n_control * p_c + n_treatment * p_t) / (n_control + n_treatment)
    se_null = math.sqrt(pooled * (1 - pooled) * (1 / n_control + 1 / n_treatment))
    se_point = math.sqrt(p_c * (1 - p_c) / n_control + p_t * (1 - p_t) / n_treatment)
    z = _quantile(alpha, one_sided)
    shift = p_t - p_c
    gap = (shift if one_sided else abs(shift)) - z * se_null
    if se_point == 0:
        # Both rates are 0 or 1: the estimate equals the true difference.
        power = 1.0 if gap > 0 else 0.0
    else:
        power = _NORMAL.cdf(gap / se_point)
    sign = 1 if one_sided or shift >= 0 else -1
    return PowerResult(power, sign * z * se_null, "above" if sign > 0 else "below", se_null)


def log_rank_events(point, n_control, n_treatment, null_value, alpha, one_sided) -> PowerResult:
    """Schoenfeld's formula: power from the number of events and the hazard ratio."""
    if one_sided or null_value != 0:
        raise ValueError("The log-rank power formula is for the two-sided test of equal survival.")
    share = n_control / (n_control + n_treatment)
    se = 1 / math.sqrt(point["events"] * share * (1 - share))
    z = _quantile(alpha, one_sided)
    log_ratio = math.log(point["value"])
    sign = 1 if log_ratio >= 0 else -1
    return PowerResult(
        _NORMAL.cdf(abs(log_ratio) / se - z), math.exp(sign * z * se), _side(log_ratio), se
    )


TWO_MEANS = PowerFormula(
    key="normal_two_means",
    title="Difference of two means, normal approximation with a known standard deviation",
    version=1,
    point="mean_difference",
    function=two_means,
    assumptions=(NORMAL_APPROXIMATION_POWER, PLANNING_SD),
    references=(CHOW, JULIOUS),
)
TWO_PROPORTIONS = PowerFormula(
    key="normal_two_proportions",
    title="Difference of two proportions, normal approximation",
    version=1,
    point="binomial_rates",
    function=two_proportions,
    assumptions=(NORMAL_APPROXIMATION_POWER, UNADJUSTED_PROPORTIONS),
    references=(FLEISS, R_POWER_PROP),
)
SCHOENFELD = PowerFormula(
    key="schoenfeld_log_rank",
    title="Log-rank test, Schoenfeld's formula in the number of events",
    version=1,
    point="hazard_ratio",
    function=log_rank_events,
    assumptions=(NORMAL_APPROXIMATION_POWER, PROPORTIONAL_HAZARDS, PLANNING_EVENTS, AT_RISK_SHARES),
    references=(SCHOENFELD_1981, SCHOENFELD_1983),
)
