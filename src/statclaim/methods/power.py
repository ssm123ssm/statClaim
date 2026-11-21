"""Approximate power formulas for cited tests: normal approximations, and the noncentral t
for tests of cluster summaries, where clusters are few.

A formula sees plain numbers: the planning point, the arm sizes, the null's value,
alpha and the side. A one-sided test uses alpha, in the direction that favours the
treatment: "higher" or "lower". A two-sided test ("both") uses alpha/2 and ignores
rejections in the direction away from the planning point, as R's power.t.test and
power.prop.test do by default.
"""

import math
from statistics import NormalDist

from statclaim.methods.assumptions import (
    AT_RISK_SHARES,
    EQUAL_CLUSTER_SIZES,
    NONCENTRAL_T_POWER,
    NORMAL_APPROXIMATION_POWER,
    PLANNING_EVENTS,
    PLANNING_ICC,
    PLANNING_SD,
    PROPORTIONAL_HAZARDS,
    UNADJUSTED_PROPORTIONS,
)
from statclaim.methods.core import PowerFormula, PowerResult
from statclaim.methods.t_distribution import (
    BENTON_KRISHNAMOORTHY,
    LENTH,
    noncentral_t_sf,
    t_quantile,
)

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
DONNER_BIRKETT_BUCK = (
    "Donner, A., Birkett, N. and Buck, C. (1981). Randomization by cluster: sample size "
    "requirements and analysis. American Journal of Epidemiology 114(6), 906-914. [to verify]"
)
R_POWER_T = "R Core Team. power.t.test, in the stats package of R."


SIDES = ("higher", "lower", "both")


def _quantile(alpha: float, side: str) -> float:
    if side not in SIDES:
        raise ValueError(f"Unknown side {side!r}.")
    return _NORMAL.inv_cdf(1 - (alpha / 2 if side == "both" else alpha))


def _side(shift: float) -> str:
    return "above" if shift >= 0 else "below"


def two_means(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """A difference of two means with the standard deviation treated as known."""
    se = point["sd"] * math.sqrt(1 / n_control + 1 / n_treatment)
    z = _quantile(alpha, side)
    if side == "higher":
        # Null: difference <= null_value. Reject when the estimate is above the margin + z SE.
        shift = point["value"] - null_value
        return PowerResult(_NORMAL.cdf(shift / se - z), null_value + z * se, "above", se)
    if side == "lower":
        # Null: difference >= null_value. Reject when the estimate is below the margin - z SE.
        shift = null_value - point["value"]
        return PowerResult(_NORMAL.cdf(shift / se - z), null_value - z * se, "below", se)
    shift = point["value"]
    sign = 1 if shift >= 0 else -1
    return PowerResult(_NORMAL.cdf(abs(shift) / se - z), sign * z * se, _side(shift), se)


def two_proportions(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """A difference of two proportions: pooled variance under the null, unpooled at the point.

    With equal arms this is R's power.prop.test without a continuity correction.
    """
    if null_value != 0 or side == "lower":
        raise ValueError("The two-proportion formula supports a zero difference, higher or both.")
    p_c, p_t = point["p_control"], point["p_treatment"]
    pooled = (n_control * p_c + n_treatment * p_t) / (n_control + n_treatment)
    se_null = math.sqrt(pooled * (1 - pooled) * (1 / n_control + 1 / n_treatment))
    se_point = math.sqrt(p_c * (1 - p_c) / n_control + p_t * (1 - p_t) / n_treatment)
    z = _quantile(alpha, side)
    shift = p_t - p_c
    one_sided = side == "higher"
    gap = (shift if one_sided else abs(shift)) - z * se_null
    if se_point == 0:
        # Both rates are 0 or 1: the estimate equals the true difference.
        power = 1.0 if gap > 0 else 0.0
    else:
        power = _NORMAL.cdf(gap / se_point)
    sign = 1 if one_sided or shift >= 0 else -1
    return PowerResult(power, sign * z * se_null, "above" if sign > 0 else "below", se_null)


def log_rank_events(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """Schoenfeld's formula: power from the number of events and the hazard ratio."""
    if side != "both" or null_value != 0:
        raise ValueError("The log-rank power formula is for the two-sided test of equal survival.")
    share = n_control / (n_control + n_treatment)
    se = 1 / math.sqrt(point["events"] * share * (1 - share))
    z = _quantile(alpha, side)
    log_ratio = math.log(point["value"])
    sign = 1 if log_ratio >= 0 else -1
    return PowerResult(
        _NORMAL.cdf(abs(log_ratio) / se - z), math.exp(sign * z * se), _side(log_ratio), se
    )


def cluster_means(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """The t-test on cluster means. The sizes count clusters; a mean over m participants has
    variance sd^2 (1 + (m - 1) icc) / m. With equal clusters and arms, R's power.t.test with
    n clusters per arm and that standard deviation."""
    k_c, k_t = n_control, n_treatment
    variances = [
        point["sd"] ** 2 * (1 + (m - 1) * point["icc"]) / m
        for m in (point["size_control"], point["size_treatment"])
    ]
    se = math.sqrt(variances[0] / k_c + variances[1] / k_t)
    df = k_c + k_t - 2
    q = t_quantile(1 - (alpha / 2 if side == "both" else alpha), df)
    if side == "higher":
        shift = point["value"] - null_value
        return PowerResult(noncentral_t_sf(q, df, shift / se), null_value + q * se, "above", se)
    if side == "lower":
        shift = null_value - point["value"]
        return PowerResult(noncentral_t_sf(q, df, shift / se), null_value - q * se, "below", se)
    if side != "both":
        raise ValueError(f"Unknown side {side!r}.")
    shift = point["value"]
    sign = 1 if shift >= 0 else -1
    return PowerResult(noncentral_t_sf(q, df, abs(shift) / se), sign * q * se, _side(shift), se)


def cluster_proportions(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """The t-test on cluster proportions, two-sided. The sizes count clusters; a proportion
    over m participants has variance p (1 - p)(1 + (m - 1) icc) / m in its own arm. With equal
    clusters and arms, R's power.t.test with the root mean of the two variances."""
    if null_value != 0 or side != "both":
        raise ValueError("The cluster proportion formula is for the two-sided test of equality.")
    k_c, k_t = n_control, n_treatment
    p_c, p_t = point["p_control"], point["p_treatment"]
    variances = [
        p * (1 - p) * (1 + (m - 1) * point["icc"]) / m
        for p, m in ((p_c, point["size_control"]), (p_t, point["size_treatment"]))
    ]
    se = math.sqrt(variances[0] / k_c + variances[1] / k_t)
    df = k_c + k_t - 2
    q = t_quantile(1 - alpha / 2, df)
    shift = p_t - p_c
    sign = 1 if shift >= 0 else -1
    # Both rates 0 or 1: every cluster's proportion equals its arm's rate.
    power = noncentral_t_sf(q, df, abs(shift) / se) if se > 0 else 1.0
    return PowerResult(power, sign * q * se, _side(shift), se)


NONCENTRAL_T = "noncentral t at the planning values, not a bound"

TWO_MEANS = PowerFormula(
    key="normal_two_means",
    title="Difference of two means, normal approximation with a known standard deviation",
    version=2,  # takes the side of the test, so lower-is-better tests can be planned
    point="mean_difference",
    function=two_means,
    assumptions=(NORMAL_APPROXIMATION_POWER, PLANNING_SD),
    references=(CHOW, JULIOUS),
)
TWO_PROPORTIONS = PowerFormula(
    key="normal_two_proportions",
    title="Difference of two proportions, normal approximation",
    version=2,  # takes the side of the test, so lower-is-better tests can be planned
    point="binomial_rates",
    function=two_proportions,
    assumptions=(NORMAL_APPROXIMATION_POWER, UNADJUSTED_PROPORTIONS),
    references=(FLEISS, R_POWER_PROP),
)
SCHOENFELD = PowerFormula(
    key="schoenfeld_log_rank",
    title="Log-rank test, Schoenfeld's formula in the number of events",
    version=2,  # takes the side of the test, so lower-is-better tests can be planned
    point="hazard_ratio",
    function=log_rank_events,
    assumptions=(NORMAL_APPROXIMATION_POWER, PROPORTIONAL_HAZARDS, PLANNING_EVENTS, AT_RISK_SHARES),
    references=(SCHOENFELD_1981, SCHOENFELD_1983),
)
CLUSTER_MEANS = PowerFormula(
    key="cluster_t_means",
    title="t-test on cluster means, noncentral t with the design effect",
    version=1,
    point="mean_difference",
    function=cluster_means,
    assumptions=(NONCENTRAL_T_POWER, PLANNING_SD, PLANNING_ICC, EQUAL_CLUSTER_SIZES),
    references=(DONNER_BIRKETT_BUCK, R_POWER_T, LENTH, BENTON_KRISHNAMOORTHY),
    approximation=NONCENTRAL_T,
)
CLUSTER_PROPORTIONS = PowerFormula(
    key="cluster_t_proportions",
    title="t-test on cluster proportions, noncentral t with the design effect",
    version=1,
    point="binomial_rates",
    function=cluster_proportions,
    assumptions=(NONCENTRAL_T_POWER, PLANNING_ICC, EQUAL_CLUSTER_SIZES),
    references=(DONNER_BIRKETT_BUCK, R_POWER_T, LENTH, BENTON_KRISHNAMOORTHY),
    approximation=NONCENTRAL_T,
)
