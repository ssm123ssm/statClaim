"""Power formulas for cited tests of observational studies.

A formula sees plain numbers: the planning point, the number of participants n, the
number of covariates and alpha. Each test is two-sided, and like R's power functions a
formula ignores rejections in the direction away from the planning point. Each returns a
PowerResult; its critical value is on the scale of the estimate.
"""

import math

from statclaim.methods.core import Assumption, PowerFormula, PowerResult
from statclaim.methods.t_distribution import random_design_power, t_quantile

NORMAL_EXPOSURE_POWER = Assumption(
    "normal_exposure_power",
    "approximation",
    "Power is for an exposure that is normal, given the covariates, with the planning "
    "standard deviation: given the exposure the test statistic is noncentral t, and power "
    "averages over the exposure's spread. Exact for that model; otherwise an approximation, "
    "not a bound.",
)
PLANNING_ASSOCIATION = Assumption(
    "planning_association",
    "scope",
    "The correlation, or the slope with its standard deviations, is a planning input, not an "
    "established fact.",
)
COVARIATES_EXPLAIN_EXPOSURE = Assumption(
    "covariates_explain_exposure",
    "scope",
    "exposure_r2, the share of the exposure's variance the covariates explain, is a planning "
    "input; with it left out, the covariates are taken to be unrelated to the exposure.",
)

SAMPSON = (
    "Sampson, A. R. (1974). A tale of two regressions. Journal of the American Statistical "
    "Association 69(347), 682-689. [to verify]"
)
GATSONIS_SAMPSON = (
    "Gatsonis, C. and Sampson, A. R. (1989). Multiple correlation: exact power and sample "
    "size calculations. Psychological Bulletin 106(3), 516-524. [to verify]"
)
COHEN = (
    "Cohen, J. (1988). Statistical Power Analysis for the Behavioral Sciences, 2nd ed. "
    "Lawrence Erlbaum. Chapters 3 and 9."
)

EXACT_UNDER_NORMALITY = "noncentral t averaged over a normal exposure, not a bound"


def correlation_power(point, n, covariates, alpha) -> PowerResult:
    """The t-test of Pearson's correlation under bivariate normality, with n - 2 degrees of
    freedom. Given the exposure, t is noncentral t with noncentrality
    rho / sqrt(1 - rho^2) times the root of the exposure's sum of squares in its own
    standard deviations, which is chi-square with n - 1 degrees of freedom."""
    rho = point["value"]
    df = n - 2
    critical = t_quantile(1 - alpha / 2, df)
    effect = abs(rho) / math.sqrt(1 - rho * rho)
    power = random_design_power(critical, df, effect, n - 1)
    # The test rejects when |r| passes r_c = t_c / sqrt(t_c^2 + df).
    se = 1 / math.sqrt(critical * critical + df)
    sign = 1 if rho >= 0 else -1
    return PowerResult(power, sign * critical * se, "above" if sign > 0 else "below", se)


def slope_power(point, n, covariates, alpha) -> PowerResult:
    """The t-test of the exposure's slope in a linear regression with k covariates, with
    n - k - 2 degrees of freedom. Given the exposure and covariates, t is noncentral t with
    noncentrality slope * sd(x | z) / residual_sd times the root of the exposure's residual
    sum of squares in units of sd(x | z), which is chi-square with n - k - 1 degrees of
    freedom when the exposure is normal given the covariates."""
    k = covariates
    df = n - k - 2
    spread = point["exposure_sd"] * math.sqrt(1 - point.get("exposure_r2", 0.0))
    critical = t_quantile(1 - alpha / 2, df)
    effect = abs(point["value"]) * spread / point["residual_sd"]
    power = random_design_power(critical, df, effect, n - k - 1)
    se = point["residual_sd"] / (spread * math.sqrt(n - k - 1))
    sign = 1 if point["value"] >= 0 else -1
    return PowerResult(power, sign * critical * se, "above" if sign > 0 else "below", se)


CORRELATION = PowerFormula(
    key="pearson_random_normal",
    title="t-test of a correlation, exact under bivariate normality",
    version=1,
    point="correlation",
    function=correlation_power,
    assumptions=(NORMAL_EXPOSURE_POWER, PLANNING_ASSOCIATION),
    references=(SAMPSON, GATSONIS_SAMPSON, COHEN),
    approximation=EXACT_UNDER_NORMALITY,
)
SLOPE = PowerFormula(
    key="slope_random_normal",
    title="t-test of a regression slope, exact for a normal exposure given the covariates",
    version=1,
    point="slope",
    function=slope_power,
    assumptions=(NORMAL_EXPOSURE_POWER, PLANNING_ASSOCIATION, COVARIATES_EXPLAIN_EXPOSURE),
    references=(SAMPSON, GATSONIS_SAMPSON, COHEN),
    approximation=EXACT_UNDER_NORMALITY,
)
