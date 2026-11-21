"""Power formulas for cited tests of observational studies.

A formula sees plain numbers: the planning point, a size, the number of covariates and
alpha. The size is the participants for a regression or a correlation, the pairs for a
matched study and the events for a person-time cohort. Each test is two-sided, and like
R's power functions a formula ignores rejections in the direction away from the planning
point. Each returns a PowerResult; its critical value is on the scale of the estimate.
"""

import math
from statistics import NormalDist

from statclaim.methods.core import Assumption, PowerFormula, PowerResult
from statclaim.methods.t_distribution import random_design_power, t_quantile

_NORMAL = NormalDist()

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
NORMAL = "normal approximation, not a bound"

WALD_POWER = Assumption(
    "wald_power",
    "approximation",
    "Power is for the Wald test of the exposure's coefficient, from a normal approximation with "
    "its variance under the null for the critical value and under the alternative for the "
    "spread. It is an approximation, not a bound.",
)
COVARIATES_UNRELATED = Assumption(
    "covariates_unrelated",
    "approximation",
    "Covariates are taken to be unrelated to the exposure. Covariates that explain part of the "
    "exposure need more participants: about 1 / (1 - R^2) times as many.",
)
CASE_CONTROL_ROLES = Assumption(
    "case_control_roles",
    "approximation",
    "For a case-control study, the odds ratio is the same with exposure as the outcome, so "
    "power uses the cases' share and each group's probability of exposure.",
)
HSIEH = (
    "Hsieh, F. Y., Bloch, D. A. and Larsen, M. D. (1998). A simple method of sample size "
    "calculation for linear and logistic regression. Statistics in Medicine 17(14), "
    "1623-1634."
)
SIGNORINI = (
    "Signorini, D. F. (1991). Sample size for Poisson regression. Biometrika 78(2), 446-450."
)
CONNOR = (
    "Connor, R. J. (1987). Sample size for testing differences in proportions for the "
    "paired-sample design. Biometrics 43(1), 207-211."
)
R_PWRSS = "Bulus, M. pwrss: power.z.logistic and power.z.poisreg, an R package."
DESIGN_EFFECT_POWER = Assumption(
    "design_effect_power",
    "approximation",
    "Power is that of a simple random sample of n / deff participants, where deff, the "
    "survey's design effect for the exposure's coefficient, is a planning input. A "
    "design-based test with few clusters, or weights that vary a lot, has less power than this.",
)
KISH = "Kish, L. (1965). Survey Sampling. Wiley. Section 8.2."
LUMLEY_POWER = "Lumley, T. (2010). Complex Surveys: A Guide to Analysis Using R. Wiley."
R_MESS = "Ekstrom, C. T. MESS: power_mcnemar_test, an R package."


def _upper(alpha: float) -> float:
    return _NORMAL.inv_cdf(1 - alpha / 2)


def logistic_groups_power(point, n, covariates, alpha) -> PowerResult:
    """Hsieh's formula for logistic regression on a binary exposure: n participants, of whom
    a share B have the exposure, with outcome probabilities p_reference without it and
    p_other with it. The test of the log odds ratio has power
    Phi((|p_other - p_reference| sqrt(n (1 - B)) - z sqrt(p (1 - p) / B)) /
    sqrt(p_reference (1 - p_reference) + p_other (1 - p_other) (1 - B) / B)), with
    p = (1 - B) p_reference + B p_other."""
    p0, p1, share = point["p_reference"], point["p_other"], point["share_other"]
    pooled = (1 - share) * p0 + share * p1
    z = _upper(alpha)
    scale = math.sqrt(n * (1 - share))
    null_sd = math.sqrt(pooled * (1 - pooled) / share)
    spread = math.sqrt(p0 * (1 - p0) + p1 * (1 - p1) * (1 - share) / share)
    gap = p1 - p0
    power = _NORMAL.cdf((abs(gap) * scale - z * null_sd) / spread)
    sign = 1 if gap >= 0 else -1
    return PowerResult(
        power, sign * z * null_sd / scale, "above" if sign > 0 else "below", null_sd / scale
    )


def logistic_trend_power(point, n, covariates, alpha) -> PowerResult:
    """Hsieh's formula for logistic regression on a normal exposure: the odds ratio per
    standard deviation of the exposure, and the outcome's probability p at the exposure's
    mean. Power is Phi(sqrt(n (1 - R^2) p (1 - p)) |log odds ratio| - z)."""
    p = point["baseline"]
    log_ratio = math.log(point["value"])
    se = 1 / math.sqrt(n * (1 - point.get("exposure_r2", 0.0)) * p * (1 - p))
    z = _upper(alpha)
    sign = 1 if log_ratio >= 0 else -1
    power = _NORMAL.cdf(abs(log_ratio) / se - z)
    return PowerResult(power, math.exp(sign * z * se), "above" if sign > 0 else "below", se)


def poisson_rates_power(point, events, covariates, alpha) -> PowerResult:
    """Signorini's formula for Poisson regression on a binary exposure, in the expected
    events. With a share s of the person-time exposed and rate ratio r, the events expected
    were nobody exposed are events / (1 - s + s r); the log rate ratio has variance
    (1 / (1 - s) + 1 / (s r)) over them, and 1 / (s (1 - s)) under the null."""
    share, ratio = point["exposed_share"], point["rate_ratio"]
    baseline = events / (1 - share + share * ratio)
    null_variance = 1 / (share * (1 - share))
    variance = 1 / (1 - share) + 1 / (share * ratio)
    z = _upper(alpha)
    log_ratio = math.log(ratio)
    power = _NORMAL.cdf(
        (abs(log_ratio) * math.sqrt(baseline) - z * math.sqrt(null_variance)) / math.sqrt(variance)
    )
    se = math.sqrt(null_variance / baseline)
    sign = 1 if log_ratio >= 0 else -1
    return PowerResult(power, math.exp(sign * z * se), "above" if sign > 0 else "below", se)


def matched_pairs_power(point, pairs, covariates, alpha) -> PowerResult:
    """Connor's normal approximation for 1:1 matched pairs, which a conditional logistic
    regression on a binary exposure and no covariates tests like McNemar's test. With the
    smaller discordant probability q and psi >= 1 the ratio of the larger to it, power is
    Phi((sqrt(n q) (psi - 1) - z sqrt(psi + 1)) / sqrt(psi + 1 - q (psi - 1)^2))."""
    ratio = point["odds_ratio"]
    psi = max(ratio, 1 / ratio)
    q = point["share"] / (1 + psi)
    z = _upper(alpha)
    power = _NORMAL.cdf(
        (math.sqrt(pairs * q) * (psi - 1) - z * math.sqrt(psi + 1))
        / math.sqrt(psi + 1 - q * (psi - 1) ** 2)
    )
    # The conditional odds ratio's estimate must pass this, given the expected discordant pairs.
    discordant = pairs * point["share"]
    se = 2 / math.sqrt(discordant)
    sign = 1 if ratio >= 1 else -1
    return PowerResult(power, math.exp(sign * z * se), "above" if sign > 0 else "below", se)


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
LOGISTIC_GROUPS = PowerFormula(
    key="hsieh_logistic_binary",
    title="Logistic regression on a binary exposure, Hsieh's formula",
    version=1,
    point="association_groups",
    function=logistic_groups_power,
    assumptions=(WALD_POWER, COVARIATES_UNRELATED, CASE_CONTROL_ROLES),
    references=(HSIEH, R_PWRSS),
    approximation=NORMAL,
)
LOGISTIC_TREND = PowerFormula(
    key="hsieh_logistic_normal",
    title="Logistic regression on a normal exposure, Hsieh's formula",
    version=1,
    point="odds_per_sd",
    function=logistic_trend_power,
    assumptions=(WALD_POWER, PLANNING_ASSOCIATION, COVARIATES_EXPLAIN_EXPOSURE),
    references=(HSIEH, R_PWRSS),
    approximation=NORMAL,
)
POISSON_RATES = PowerFormula(
    key="signorini_poisson_binary",
    title="Poisson regression of rates on a binary exposure, Signorini's formula",
    version=1,
    point="incidence_rates",
    function=poisson_rates_power,
    assumptions=(WALD_POWER, COVARIATES_UNRELATED),
    references=(SIGNORINI, R_PWRSS),
    approximation=NORMAL,
)
MATCHED_PAIRS = PowerFormula(
    key="connor_matched_pairs",
    title="Conditional logistic regression of 1:1 matched pairs, Connor's formula",
    version=1,
    point="discordant_pairs",
    function=matched_pairs_power,
    assumptions=(WALD_POWER, COVARIATES_UNRELATED),
    references=(CONNOR, R_MESS),
    approximation=NORMAL,
)


def survey_groups_power(point, n, covariates, alpha) -> PowerResult:
    """A 2x2 survey table, or a survey logistic regression on a binary exposure: Hsieh's
    formula for two groups at the effective sample size n / deff."""
    p0, p1, share = point["p_reference"], point["p_other"], point["share_other"]
    effective = n / point.get("design_effect", 1.0)
    pooled = (1 - share) * p0 + share * p1
    z = _upper(alpha)
    scale = math.sqrt(effective * (1 - share))
    null_sd = math.sqrt(pooled * (1 - pooled) / share)
    spread = math.sqrt(p0 * (1 - p0) + p1 * (1 - p1) * (1 - share) / share)
    gap = p1 - p0
    power = _NORMAL.cdf((abs(gap) * scale - z * null_sd) / spread)
    sign = 1 if gap >= 0 else -1
    direction = "above" if sign > 0 else "below"
    return PowerResult(power, sign * z * null_sd / scale, direction, null_sd / scale)


def survey_trend_power(point, n, covariates, alpha) -> PowerResult:
    """A survey logistic regression on a normal exposure: Hsieh's formula at n / deff."""
    p = point["baseline"]
    effective = n / point.get("design_effect", 1.0)
    log_ratio = math.log(point["value"])
    se = 1 / math.sqrt(effective * (1 - point.get("exposure_r2", 0.0)) * p * (1 - p))
    z = _upper(alpha)
    sign = 1 if log_ratio >= 0 else -1
    power = _NORMAL.cdf(abs(log_ratio) / se - z)
    return PowerResult(power, math.exp(sign * z * se), "above" if sign > 0 else "below", se)


def survey_slope_power(point, n, covariates, alpha) -> PowerResult:
    """A survey linear regression on a measured exposure: the design-based Wald test of the
    slope, normal, with the slope's variance residual_sd^2 deff / (n sd(x | z)^2)."""
    effective = n / point.get("design_effect", 1.0)
    spread = point["exposure_sd"] * math.sqrt(1 - point.get("exposure_r2", 0.0))
    se = point["residual_sd"] / (spread * math.sqrt(effective))
    z = _upper(alpha)
    sign = 1 if point["value"] >= 0 else -1
    power = _NORMAL.cdf(abs(point["value"]) / se - z)
    return PowerResult(power, sign * z * se, "above" if sign > 0 else "below", se)


SURVEY_GROUPS = PowerFormula(
    key="survey_two_groups",
    title="Survey test of a binary exposure, two proportions at the effective sample size",
    version=1,
    point="association_groups",
    function=survey_groups_power,
    assumptions=(WALD_POWER, DESIGN_EFFECT_POWER, COVARIATES_UNRELATED),
    references=(HSIEH, KISH, LUMLEY_POWER),
    approximation=NORMAL,
)
SURVEY_TREND = PowerFormula(
    key="survey_logistic_normal",
    title="Survey logistic regression on a normal exposure, Hsieh's formula at n / deff",
    version=1,
    point="odds_per_sd",
    function=survey_trend_power,
    assumptions=(
        WALD_POWER,
        DESIGN_EFFECT_POWER,
        PLANNING_ASSOCIATION,
        COVARIATES_EXPLAIN_EXPOSURE,
    ),
    references=(HSIEH, KISH, LUMLEY_POWER),
    approximation=NORMAL,
)
SURVEY_SLOPE = PowerFormula(
    key="survey_slope_normal",
    title="Survey linear regression on a measured exposure, Wald test at n / deff",
    version=1,
    point="slope",
    function=survey_slope_power,
    assumptions=(
        WALD_POWER,
        DESIGN_EFFECT_POWER,
        PLANNING_ASSOCIATION,
        COVARIATES_EXPLAIN_EXPOSURE,
    ),
    references=(KISH, LUMLEY_POWER),
    approximation=NORMAL,
)
