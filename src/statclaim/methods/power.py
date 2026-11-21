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
    EXPONENTIAL_DROPOUT,
    EXPONENTIAL_TIMES,
    NONCENTRAL_T_POWER,
    NORMAL_APPROXIMATION_POWER,
    PLANNING_EVENTS,
    PLANNING_ICC,
    PLANNING_SD,
    PROPORTIONAL_HAZARDS,
    UNADJUSTED_PROPORTIONS,
    UNIFORM_ACCRUAL,
    WALD_ENUMERATION,
)
from statclaim.methods.core import PowerFormula, PowerResult
from statclaim.methods.t_distribution import (
    BENTON_KRISHNAMOORTHY,
    LENTH,
    noncentral_t_sf,
    t_quantile,
)

_NORMAL = NormalDist()

AGRESTI_2013 = "Agresti, A. (2013). Categorical Data Analysis, 3rd ed. Wiley. Sections 3.1 and 5.2."
HAUCK_DONNER = (
    "Hauck, W. W. and Donner, A. (1977). Wald's test as applied to hypotheses in logit "
    "analysis. Journal of the American Statistical Association 72(360), 851-853."
)
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
LACHIN_FOULKES = (
    "Lachin, J. M. and Foulkes, M. A. (1986). Evaluation of sample size and power for analyses "
    "of survival with allowance for nonuniform patient entry, losses to follow-up, "
    "noncompliance, and stratification. Biometrics 42(3), 507-519. [to verify]"
)
R_SURVIVAL_PACKAGES = (
    "Anderson, K. M. gsDesign (nSurv, eEvents), and Wassmer, G. and Pahlke, F. rpact "
    "(getSampleSizeSurvival), R packages for survival designs."
)


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


def _binomial_window(n: int, rate: float):
    """(k, P(K = k)) for K binomial(n, rate), within 12 standard deviations of the mean, where
    the rest is far below a double's precision."""
    if rate <= 0.0 or rate >= 1.0:
        yield (0 if rate <= 0.0 else n), 1.0
        return
    mean, spread = n * rate, math.sqrt(n * rate * (1 - rate))
    low, high = max(0, int(mean - 12 * spread) - 1), min(n, int(mean + 12 * spread) + 2)
    log_rate, log_rest = math.log(rate), math.log1p(-rate)
    base = math.lgamma(n + 1)
    for k in range(low, high + 1):
        weight = base - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * log_rate
        yield k, math.exp(weight + (n - k) * log_rest)


def wald_rejection(n_control, n_treatment, alpha, side, p_control, p_treatment) -> float:
    """The probability that the Wald test of the log odds ratio rejects, summed over both
    arms' binomial counts. A table with an empty cell does not reject."""
    z = _quantile(alpha, side)
    treated = list(_binomial_window(n_treatment, p_treatment))
    total = 0.0
    for x_c, w_c in _binomial_window(n_control, p_control):
        if x_c in (0, n_control):
            continue
        log_c = math.log(x_c / (n_control - x_c))
        var_c = 1 / x_c + 1 / (n_control - x_c)
        inner = 0.0
        for x_t, w_t in treated:
            if x_t in (0, n_treatment):
                continue
            ratio = math.log(x_t / (n_treatment - x_t)) - log_c
            wald = ratio / math.sqrt(var_c + 1 / x_t + 1 / (n_treatment - x_t))
            if wald > z if side == "higher" else abs(wald) > z:
                inner += w_t
        total += w_c * inner
    return min(total, 1.0)


def logistic_wald(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """The Wald test of the treatment coefficient in a logistic regression with treatment
    alone: the log odds ratio of the 2x2 table over its standard error, summed exactly over
    both arms' binomial counts. The estimate must pass the log odds ratio at which the Wald
    statistic reaches its critical value with the standard error the planning rates expect."""
    if null_value != 0 or side == "lower":
        raise ValueError("The Wald enumeration supports a zero difference, higher or both.")
    p_c, p_t = point["p_control"], point["p_treatment"]
    power = wald_rejection(n_control, n_treatment, alpha, side, p_c, p_t)
    expected = (
        1 / (n_control * p_c * (1 - p_c)) + 1 / (n_treatment * p_t * (1 - p_t))
        if 0 < p_c < 1 and 0 < p_t < 1
        else math.inf
    )
    se = math.sqrt(expected)
    z = _quantile(alpha, side)
    one_sided = side == "higher"
    sign = 1 if one_sided or p_t >= p_c else -1
    critical = math.exp(sign * z * se) if math.isfinite(se) else math.inf
    return PowerResult(power, critical, "above" if sign > 0 else "below", se)


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


def log_rank_times(point, n_control, n_treatment, null_value, alpha, side) -> PowerResult:
    """Schoenfeld's formula at the expected number of events. Times are exponential, the
    control hazard log 2 / median; participants enter uniformly over the accrual period and
    are followed to its end plus the follow-up; dropout is exponential, with probability
    `dropout` by `dropout_time`. A participant has an event by the analysis with probability
    h / (h + d) (1 - (e^(-(h + d) f) - e^(-(h + d)(a + f))) / ((h + d) a)) for hazard h,
    dropout hazard d, accrual a and follow-up f, or h / (h + d) (1 - e^(-(h + d) f)) when
    a = 0."""
    if side != "both" or null_value != 0:
        raise ValueError("The log-rank power formula is for the two-sided test of equal survival.")
    control = math.log(2) / point["control_median"]
    dropout = point.get("dropout", 0.0)
    loss = -math.log1p(-dropout) / point["dropout_time"] if dropout else 0.0
    accrual, follow_up = point["accrual"], point["follow_up"]

    def event_probability(hazard: float) -> float:
        rate = hazard + loss
        if accrual == 0:
            seen = -math.expm1(-rate * follow_up)
        else:
            seen = 1 - (math.exp(-rate * follow_up) - math.exp(-rate * (accrual + follow_up))) / (
                rate * accrual
            )
        return hazard / rate * seen

    probabilities = (event_probability(control), event_probability(point["value"] * control))
    events = n_control * probabilities[0] + n_treatment * probabilities[1]
    share = n_control / (n_control + n_treatment)
    se = 1 / math.sqrt(events * share * (1 - share))
    z = _quantile(alpha, side)
    log_ratio = math.log(point["value"])
    sign = 1 if log_ratio >= 0 else -1
    return PowerResult(
        _NORMAL.cdf(abs(log_ratio) / se - z),
        math.exp(sign * z * se),
        _side(log_ratio),
        se,
        events,
        probabilities,
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
WALD_EXACT = "sum over both arms' binomial counts, exact for the Wald test"

LOGISTIC_WALD = PowerFormula(
    key="logistic_wald_enumeration",
    title="Wald test of the treatment coefficient, summed over both arms' binomial counts",
    version=1,
    point="binomial_rates",
    function=logistic_wald,
    assumptions=(WALD_ENUMERATION, UNADJUSTED_PROPORTIONS),
    references=(AGRESTI_2013, HAUCK_DONNER),
    approximation=WALD_EXACT,
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
SCHOENFELD_TIMES = PowerFormula(
    key="schoenfeld_exponential_times",
    title="Log-rank test, Schoenfeld's formula at the events expected from exponential times",
    version=1,
    point="exponential_survival",
    function=log_rank_times,
    assumptions=(
        NORMAL_APPROXIMATION_POWER,
        PROPORTIONAL_HAZARDS,
        AT_RISK_SHARES,
        EXPONENTIAL_TIMES,
        UNIFORM_ACCRUAL,
        EXPONENTIAL_DROPOUT,
    ),
    references=(SCHOENFELD_1981, SCHOENFELD_1983, LACHIN_FOULKES, R_SURVIVAL_PACKAGES),
)
