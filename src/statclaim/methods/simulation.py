"""Simulation models for cited tests: how one simulated study is drawn and tested.

Each model simulates the cited test itself, with its own critical values, at the
planning point. Power found this way is an estimate with Monte Carlo error, shown by
its interval; it is never a bound and never evidence for the test's guarantee.
"""

import math

from statclaim.methods.assumptions import (
    MONTE_CARLO_ERROR,
    PLANNING_ICC,
    PLANNING_SD,
    SIMULATED_ASSOCIATION,
    SIMULATED_CLUSTER_PROPORTIONS,
    SIMULATED_CLUSTERS,
    SIMULATED_SURVIVAL,
    SIMULATED_TWO_MEANS,
)
from statclaim.methods.core import SimulationModel
from statclaim.simulation import (
    REFERENCES,
    cluster_trial,
    correlation_trial,
    log_rank_trial,
    two_means_trial,
)

STUDENT_1908 = "Student (1908). The probable error of a mean. Biometrika 6(1), 1-25."
WELCH_1947 = (
    "Welch, B. L. (1947). The generalization of 'Student's' problem when several different "
    "population variances are involved. Biometrika 34(1-2), 28-35."
)


def _two_means_scenario(point: dict) -> str:
    sd, sd_treatment = point["sd"], point.get("sd_treatment", point["sd"])
    skewness = point.get("skewness", 0.0)
    shape = f"gamma-shaped outcomes (skewness {skewness:g})" if skewness else "normal outcomes"
    spread = (
        f"standard deviation {sd:g} in both arms"
        if sd_treatment == sd
        else f"standard deviations {sd:g} (control) and {sd_treatment:g} (treatment)"
    )
    return f"{shape} with {spread} and a true mean difference of {point['value']:g}"


def _two_means(point, n_control, n_treatment, null_value, alpha, side, welch):
    return two_means_trial(
        point["value"],
        point["sd"],
        n_control,
        n_treatment,
        null_value,
        alpha,
        side,
        welch=welch,
        sd_treatment=point.get("sd_treatment"),
        skewness=point.get("skewness", 0.0),
    )


def _student(point, n_control, n_treatment, null_value, alpha, side):
    """Student's pooled t-test on simulated outcomes of the declared scenario."""
    return _two_means(point, n_control, n_treatment, null_value, alpha, side, welch=False)


def _welch(point, n_control, n_treatment, null_value, alpha, side):
    """Welch's t-test on simulated outcomes of the declared scenario."""
    return _two_means(point, n_control, n_treatment, null_value, alpha, side, welch=True)


# Version 2: also simulates unequal SDs and skewed outcomes.
STUDENT = SimulationModel(
    key="normal_two_means_student",
    title="Student's t-test on simulated outcomes",
    version=2,
    point="mean_difference",
    trial=_student,
    scenario=_two_means_scenario,
    assumptions=(SIMULATED_TWO_MEANS, PLANNING_SD, MONTE_CARLO_ERROR),
    references=(STUDENT_1908, *REFERENCES),
)
WELCH = SimulationModel(
    key="normal_two_means_welch",
    title="Welch's t-test on simulated outcomes",
    version=2,
    point="mean_difference",
    trial=_welch,
    scenario=_two_means_scenario,
    assumptions=(SIMULATED_TWO_MEANS, PLANNING_SD, MONTE_CARLO_ERROR),
    references=(WELCH_1947, *REFERENCES),
)


def _cluster_scenario(point: dict) -> str:
    sizes = f"{point['size_control']:g} and {point['size_treatment']:g} participants per cluster"
    varied = (
        f", varying with coefficient of variation {point.get('cluster_size_cv', 0.0):g}"
        if point.get("cluster_size_cv")
        else ""
    )
    effect = (
        f"a true difference of {point['value']:g}"
        if "value" in point
        else f"rates {point['p_control']:g} and {point['p_treatment']:g}"
    )
    return f"clusters of {sizes}{varied}, intracluster correlation {point['icc']:g}, {effect}"


def _cluster_means(point, n_control, n_treatment, null_value, alpha, side):
    """The t-test on cluster means: each cluster has a normal effect with variance
    icc sd^2, and its m participants a mean about it with variance (1 - icc) sd^2 / m."""
    if side != "both" or null_value != 0:
        raise ValueError("The cluster t-test is two-sided, of equal means.")
    sd, icc = point["sd"], point["icc"]
    between, within = sd * math.sqrt(icc), sd * math.sqrt(1.0 - icc)
    shift = (0.0, point["value"])

    def summary(stream, size, arm):
        return shift[arm] + between * stream.normal() + within / math.sqrt(size) * stream.normal()

    sizes = (point["size_control"], point["size_treatment"])
    return cluster_trial(
        summary, (n_control, n_treatment), sizes, point.get("cluster_size_cv", 0.0), alpha
    )


def _cluster_proportions(point, n_control, n_treatment, null_value, alpha, side):
    """The t-test on cluster proportions: each cluster's rate is beta with the arm's rate as
    its mean and icc as the intracluster correlation, and its responses binomial."""
    if side != "both" or null_value != 0:
        raise ValueError("The cluster t-test is two-sided, of equal proportions.")
    icc, rates = point["icc"], (point["p_control"], point["p_treatment"])

    def summary(stream, size, arm):
        p = rates[arm]
        if icc > 0 and 0 < p < 1:
            p = stream.beta(p * (1 - icc) / icc, (1 - p) * (1 - icc) / icc)
        return stream.binomial(size, p) / size

    sizes = (point["size_control"], point["size_treatment"])
    return cluster_trial(
        summary, (n_control, n_treatment), sizes, point.get("cluster_size_cv", 0.0), alpha
    )


CLUSTER_MEANS = SimulationModel(
    key="cluster_t_means_simulated",
    title="t-test on simulated cluster means with a random cluster effect",
    version=1,
    point="mean_difference",
    trial=_cluster_means,
    scenario=_cluster_scenario,
    assumptions=(SIMULATED_CLUSTERS, PLANNING_SD, PLANNING_ICC, MONTE_CARLO_ERROR),
    references=(STUDENT_1908, *REFERENCES),
)
CLUSTER_PROPORTIONS = SimulationModel(
    key="cluster_t_proportions_simulated",
    title="t-test on simulated cluster proportions with beta-distributed cluster rates",
    version=1,
    point="binomial_rates",
    trial=_cluster_proportions,
    scenario=_cluster_scenario,
    assumptions=(SIMULATED_CLUSTER_PROPORTIONS, PLANNING_ICC, MONTE_CARLO_ERROR),
    references=(STUDENT_1908, *REFERENCES),
)


MANTEL_1966 = (
    "Mantel, N. (1966). Evaluation of survival data and two new rank order statistics arising "
    "in its consideration. Cancer Chemotherapy Reports 50(3), 163-170."
)


def _survival_scenario(point: dict) -> str:
    delay = point.get("effect_delay", 0.0)
    effect = (
        f"hazard ratio {point['value']:g} from {delay:g} after entry"
        if delay
        else f"hazard ratio {point['value']:g}"
    )
    lost = (
        f", {point['dropout']:g} dropping out by {point['dropout_time']:g}"
        if point.get("dropout")
        else ""
    )
    return (
        f"exponential times with control median {point['control_median']:g} and {effect}, "
        f"accrual over {point['accrual']:g} and follow-up of {point['follow_up']:g}{lost}"
    )


def _log_rank(point, n_control, n_treatment, null_value, alpha, side):
    """The two-sided log-rank test on simulated exponential survival times."""
    if side != "both":
        raise ValueError("The log-rank test is two-sided, of equal survival.")
    return log_rank_trial(
        point["value"],
        point["control_median"],
        point["accrual"],
        point["follow_up"],
        n_control,
        n_treatment,
        alpha,
        dropout=point.get("dropout", 0.0),
        dropout_time=point.get("dropout_time", 1.0),
        delay=point.get("effect_delay", 0.0),
    )


LOG_RANK = SimulationModel(
    key="log_rank_simulated",
    title="Log-rank test on simulated exponential survival times",
    version=1,
    point="exponential_survival",
    trial=_log_rank,
    scenario=_survival_scenario,
    assumptions=(SIMULATED_SURVIVAL, MONTE_CARLO_ERROR),
    references=(MANTEL_1966, *REFERENCES),
)


# Cited tests of observational studies take a total and covariates:
# trial(point, n, covariates, alpha).
FISHER_1915 = (
    "Fisher, R. A. (1915). Frequency distribution of the values of the correlation coefficient "
    "in samples from an indefinitely large population. Biometrika 10(4), 507-521."
)


def _skew_words(point: dict) -> str:
    parts = [
        f"{label} with skewness {point[name]:g}"
        for name, label in (("exposure_skewness", "an exposure"), ("skewness", "an outcome error"))
        if point.get(name)
    ]
    return " and ".join(parts) or "normal data"


def _correlation_scenario(point: dict) -> str:
    return f"{_skew_words(point)}, and a correlation of {point['value']:g}"


def _slope_scenario(point: dict) -> str:
    return (
        f"{_skew_words(point)}, a slope of {point['value']:g}, exposure SD "
        f"{point['exposure_sd']:g} and residual SD {point['residual_sd']:g}"
    )


def _skews(point: dict) -> dict:
    return {
        "skewness": point.get("skewness", 0.0),
        "exposure_skewness": point.get("exposure_skewness", 0.0),
    }


def _pearson(point, n, covariates, alpha):
    """The t-test of Pearson's correlation on simulated, possibly skewed, data."""
    return correlation_trial(point["value"], n, alpha, **_skews(point))


def _slope(point, n, covariates, alpha):
    """The t-test of a simple regression's slope, which is the correlation's t-test at the
    correlation slope * exposure SD / the root of slope^2 exposure SD^2 + residual SD^2."""
    if covariates:
        raise ValueError("Skewed data are simulated without covariates.")
    signal = point["value"] * point["exposure_sd"]
    rho = signal / math.sqrt(signal * signal + point["residual_sd"] ** 2)
    return correlation_trial(rho, n, alpha, **_skews(point))


PEARSON = SimulationModel(
    key="pearson_simulated",
    title="t-test of Pearson's correlation on simulated skewed data",
    version=1,
    point="correlation",
    trial=_pearson,
    scenario=_correlation_scenario,
    assumptions=(SIMULATED_ASSOCIATION, MONTE_CARLO_ERROR),
    references=(FISHER_1915, *REFERENCES),
)
SLOPE = SimulationModel(
    key="slope_simulated",
    title="t-test of a regression slope on simulated skewed data",
    version=1,
    point="slope",
    trial=_slope,
    scenario=_slope_scenario,
    assumptions=(SIMULATED_ASSOCIATION, MONTE_CARLO_ERROR),
    references=(FISHER_1915, *REFERENCES),
)
