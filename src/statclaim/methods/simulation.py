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
    SIMULATED_CLUSTER_PROPORTIONS,
    SIMULATED_CLUSTERS,
    SIMULATED_TWO_MEANS,
)
from statclaim.methods.core import SimulationModel
from statclaim.simulation import REFERENCES, cluster_trial, two_means_trial

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
