"""Simulation models for cited tests: how one simulated study is drawn and tested.

Each model simulates the cited test itself, with its own critical values, at the
planning point. Power found this way is an estimate with Monte Carlo error, shown by
its interval; it is never a bound and never evidence for the test's guarantee.
"""

from statclaim.methods.assumptions import MONTE_CARLO_ERROR, PLANNING_SD, SIMULATED_NORMAL
from statclaim.methods.core import SimulationModel
from statclaim.simulation import REFERENCES, two_means_trial

STUDENT_1908 = "Student (1908). The probable error of a mean. Biometrika 6(1), 1-25."
WELCH_1947 = (
    "Welch, B. L. (1947). The generalization of 'Student's' problem when several different "
    "population variances are involved. Biometrika 34(1-2), 28-35."
)


def _normal_scenario(point: dict) -> str:
    return (
        f"normal outcomes with standard deviation {point['sd']:g} in both arms and a true mean "
        f"difference of {point['value']:g}"
    )


def _student(point, n_control, n_treatment, null_value, alpha, side):
    """Student's pooled t-test on simulated normal outcomes."""
    return two_means_trial(
        point["value"], point["sd"], n_control, n_treatment, null_value, alpha, side, welch=False
    )


def _welch(point, n_control, n_treatment, null_value, alpha, side):
    """Welch's t-test on simulated normal outcomes."""
    return two_means_trial(
        point["value"], point["sd"], n_control, n_treatment, null_value, alpha, side, welch=True
    )


STUDENT = SimulationModel(
    key="normal_two_means_student",
    title="Student's t-test on simulated normal outcomes",
    version=1,
    point="mean_difference",
    trial=_student,
    scenario=_normal_scenario,
    assumptions=(SIMULATED_NORMAL, PLANNING_SD, MONTE_CARLO_ERROR),
    references=(STUDENT_1908, *REFERENCES),
)
WELCH = SimulationModel(
    key="normal_two_means_welch",
    title="Welch's t-test on simulated normal outcomes",
    version=1,
    point="mean_difference",
    trial=_welch,
    scenario=_normal_scenario,
    assumptions=(SIMULATED_NORMAL, PLANNING_SD, MONTE_CARLO_ERROR),
    references=(WELCH_1947, *REFERENCES),
)
