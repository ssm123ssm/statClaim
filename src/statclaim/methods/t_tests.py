"""Two-sample t-tests for a difference of means. Guarantees are cited, not proved."""

from statclaim.methods.assumptions import (
    EQUAL_VARIANCES,
    FINITE_VARIANCE,
    FIXED_SIZES,
    INDEPENDENT,
    NORMAL,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import CitedMethod, MethodModule
from statclaim.methods.power import TWO_MEANS

STUDENT = "Student (1908). The probable error of a mean. Biometrika 6(1), 1-25."
FISHER = "Fisher, R. A. (1925). Applications of 'Student's' distribution. Metron 5, 90-104."
WELCH = (
    "Welch, B. L. (1947). The generalization of 'Student's' problem when several different "
    "population variances are involved. Biometrika 34(1-2), 28-35."
)
SATTERTHWAITE = (
    "Satterthwaite, F. E. (1946). An approximate distribution of estimates of variance "
    "components. Biometrics Bulletin 2(6), 110-114."
)
LEHMANN_ROMANO = (
    "Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses, 3rd ed. "
    "Springer. Chapters 5 and 11."
)

# Exact under normality with a common variance.
_POOLED = dict(
    outcome="continuous",
    module="tests.t",
    version=1,
    scope="finite_sample",
    assumptions=(INDEPENDENT, FIXED_SIZES, SINGLE_ANALYSIS, NORMAL, EQUAL_VARIANCES),
    references=(STUDENT, FISHER, LEHMANN_ROMANO),
    min_per_arm=1,
    min_total=3,
    power=TWO_MEANS,
)
# Needs no normality or common variance, but its level is only approximate.
_WELCH = dict(
    outcome="continuous",
    module="tests.t",
    version=1,
    scope="asymptotic",
    assumptions=(INDEPENDENT, FIXED_SIZES, SINGLE_ANALYSIS, FINITE_VARIANCE),
    references=(WELCH, SATTERTHWAITE, LEHMANN_ROMANO),
    min_per_arm=2,
    min_total=4,
    power=TWO_MEANS,
)

MODULE = MethodModule(
    "tests.t",
    "Pooled-variance and Welch t-tests for two means. The compiler checks the null and the "
    "sampling plan against each test's contract. The Type I guarantee is cited from the "
    "literature and is not checked by Lean: exact under normality and equal variances for "
    "the pooled test, a large-sample approximation for Welch.",
    (
        CitedMethod(
            key="t_test",
            title="Two-sided pooled-variance t-test",
            null="equal_means",
            relation="equals",
            **_POOLED,
        ),
        CitedMethod(
            key="t_test_one_sided",
            title="One-sided pooled-variance t-test",
            null="mean_difference_at_most",
            relation="at_most",
            **_POOLED,
        ),
        CitedMethod(
            key="welch_test",
            title="Two-sided Welch t-test",
            null="equal_means",
            relation="equals",
            **_WELCH,
        ),
        CitedMethod(
            key="welch_test_one_sided",
            title="One-sided Welch t-test",
            null="mean_difference_at_most",
            relation="at_most",
            **_WELCH,
        ),
    ),
)
