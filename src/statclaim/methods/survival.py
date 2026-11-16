"""Tests for a time-to-event outcome. Guarantees are cited, not proved."""

from statclaim.methods.assumptions import (
    INDEPENDENT,
    INDEPENDENT_CENSORING,
    PRESPECIFIED_ANALYSIS_TIME,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import CitedMethod, MethodModule

MANTEL = (
    "Mantel, N. (1966). Evaluation of survival data and two new rank order statistics "
    "arising in its consideration. Cancer Chemotherapy Reports 50(3), 163-170."
)
PETO = (
    "Peto, R. and Peto, J. (1972). Asymptotically efficient rank invariant test procedures. "
    "Journal of the Royal Statistical Society A 135(2), 185-207."
)
FLEMING_HARRINGTON = (
    "Fleming, T. R. and Harrington, D. P. (1991). Counting Processes and Survival Analysis. Wiley."
)

MODULE = MethodModule(
    "tests.survival",
    "The log-rank test for two survival curves. The compiler checks the null and the "
    "sampling plan against the test's contract. The Type I guarantee is cited from the "
    "literature and is a large-sample approximation in the number of events. Proportional "
    "hazards is not needed for the error rate; it matters for power.",
    (
        CitedMethod(
            key="log_rank",
            module="tests.survival",
            title="Two-sided log-rank test",
            version=1,
            outcome="survival",
            null="equal_survival",
            relation="equals",
            scope="asymptotic",
            limit="the number of events grows",
            assumptions=(
                INDEPENDENT,
                INDEPENDENT_CENSORING,
                PRESPECIFIED_ANALYSIS_TIME,
                SINGLE_ANALYSIS,
            ),
            references=(MANTEL, PETO, FLEMING_HARRINGTON),
            min_per_arm=1,
            min_total=2,
        ),
    ),
)
