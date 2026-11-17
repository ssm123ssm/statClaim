"""Assumptions shared between methods. Reuse an entry before adding a new one.

An id never changes meaning. To change what an assumption says, add a new id.
"""

from statclaim.methods.core import Assumption

INDEPENDENT = Assumption(
    "independent_observations",
    "sampling",
    "Observations are independent within and between the two arms.",
)
FIXED_SIZES = Assumption(
    "fixed_sample_sizes", "design", "Arm sizes are fixed before observing outcomes."
)
SINGLE_ANALYSIS = Assumption(
    "single_analysis", "design", "The test is run once, on the complete data."
)
NORMAL = Assumption(
    "normal_outcomes", "distribution", "Outcomes in each arm are normally distributed."
)
EQUAL_VARIANCES = Assumption(
    "equal_variances", "distribution", "The two arms have the same variance."
)
FINITE_VARIANCE = Assumption(
    "finite_variance",
    "distribution",
    "Outcomes in each arm are identically distributed with finite, positive variance.",
)
PRESPECIFIED_FAMILY = Assumption(
    "prespecified_family",
    "design",
    "The set of analyses and their levels are chosen before outcomes are observed.",
)
INDEPENDENT_CENSORING = Assumption(
    "independent_censoring",
    "sampling",
    "Within each arm, censoring is independent of the time to the event.",
)
PRESPECIFIED_ANALYSIS_TIME = Assumption(
    "prespecified_analysis_time",
    "design",
    "When to analyse is fixed in advance, by calendar time or by a number of events, and "
    "does not depend on the observed difference between arms.",
)
PRESPECIFIED_LOOKS = Assumption(
    "prespecified_looks",
    "design",
    "The looks happen at the declared cumulative sample sizes, fixed in advance, and the "
    "study stops at the first look that rejects.",
)
PRESPECIFIED_ORDER = Assumption(
    "prespecified_order",
    "design",
    "The tests and their order are fixed in advance, and a test is carried out only if "
    "every earlier test in the order rejected.",
)
PRESPECIFIED_GRAPH = Assumption(
    "prespecified_graph",
    "design",
    "The tests, their starting shares of the level and the rules for passing a share on "
    "are fixed in advance, and a share is passed on only after a rejection. Each test "
    "controls its error at every level up to the overall level, not only at one.",
)
