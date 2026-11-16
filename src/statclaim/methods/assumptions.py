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
