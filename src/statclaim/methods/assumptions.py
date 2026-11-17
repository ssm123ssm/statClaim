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
DECLARED_VALID = Assumption(
    "declared_test_is_valid",
    "vouched",
    "The declared test rejects its true null with probability at most its level. "
    "StatClaim has no contract or source for this test.",
)
INDEPENDENT_PARTICIPANTS = Assumption(
    "independent_participants",
    "sampling",
    "Participants are independent of one another. Measurements on one participant may be "
    "correlated.",
)
MISSING_AT_RANDOM = Assumption(
    "missing_at_random",
    "sampling",
    "Missing measurements are missing at random given the observed data and the model.",
)
CORRECT_MEAN_MODEL = Assumption(
    "correct_mean_model",
    "distribution",
    "The model for the mean, with its covariates, is fixed in advance and correctly specified.",
)
COVARIANCE_STRUCTURE = Assumption(
    "covariance_structure",
    "distribution",
    "The covariance between a participant's measurements is correctly specified. An "
    "unstructured matrix imposes no structure.",
)
APPROXIMATELY_NORMAL_ESTIMATE = Assumption(
    "approximately_normal_estimate",
    "distribution",
    "Errors are multivariate normal, or the study is large enough for the estimated "
    "treatment contrast to be approximately normal.",
)
LOGIT_LINEAR = Assumption(
    "logit_linear",
    "distribution",
    "The log odds of response are linear in the model's covariates, which are fixed in advance.",
)
NULL_IS_ZERO_COEFFICIENT = Assumption(
    "null_is_zero_coefficient",
    "scope",
    "The test is of the treatment coefficient. Under the declared null, treatment has no "
    "effect on response given the covariates.",
)
ENOUGH_EVENTS = Assumption(
    "enough_events",
    "distribution",
    "There are enough responders and non-responders in each arm for the estimated "
    "coefficient to be approximately normal, with no separation.",
)

# Assumptions of the approximate power formulas in power.py. Power is a calculation,
# so these concern how the number was obtained, not the test's error rate.
NORMAL_APPROXIMATION_POWER = Assumption(
    "normal_approximation_power",
    "approximation",
    "Power comes from a normal approximation to the test statistic, with its variance at "
    "the planning values. It is an approximation, not a bound.",
)
PLANNING_SD = Assumption(
    "planning_standard_deviation",
    "scope",
    "The standard deviation is a planning input, not an established fact. It is the "
    "standard deviation of one participant's outcome on the analysed scale; for a mixed "
    "model, the effective standard deviation of the contrast.",
)
UNADJUSTED_PROPORTIONS = Assumption(
    "unadjusted_proportions",
    "approximation",
    "Power is for an unadjusted comparison of two proportions. Covariates in the analysis "
    "model change it.",
)
PROPORTIONAL_HAZARDS = Assumption(
    "proportional_hazards",
    "distribution",
    "The hazard ratio is constant over time. The log-rank test's error rate does not need "
    "this; its power formula does.",
)
PLANNING_EVENTS = Assumption(
    "planning_events",
    "scope",
    "The number of events is a planning input, not an established fact. Power depends on "
    "the events, not on the arm sizes.",
)
AT_RISK_SHARES = Assumption(
    "at_risk_shares",
    "approximation",
    "Each arm's share of the participants at risk stays close to its share at "
    "randomisation, as when the hazard ratio is near 1.",
)
