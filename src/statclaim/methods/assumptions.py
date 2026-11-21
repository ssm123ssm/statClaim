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
INDEPENDENT_CLUSTERS = Assumption(
    "independent_clusters",
    "sampling",
    "Clusters are independent of one another. Participants in one cluster may be correlated.",
)
NORMAL_CLUSTER_SUMMARIES = Assumption(
    "normal_cluster_summaries",
    "distribution",
    "Each cluster's summary, such as its mean outcome, is normally distributed with the same "
    "variance in both arms. Clusters of very different sizes make this doubtful.",
)
NORMAL_CLUSTER_PROPORTIONS = Assumption(
    "normal_cluster_proportions",
    "distribution",
    "Each cluster's proportion of responders is close enough to normally distributed, with "
    "the same variance in both arms, for a t-test. Small clusters, rare or very common "
    "responses, and clusters of very different sizes make this doubtful.",
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

# The direction of benefit, listed when a one-sided null is used and the model does not
# declare which direction is better. Declaring it with better= has it checked instead.
HIGHER_IS_BETTER = Assumption(
    "higher_is_better",
    "meaning",
    "Higher values of the outcome are better: the one-sided null asks whether the "
    'treatment\'s are higher. The file does not say so; declare better="higher" on the '
    "model to have this checked.",
)
LOWER_IS_BETTER = Assumption(
    "lower_is_better",
    "meaning",
    "Lower values of the outcome are better: the one-sided null asks whether the "
    'treatment\'s are lower. The file does not say so; declare better="lower" on the '
    "model to have this checked.",
)

# What a file can declare about its design, and the assumptions each feature contradicts.
# A test that rests on a contradicted assumption is refused for that design. The ids
# include independent_binomial_arms, the Lean-backed tests' assumption (identify.py).
CONTRADICTED_BY = {
    # Measurements on one participant are correlated, so they are not independent
    # observations, and they are not separate binomial trials.
    "repeated_measures": ("independent_observations", "independent_binomial_arms"),
    # Participants in one cluster tend to be alike, so they are not independent.
    "clusters": (
        "independent_observations",
        "independent_participants",
        "independent_binomial_arms",
    ),
}
# A declared test is taken on the author's word, so each feature adds what it must do.
ACCOUNTS_FOR = {
    "repeated_measures": Assumption(
        "accounts_for_repeated_measures",
        "vouched",
        "The declared test accounts for the several measurements on each participant, "
        "which may be correlated.",
    ),
    "clusters": Assumption(
        "accounts_for_clusters",
        "vouched",
        "The declared test accounts for randomisation by cluster: participants in one "
        "cluster may be correlated.",
    ),
}

# Who is analysed, as an assignment can declare with population=. A randomisation test
# needs everyone randomised, so per_protocol contradicts it; other tests take either, and
# their claims say which population the bound covers.
POPULATIONS = {
    "randomised": "Everyone randomised, analysed in the arm they were assigned to (intention "
    "to treat). Turns a randomisation test's analysed_as_randomised into a declaration.",
    "per_protocol": "Participants excluded after randomisation are left out; the arm sizes "
    "count those analysed. A randomisation test is refused; other claims say they cover this "
    "population only, and list as assumed that exclusions were not chosen from the results.",
}
RANDOMISED_POPULATION = Assumption(
    "randomised_population",
    "scope",
    "The bound covers the randomised population: everyone randomised, analysed in the arm "
    "they were assigned to, as the assignment declares.",
)
PER_PROTOCOL_POPULATION = Assumption(
    "per_protocol_population",
    "scope",
    "The bound covers the per-protocol population only, as the assignment declares: "
    "participants excluded after randomisation are left out. Randomisation does not make the "
    "arms' remaining groups comparable, so a difference between them need not be caused by "
    "treatment.",
)
# The arm sizes a per-protocol file declares count those left after exclusions, so they
# were not fixed before outcomes in the way a fixed design's sizes are.
PRESPECIFIED_EXCLUSIONS = Assumption(
    "prespecified_exclusions",
    "sampling",
    "Who is excluded after randomisation was decided by rules fixed before outcomes were "
    "observed, so the arm sizes analysed were not chosen by looking at the results.",
)
POPULATION_COVERED = {
    "randomised": (RANDOMISED_POPULATION,),
    "per_protocol": (PER_PROTOCOL_POPULATION, PRESPECIFIED_EXCLUSIONS),
}

# Assumptions of the approximate power formulas in power.py. Power is a calculation,
# so these concern how the number was obtained, not the test's error rate.
NORMAL_APPROXIMATION_POWER = Assumption(
    "normal_approximation_power",
    "approximation",
    "Power comes from a normal approximation to the test statistic, with its variance at "
    "the planning values. It is an approximation, not a bound.",
)
SIMULATED_NORMAL = Assumption(
    "simulated_normal_outcomes",
    "monte_carlo",
    "The simulation draws normal outcomes with the planning standard deviation in both arms. "
    "Power for outcomes with another distribution or unequal spreads may differ.",
)
MONTE_CARLO_ERROR = Assumption(
    "monte_carlo_error",
    "monte_carlo",
    "Simulated power and Type I error are estimates with Monte Carlo error. Each 95% "
    "interval covers the true rate in 95% of simulations; a size found by search is "
    "confirmed by an independent run. An estimate is not a bound.",
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
NONCENTRAL_T_POWER = Assumption(
    "noncentral_t_power",
    "approximation",
    "Power comes from the noncentral t distribution of the t-test on cluster summaries, with "
    "the variance of a cluster's summary at the planning values. Exact for normal cluster "
    "means of equal variance; otherwise an approximation, not a bound.",
)
PLANNING_ICC = Assumption(
    "planning_icc",
    "scope",
    "The intracluster correlation is a planning input, not an established fact: the share of "
    "the outcome's variance that lies between clusters. A cluster of m participants has a "
    "summary with variance (1 + (m - 1) icc) / m times that of one participant.",
)
EQUAL_CLUSTER_SIZES = Assumption(
    "equal_cluster_sizes",
    "approximation",
    "Every cluster in an arm has the arm's mean size. Clusters of unequal sizes give less "
    "power than this.",
)
