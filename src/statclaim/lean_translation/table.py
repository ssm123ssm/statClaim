"""The Lean meaning or evidence boundary of every DSL constructor and operation."""

from dataclasses import dataclass

ROLES = {
    "model": "A study model or a part of one: arms, outcome, assignment, strata.",
    "design": "A sampling plan or a stopping rule.",
    "null": "A null hypothesis, as a predicate on the model's parameters.",
    "analysis": "A test whose guarantee a Lean module proves.",
    "premise": "A test whose guarantee enters as a named premise, cited or declared.",
    "composition": "A rule combining the members' guarantees, proved in Lean or cited.",
    "claim": "A proposition the program states.",
    "data": "Observed data, checked against the model's outcome domain.",
    "planning": "A planning input; it has a Lean meaning when its analysis is exact.",
    "operation": "A request for evidence.",
}

# Lean files the table may name before they exist.
PLANNED: tuple[str, ...] = ()


@dataclass(frozen=True)
class InLean:
    role: str
    lean: tuple[str, ...]  # the Lean files, from the repository root, that give it meaning


@dataclass(frozen=True)
class NotInLean:
    reason: str


def _in(role: str, *files: str) -> InLean:
    return InLean(role, tuple(f"StatClaim/{name}.lean" for name in files))


CORE = "Core/Objects"
POLICY = "Core/Policy"
OUTCOMES = "Interface/Outcomes"
PREMISES = "Interface/Premises"
PROGRAM = "Semantics/Meaning"
RESULTS = "Semantics/Results"
INTERVALS = "Semantics/Intervals"
PLANS = "Semantics/Plans"
METHODS = "Generated/Methods"
BINOMIAL = "Modules/TwoArmBinomial"
RANDOMISATION = "Modules/Randomisation"
ASSOCIATION = "Modules/Association"
INCIDENCE = "Modules/Incidence"
MATCHED = "Modules/Matched"
INTERVAL = "Modules/BinomialInterval"
ONE_SAMPLE = "Modules/OneSampleBinomial"
TWO_STAGE = "Modules/TwoStageBinomial"
COMPOSITION = "Modules/Composition"

# The guarantee of every cited test enters as a premise generated from the method registry.
CITED = _in("premise", METHODS, PREMISES)

APPROXIMATE = NotInLean(
    "A planning point for an approximate power formula or a simulation; its results are "
    "calculated or simulated, never proved."
)
PRECISION = NotInLean("Precision searches are calculations; Lean does not check them.")

TABLE: dict[str, InLean | NotInLean] = {
    # Two-arm models and their parts. Binary outcomes have a Lean law; continuous and
    # survival outcomes are abstract models whose claims hold for any law meeting the premises.
    "two_arm_binomial": _in("model", BINOMIAL),
    "two_arm_continuous": _in("model", OUTCOMES),
    "two_arm_survival": _in("model", OUTCOMES),
    "two_arm": _in("model", BINOMIAL, OUTCOMES),
    "assignment": _in("model", OUTCOMES, RANDOMISATION),
    "cluster_assignment": _in("model", OUTCOMES, RANDOMISATION),
    "stratum": _in("model", RANDOMISATION),
    "binary_outcome": _in("model", BINOMIAL),
    "continuous_outcome": _in("model", OUTCOMES),
    "survival_outcome": _in("model", OUTCOMES),
    # Nulls.
    "equal_proportions": _in("null", BINOMIAL),
    "proportion_difference": _in("null", BINOMIAL),
    "proportion_difference_at_most": _in("null", "Modules/DifferenceTest"),
    "equal_means": _in("null", OUTCOMES),
    "mean_difference_at_most": _in("null", OUTCOMES),
    "mean_difference_at_least": _in("null", OUTCOMES),
    "equal_survival": _in("null", OUTCOMES),
    "no_effect": _in("null", RANDOMISATION),
    "no_association": _in("null", ASSOCIATION, OUTCOMES),
    # Sampling plans and stopping rules.
    "fixed": _in("design", CORE),
    "adaptive": _in("design", CORE),
    "two_stage_binomial": _in("design", TWO_STAGE, POLICY),
    "threshold_rule": _in("design", TWO_STAGE),
    "posterior_rule": _in("design", TWO_STAGE),
    "beta_prior": _in("design", TWO_STAGE),
    "blinded_reestimation": NotInLean(
        "Its Type I error is estimated by simulation at declared null scenarios, not proved."
    ),
    # Analyses proved in Lean.
    "fisher": _in("analysis", "Modules/Fisher"),
    "fisher_one_sided": _in("analysis", "Modules/FisherOneSided"),
    "difference_test": _in("analysis", "Modules/DifferenceTest"),
    "randomisation_test": _in("analysis", RANDOMISATION),
    "binomial_test": _in("analysis", ONE_SAMPLE),
    "two_stage_test": _in("analysis", TWO_STAGE),
    "fisher_exact": _in("analysis", ASSOCIATION),
    "rate_test": _in("analysis", INCIDENCE),
    "mcnemar": _in("analysis", MATCHED),
    # Cited tests, from the method registry.
    "t_test": CITED,
    "t_test_one_sided": CITED,
    "welch_test": CITED,
    "welch_test_one_sided": CITED,
    "mmrm_test": CITED,
    "mmrm_test_one_sided": CITED,
    "log_rank": CITED,
    "logistic_regression": CITED,
    "logistic_regression_one_sided": CITED,
    "cluster_t_test": CITED,
    "cluster_proportion_t_test": CITED,
    "logistic_association": CITED,
    "conditional_logistic": CITED,
    "poisson_rate_regression": CITED,
    "modified_poisson": CITED,
    "linear_association": CITED,
    "pearson_correlation": CITED,
    "spearman_correlation": CITED,
    "survey_logistic": CITED,
    "survey_linear": CITED,
    "rao_scott_test": CITED,
    # The author names the method and vouches for it; its premise is made per declaration.
    "declared_test": _in("premise", PREMISES),
    # Combinations of guarantees. The graphical procedure's guarantee is cited.
    "bonferroni": _in(
        "composition",
        COMPOSITION,
        "Modules/Bonferroni",
        "Modules/FisherFamily",
        "Modules/FisherFamilyN",
    ),
    "fixed_sequence": _in("composition", COMPOSITION),
    "alpha_spending": _in("composition", COMPOSITION),
    "graphical": _in("composition", PREMISES),
    # Observational studies: concrete laws for exact tests, abstract ones for cited tests.
    "cross_sectional": _in("model", ASSOCIATION, OUTCOMES),
    "cohort": _in("model", ASSOCIATION, OUTCOMES),
    "case_control": _in("model", ASSOCIATION, OUTCOMES),
    "person_time_cohort": _in("model", INCIDENCE, OUTCOMES),
    "matched_case_control": _in("model", MATCHED, OUTCOMES),
    # Single-arm models.
    "one_arm_binomial": _in("model", ONE_SAMPLE),
    # Observed data.
    "observe": _in("data", BINOMIAL),
    "responses": _in("data", ONE_SAMPLE),
    "observed_table": _in("data", ASSOCIATION),
    "observed_pairs": _in("data", MATCHED),
    "observed_events": _in("data", INCIDENCE),
    "stopped_at_interim": _in("data", TWO_STAGE),
    "completed_stages": _in("data", TWO_STAGE),
    # Claims about procedures and families.
    "typeI": _in("claim", PROGRAM, CORE, POLICY),
    "familywise": _in("claim", PROGRAM, COMPOSITION),
    # Claims about observed results: the computed value equals the formal one.
    "result": _in("claim", RESULTS, "Modules/Fisher", "Computation"),
    "binomial_result": _in("claim", RESULTS, ONE_SAMPLE),
    "two_stage_result": _in("claim", RESULTS, TWO_STAGE),
    "association_result": _in("claim", RESULTS, ASSOCIATION),
    "matched_result": _in("claim", RESULTS, MATCHED),
    "rate_result": _in("claim", RESULTS, INCIDENCE),
    # Interval claims: coverage of an exact or conservative interval.
    "confidence_interval": _in("claim", INTERVALS, INTERVAL),
    "difference_interval": _in("claim", INTERVALS, INTERVAL),
    "prevalence": _in("claim", INTERVALS, INTERVAL),
    "cumulative_incidence": _in("claim", INTERVALS, INTERVAL),
    "odds_ratio": _in("claim", INTERVALS, INTERVAL, ASSOCIATION),
    "risk_ratio": _in("claim", INTERVALS, INTERVAL, ASSOCIATION),
    "risk_difference": _in("claim", INTERVALS, INTERVAL, ASSOCIATION),
    "prevalence_ratio": _in("claim", INTERVALS, INTERVAL, ASSOCIATION),
    "prevalence_difference": _in("claim", INTERVALS, INTERVAL, ASSOCIATION),
    "rate_ratio": _in("claim", INTERVALS, INCIDENCE),
    "conditional_odds_ratio": _in("claim", INTERVALS, MATCHED),
    # Planning claims: proved for exact analyses, calculated or simulated for the rest.
    "meets": _in(
        "claim",
        PLANS,
        POLICY,
        "Modules/FisherPower",
        "Modules/BinomialPower",
        "Modules/AssociationPower",
        TWO_STAGE,
    ),
    "sample_size": _in(
        "claim", PLANS, "Modules/FisherPower", "Modules/BinomialPower", "Modules/AssociationPower"
    ),
    "smallest_sample_size": _in(
        "claim", PLANS, "Modules/FisherPower", "Modules/BinomialPower", "Modules/AssociationPower"
    ),
    # Planning inputs for exact analyses.
    "power_target": _in("planning", POLICY),
    "binomial_rates": _in("planning", "Modules/FisherPower"),
    "response_rate": _in("planning", "Modules/BinomialPower", TWO_STAGE),
    "risks": _in("planning", "Modules/AssociationPower"),
    "exposure_prevalence": _in("planning", "Modules/AssociationPower"),
    "outcome_prevalence": _in("planning", "Modules/AssociationPower"),
    "discordant_pairs": _in("planning", "Modules/BinomialPower"),
    "incidence_rates": _in("planning", "Modules/BinomialPower"),
    "equal_arm_sizes": _in("planning", "Modules/FisherPower"),
    "allocated_arm_sizes": _in("planning", "Modules/FisherPower"),
    "cohort_sizes": _in("planning", "Modules/AssociationPower"),
    "case_control_sizes": _in("planning", "Modules/AssociationPower"),
    "total_sizes": _in("planning", "Modules/AssociationPower"),
    "matched_sizes": _in("planning", "Modules/BinomialPower"),
    "event_counts": _in("planning", "Modules/BinomialPower"),
    "sample_sizes": _in("planning", "Modules/BinomialPower", ONE_SAMPLE),
    "two_stage_designs": _in("planning", TWO_STAGE),
    # Planning inputs with no Lean meaning.
    "mean_difference": APPROXIMATE,
    "hazard_ratio": APPROXIMATE,
    "correlation": APPROXIMATE,
    "outcome_means": APPROXIMATE,
    "odds_per_sd": APPROXIMATE,
    "slope": APPROXIMATE,
    "exponential_survival": APPROXIMATE,
    "cluster_counts": APPROXIMATE,
    "cluster_sizes": APPROXIMATE,
    "endpoint_points": NotInLean("The power of a family is simulated, not proved."),
    "null_scenarios": NotInLean(
        "Points at which a simulation judges Type I error; a simulation is never proof."
    ),
    "proportion": PRECISION,
    "precision_target": PRECISION,
    "planned_interval": PRECISION,
    "interval_sizes": PRECISION,
    # Operations.
    "verify": _in("operation", PROGRAM),
    "calculate": NotInLean("A calculation gives numbers, not a proposition to prove."),
    "simulate": NotInLean("A simulation gives estimates with Monte Carlo error, never proof."),
}


def summary() -> dict[str, int]:
    """How many constructors and operations have each role, and how many have none."""
    counts: dict[str, int] = {}
    for entry in TABLE.values():
        key = entry.role if isinstance(entry, InLean) else "not in Lean"
        counts[key] = counts.get(key, 0) + 1
    return counts
