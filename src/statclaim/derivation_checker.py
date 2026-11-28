"""Independent checker for contract derivations.

The checker receives a serialized derivation and trusts none of it. It reads
the facts from the serialized subject, re-evaluates every premise with its own
code, and confirms the derivation's structure: the rules exist, each step's
facts and conclusion are the ones the subject implies, the final step rests on
the required earlier steps, and the open obligations are exactly the obligation
rules that fail.

It imports only data from the rest of StatClaim: the rule statements of
`derivations`, registries, assumption texts and limits. It calls none of StatClaim's
functions, neither the contract code nor the functions that build derivations, and a
test checks this. Where a contract rests on a calculation, the checker does it its own
way: a design's spending boundaries are checked from their definition, by integrating
the chance of crossing each look, not by the code that computed them. A rule name or a
success flag alone never passes.
"""

import json
import math
from contextvars import ContextVar
from fractions import Fraction
from math import comb
from statistics import NormalDist

from statclaim.association import (
    CASE_CONTROL_GROUPS,
    CASE_CONTROL_NULL,
    COHORT_GROUPS,
    COHORT_NULL,
    CROSS_SECTIONAL_NULL,
    INDEPENDENT_EXPOSURES,
    INDEPENDENT_OUTCOMES,
    NULL_STATEMENTS,
    RANDOM_SAMPLE,
    SOURCE_POPULATION,
)
from statclaim.derivations import (
    ANALYSIS_ASSUMPTIONS,
    ASSOCIATION_CONTRACT_ID,
    ASYMPTOTIC_MCNEMAR_CONTRACT_ID,
    CITED_NOT_ESTABLISHED,
    COMPOSED_NOT_ESTABLISHED,
    CONTRACT_IDS,
    DECLARED_NOT_ESTABLISHED,
    FAMILY_ASSUMPTIONS,
    FARRINGTON_MANNING_CONTRACT_ID,
    LIKELIHOOD_RATIO_CONTRACT_ID,
    MCNEMAR_CONTRACT_ID,
    NOT_ESTABLISHED,
    ONE_SAMPLE_ASSUMPTIONS,
    PEARSON_CONTRACT_ID,
    PLANNING_POINT_ASSUMPTION,
    PROPORTION_Z_CONTRACT_IDS,
    RANDOMISATION_CONTRACT_ID,
    RATE_CONTRACT_ID,
    RULES,
    TWO_STAGE_ASSUMPTIONS,
)
from statclaim.incidence import PERSON_TIME, POISSON_EVENTS, RATE_NULL
from statclaim.look_search import MAX_CANDIDATES as MAX_LOOK_CANDIDATES
from statclaim.looks_planning import EXACT_LOOKS, MAX_LOOK_ARM
from statclaim.matched import MATCHED_NULL, PAIRS_SAMPLED, WITHIN_PAIRS
from statclaim.methods import METHODS, NULL_FORMS, OUTCOMES, SHARP_NULL
from statclaim.methods.assumptions import (
    ACCOUNTS_FOR,
    CANONICAL_JOINT,
    CONTRADICTED_BY,
    DECLARED_VALID,
    FIXED_SIZES,
    HIGHER_IS_BETTER,
    LOWER_IS_BETTER,
    PRESPECIFIED_FAMILY,
    PRESPECIFIED_GRAPH,
    PRESPECIFIED_LOOKS,
    PRESPECIFIED_ORDER,
    PRESPECIFIED_SPENDING,
    REESTIMATION_TYPE_I,
    SINGLE_ANALYSIS,
)
from statclaim.methods.boundaries import JENNISON_TURNBULL, LAN_DEMETS, SPENDING
from statclaim.methods.core import SCOPES, CitedMethod, Guarantee
from statclaim.methods.observational import METHODS as OBSERVATIONAL_METHODS
from statclaim.methods.simulation import FAMILY
from statclaim.precision import EXACT_ASSUMPTIONS as PRECISION_EXACT
from statclaim.precision import EXPECTED_GROUPS as PRECISION_GROUPS
from statclaim.precision import MAX_EXACT_PAIRS as PRECISION_PAIRS
from statclaim.precision import MAX_SIZE as PRECISION_LIMIT
from statclaim.precision import MEASURES as PRECISION_MEASURES
from statclaim.precision import METHODS as PRECISION_METHODS
from statclaim.precision import NORMAL_ASSUMPTIONS as PRECISION_NORMAL
from statclaim.precision import PLANNING_POINT as PRECISION_POINT
from statclaim.randomisation import (
    AS_DRAWN,
    AS_RANDOMISED,
    COUNTS_DRAWS,
    COUNTS_EVERY_SPLIT,
    GROUPED,
    POPULATION,
    PRESPECIFIED,
    RANDOMISED,
)
from statclaim.randomisation import (
    SHARP_NULL as SHARP_NULL_TEXT,
)

SUPPORTED_NULLS = {
    "two_sided": ["equal_proportions"],
    # The one-sided test fixes the margin at zero.
    "greater": ["proportion_difference_at_most"],
    # The difference test takes any margin strictly between -1 and 1.
    "margin": ["proportion_difference_at_most"],
}
SUPPORTED_JOINT_LAWS = ["binomial_marginals"]
FAMILY_LIMITS = (2, 20)
ONE_ARM_LIMIT, PER_ARM_LIMIT, STAGE_LIMIT, SEARCH_LIMIT, RATIO_LIMIT = 1000, 500, 200, 120, 10
CITED_ARM_LIMIT = 100_000
CLUSTER_LIMIT, CLUSTER_SIZE_LIMIT = 1000, 10_000  # clusters per arm, participants per cluster
UNIT_LIMIT = 10_000  # randomised units in a randomisation test
DRAW_LIMIT = 10_000_000  # random draws for a Monte Carlo p-value
SCHEMES = ["complete", "stratified", "blocked"]  # schemes the randomisation theorem covers
GROUP_LIMIT = 1_000  # strata or blocks in a randomisation test
# The arguments of each kind of planning point a power formula can take.
POINT_KEYS = {
    "mean_difference": {"mean_difference", "sd"},
    "binomial_rates": {"p_control", "p_treatment"},
    "hazard_ratio": {"hazard_ratio", "events"},
    "exponential_survival": {"hazard_ratio", "control_median", "accrual", "follow_up"},
}
DROPOUT_KEYS = {"dropout", "dropout_time"}  # given together, or not at all
CRITERIA = ["optimal", "minimax"]
# What each observational design with fixed groups is planned at, and a search's keys.
GROUP_POINT_KEYS = {
    "cohort": ("risk_unexposed", "risk_exposed"),
    "case_control": ("exposure_controls", "exposure_cases"),
    "cross_sectional": ("prevalence_unexposed", "prevalence_exposed"),
}
TOTAL_LIMIT = 150  # participants when only the total is fixed
PAIRS_LIMIT, EVENTS_LIMIT = 400, 500  # exact power for McNemar's test and the rate test
GROUP_SEARCH_KEYS = {
    "cohort": ("min_exposed", "max_exposed", "unexposed_per_exposed"),
    "case_control": ("min_cases", "max_cases", "controls_per_case"),
}


def _favours(null: dict) -> str | None:
    """The direction a one-sided null favours the treatment in, from the registry's data."""
    entry = NULL_FORMS.get(null["predicate"])
    return entry[1].favours if entry else None


def _direction_ok(null: dict) -> bool:
    better, favours = null["model"].get("better"), _favours(null)
    return better is None or favours is None or favours == better


def _direction_facts(null: dict) -> dict:
    better = null["model"].get("better")
    return {"better": better} if better else {}


def _direction_assumed(null: dict) -> tuple:
    """A one-sided null on a model that does not say which direction is better."""
    favours = _favours(null)
    if favours is None or null["model"].get("better"):
        return ()
    return (HIGHER_IS_BETTER if favours == "higher" else LOWER_IS_BETTER,)


def _describe_design(measurements: int, clusters: tuple | None) -> str:
    """Worded independently of derivations.describe_design, and compared with it."""
    parts = [f"{measurements} measurements per participant"] if measurements > 1 else []
    if clusters:
        parts.append(f"{clusters[0]} and {clusters[1]} clusters randomised")
    return "; ".join(parts)


def _features(model: dict) -> list[str]:
    """Declared design features, read from the serialized model."""
    return [
        *(["repeated_measures"] if model.get("measurements", 1) > 1 else []),
        *(["clusters"] if "clusters_control" in model else []),
    ]


def _design_facts(name: str, model: dict, method: CitedMethod) -> tuple | None:
    """The declared-design step a method's contract needs, or None for a plain design."""
    features = _features(model)
    if not features:
        return None
    clusters = (
        (model["clusters_control"], model["clusters_treatment"])
        if "clusters_control" in model
        else None
    )
    ids = [item.id for item in method.assumptions]
    facts = {
        "subject": name,
        "design": _describe_design(model.get("measurements", 1), clusters),
        "features": features,
        "assumptions": ids,
    }
    holds = not any(set(ids) & set(CONTRADICTED_BY[feature]) for feature in features)
    return ("declared-design", facts, holds, ())


def _vouched(model: dict, method: CitedMethod) -> tuple:
    """What a declared test must do for the declared design, taken on the author's word."""
    if method.grade != "declared":
        return ()
    return tuple(ACCOUNTS_FOR[feature] for feature in _features(model))


def _whole(value, minimum: int) -> bool:
    return type(value) is int and value >= minimum


def _probability(text: str) -> bool:
    return 0 <= Fraction(text) <= 1


def _one_sample_expectations(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    n, rate = analysis["model"]["n"], analysis["null_rate"]
    steps = [
        ("sample-size-range", {"subject": name, "n": n}, _whole(n, 1) and n <= ONE_ARM_LIMIT),
        ("null-rate-interior", {"subject": name, "rate": rate}, 0 < Fraction(rate) < 1),
        (
            "level-range",
            {"subject": name, "alpha": analysis["alpha"]},
            _probability(analysis["alpha"]),
        ),
    ]

    if analysis["test"] == "binomial_score_test":
        cutoff = analysis["squared_cutoff"]
        steps.append(
            (
                "one-sample-score-cutoff",
                {"subject": name, "squared_cutoff": cutoff},
                Fraction(cutoff) > 0,
            )
        )
    return steps


def _rule_well_formed(rule: dict) -> bool:
    if rule["kind"] == "threshold":
        return _whole(rule["continue_above"], 0) and _whole(rule["reject_above"], 0)
    if rule["kind"] == "posterior":
        return (
            _whole(rule["prior_a"], 1)
            and _whole(rule["prior_b"], 1)
            and 0 < Fraction(rule["reference"]) < 1
            and _probability(rule["continue_at_least"])
            and _probability(rule["success_at_least"])
        )
    return False


def _two_stage_expectations(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    first, second = analysis["design"]["n_stage1"], analysis["design"]["n_stage2"]
    sizes_ok = all(_whole(size, 1) and size <= STAGE_LIMIT for size in (first, second))
    return [
        ("stage-sizes", {"subject": name, "n_stage1": first, "n_stage2": second}, sizes_ok),
        (
            "null-rate",
            {"subject": name, "rate": analysis["null_rate"]},
            _probability(analysis["null_rate"]),
        ),
        (
            "decision-rule",
            {"subject": name, "rule": analysis["rule"]},
            _rule_well_formed(analysis["rule"]),
        ),
    ]


def _search_valid(search: dict, arm_limit: int = PER_ARM_LIMIT) -> bool:
    if "max_per_arm" in search:
        ratio = (
            1 if search["allocation"] == "equal_arms" else int(search["allocation"].split(":")[1])
        )
        low, high = search["min_per_arm"], search["max_per_arm"]
        return (
            _whole(low, 1)
            and _whole(high, low)
            and 1 <= ratio <= RATIO_LIMIT
            and high * ratio <= arm_limit
        )
    if "max_n" in search:
        return (
            _whole(search["min_n"], 1)
            and _whole(search["max_n"], search["min_n"])
            and (search["max_n"] <= ONE_ARM_LIMIT)
        )
    return (
        _whole(search["max_total"], 2)
        and search["max_total"] <= SEARCH_LIMIT
        and search["criterion"] in CRITERIA
        and 0 < Fraction(search["null_rate"]) < 1
    )


def _cluster_search_valid(search: dict, fewest: int) -> bool:
    """Clusters per arm of a fixed size, from the method's fewest; or the declared clusters
    with a range of sizes."""
    if "cluster_size" in search:
        low, high = search["min_clusters_per_arm"], search["max_clusters_per_arm"]
        return (
            set(search) == {"cluster_size", "min_clusters_per_arm", "max_clusters_per_arm"}
            and _whole(search["cluster_size"], 1)
            and search["cluster_size"] <= CLUSTER_SIZE_LIMIT
            and _whole(low, fewest)
            and _whole(high, low)
            and high <= CLUSTER_LIMIT
        )
    low, high = search["min_cluster_size"], search["max_cluster_size"]
    return (
        set(search) == {"min_cluster_size", "max_cluster_size"}
        and _whole(low, 1)
        and _whole(high, low)
        and high <= CLUSTER_SIZE_LIMIT
    )


# The contract rule and assumptions for each kind of analysis, keyed by its test.
BLOCKS = {
    "fisher": ("analysis-contract", ANALYSIS_ASSUMPTIONS),
    "farrington_manning": ("analysis-contract", ANALYSIS_ASSUMPTIONS),
    "pearson_test": ("analysis-contract", ANALYSIS_ASSUMPTIONS),
    "likelihood_ratio_test": ("analysis-contract", ANALYSIS_ASSUMPTIONS),
    **{test: ("analysis-contract", ANALYSIS_ASSUMPTIONS) for test in PROPORTION_Z_CONTRACT_IDS},
    "binomial_exact_one_sided": ("one-sample-contract", ONE_SAMPLE_ASSUMPTIONS),
    "binomial_score_test": ("one-sample-contract", ONE_SAMPLE_ASSUMPTIONS),
    "two_stage": ("two-stage-contract", TWO_STAGE_ASSUMPTIONS),
}


def _premises(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    if analysis["test"] == "fisher":
        return _analysis_expectations(name, analysis)
    if analysis["test"] == "likelihood_ratio_test":
        model, null = analysis["design"]["model"], analysis["null"]
        cutoff = analysis["ratio_cutoff"]
        return [
            *_analysis_expectations(name, analysis),
            (
                "likelihood-ratio-cutoff",
                {"subject": name, "ratio_cutoff": cutoff},
                model == null["model"]
                and model["module"] == "two_arm_binomial"
                and min(model["n_control"], model["n_treatment"]) > 0
                and Fraction(cutoff) > 1,
            ),
        ]
    if analysis["test"] == "pearson_test":
        model, null = analysis["design"]["model"], analysis["null"]
        cutoff, correction = analysis["squared_cutoff"], analysis["correction"]
        return [
            *_analysis_expectations(name, analysis),
            (
                "pearson-cutoff",
                {"subject": name, "squared_cutoff": cutoff, "correction": correction},
                model == null["model"]
                and model["module"] == "two_arm_binomial"
                and min(model["n_control"], model["n_treatment"]) > 0
                and Fraction(cutoff) > 0
                and correction in ("none", "yates"),
            ),
        ]
    if analysis["test"] == "farrington_manning":
        model, null = analysis["design"]["model"], analysis["null"]
        margin, cutoff = null["value"], analysis["squared_cutoff"]
        return [
            *_analysis_expectations(name, {**analysis, "alternative": "margin"}),
            (
                "farrington-manning-cutoff",
                {"subject": name, "margin": margin, "squared_cutoff": cutoff},
                model == null["model"]
                and model["module"] == "two_arm_binomial"
                and min(model["n_control"], model["n_treatment"]) > 0
                and -1 < Fraction(margin) < 0
                and Fraction(cutoff) > 0,
            ),
        ]
    if analysis["test"] in PROPORTION_Z_CONTRACT_IDS:
        model, null = analysis["design"]["model"], analysis["null"]
        n, cutoff = model["n_control"], analysis["squared_cutoff"]
        valid = (
            model == null["model"]
            and model["module"] == "two_arm_binomial"
            and 0 < n == model["n_treatment"]
            and Fraction(cutoff) > 0
        )
        return [
            *_analysis_expectations(name, analysis),
            (
                f"{analysis['test'].removesuffix('_test')}-design",
                {"subject": name, "n": n, "squared_cutoff": cutoff},
                valid,
            ),
        ]
    if analysis["test"] in ("binomial_exact_one_sided", "binomial_score_test"):
        return _one_sample_expectations(name, analysis)
    if analysis["test"] == "two_stage":
        return _two_stage_expectations(name, analysis)
    raise ValueError(f"unknown analysis {analysis['test']!r}")


def _block(name: str, analysis: dict, start: int = 0) -> list[tuple]:
    """The premises of an analysis followed by its contract rule."""
    steps = [(rule, facts, holds, ()) for rule, facts, holds in _premises(name, analysis)]
    uses = tuple(range(start, start + len(steps)))
    steps.append((BLOCKS[analysis["test"]][0], {"subject": name}, True, uses))
    return steps


SCENARIO_KEYS = {"sd_treatment", "skewness"}


def _point_valid(
    point: dict, kind: str, total: int, clustered: bool = False, scenario: bool = False
) -> bool:
    """A test of cluster summaries is planned with the intracluster correlation too; a
    two-sample t-test may give a scenario for simulation."""
    if scenario and kind == "mean_difference" and SCENARIO_KEYS & set(point):
        if "sd_treatment" in point and Fraction(point["sd_treatment"]) <= 0:
            return False
        if "skewness" in point and abs(Fraction(point["skewness"])) > 4:
            return False
        point = {key: value for key, value in point.items() if key not in SCENARIO_KEYS}
    if kind == "exponential_survival" and "effect_delay" in point:
        if Fraction(point["effect_delay"]) < 0:
            return False
        point = {key: value for key, value in point.items() if key != "effect_delay"}
    if kind == "exponential_survival" and set(point) == POINT_KEYS[kind] | DROPOUT_KEYS:
        if not (0 <= Fraction(point["dropout"]) < 1 and Fraction(point["dropout_time"]) > 0):
            return False
        point = {key: value for key, value in point.items() if key not in DROPOUT_KEYS}
    if clustered and "cluster_size_cv" in point:
        if not 0 <= Fraction(point["cluster_size_cv"]) <= 3:
            return False
        point = {key: value for key, value in point.items() if key != "cluster_size_cv"}
    if set(point) != POINT_KEYS[kind] | ({"icc"} if clustered else set()):
        return False
    if clustered and not 0 <= Fraction(point["icc"]) < 1:
        return False
    if kind == "exponential_survival":
        accrual, follow_up = Fraction(point["accrual"]), Fraction(point["follow_up"])
        return (
            Fraction(point["hazard_ratio"]) > 0
            and Fraction(point["control_median"]) > 0
            and accrual >= 0
            and follow_up >= 0
            and accrual + follow_up > 0
        )
    if kind == "mean_difference":
        return Fraction(point["sd"]) > 0
    if kind == "binomial_rates":
        return _probability(point["p_control"]) and _probability(point["p_treatment"])
    return (
        Fraction(point["hazard_ratio"]) > 0
        and _whole(point["events"], 1)
        and (point["events"] <= total)
    )


# The arguments of each kind of point a cited observational test is planned at, the ones
# that may be left out, and the exposure scale its formula needs.
ASSOCIATION_POINT_KEYS = {
    "correlation": ({"correlation"}, {"skewness", "exposure_skewness"}, "continuous"),
    "slope": (
        {"slope", "exposure_sd", "residual_sd"},
        {"exposure_r2", "skewness", "exposure_skewness"},
        "continuous",
    ),
    "odds_per_sd": ({"odds_ratio_per_sd", "baseline"}, {"exposure_r2"}, "continuous"),
    "outcome_means": ({"mean_unexposed", "mean_exposed", "sd"}, {"exposed_share"}, "binary"),
    "discordant_pairs": ({"discordant", "odds_ratio"}, set(), "binary"),
    "incidence_rates": ({"rate_ratio", "exposed_time", "unexposed_time"}, {"events"}, "binary"),
    "association_groups": (None, None, "binary"),  # the design's own point; see below
}
CITED_TOTAL_LIMIT = 100_000


def _groups_point(point: dict, study: dict) -> tuple[bool, Fraction]:
    """A design's own two-group point: whether it is valid, and the gap between the groups."""
    keys = GROUP_POINT_KEYS.get(study["study"])
    if keys is None:
        return False, Fraction(0)
    wanted = {*keys, "exposed_share"} if "n" in study else set(keys)
    if set(point) != wanted or not all(_probability(point[key]) for key in keys):
        return False, Fraction(0)
    if "n" in study and not 0 < Fraction(point["exposed_share"]) < 1:
        return False, Fraction(0)
    return True, Fraction(point[keys[1]]) - Fraction(point[keys[0]])


def _association_point_valid(point: dict, kind: str, study: dict, search) -> tuple[bool, Fraction]:
    """Whether a cited observational test's point is valid, and its distance from the null."""
    if kind == "association_groups":
        return _groups_point(point, study)
    required, optional, _ = ASSOCIATION_POINT_KEYS[kind]
    if not required <= set(point) <= required | optional:
        return False, Fraction(0)
    # Skewness, for simulation, lies within the gamma shapes the engine draws.
    if any(abs(Fraction(point.get(name, "0"))) > 4 for name in ("skewness", "exposure_skewness")):
        return False, Fraction(0)
    if kind == "correlation":
        rho = Fraction(point["correlation"])
        return -1 < rho < 1, rho
    if kind == "slope":
        valid = (
            Fraction(point["exposure_sd"]) > 0
            and Fraction(point["residual_sd"]) > 0
            and 0 <= Fraction(point.get("exposure_r2", "0")) < 1
        )
        return valid, Fraction(point["slope"])
    if kind == "outcome_means":
        share = point.get("exposed_share")
        valid = (
            Fraction(point["sd"]) > 0
            and ((share is not None) == ("n" in study))
            and (share is None or 0 < Fraction(share) < 1)
        )
        return valid, Fraction(point["mean_exposed"]) - Fraction(point["mean_unexposed"])
    if kind == "odds_per_sd":
        ratio = Fraction(point["odds_ratio_per_sd"])
        valid = (
            ratio > 0
            and 0 < Fraction(point["baseline"]) < 1
            and 0 <= Fraction(point.get("exposure_r2", "0")) < 1
        )
        return valid, ratio - 1
    if kind == "discordant_pairs":
        ratio = Fraction(point["odds_ratio"])
        return 0 < Fraction(point["discordant"]) <= 1 and ratio > 0, ratio - 1
    ratio = Fraction(point["rate_ratio"])
    valid = (
        ratio > 0
        and Fraction(point["exposed_time"]) > 0
        and Fraction(point["unexposed_time"]) > 0
        # Power is given the events: the point gives them, unless a search varies them.
        and (("events" in point) == (search is None))
        and (search is not None or _whole(point["events"], 1))
    )
    return valid, ratio - 1


def _point_kind(point: dict) -> str:
    """The kind of point, told apart by its arguments."""
    for kind, (required, _, _) in ASSOCIATION_POINT_KEYS.items():
        if required is not None and required <= set(point):
            return kind
    return "association_groups"


PRECISION_DESIGNS = {"one_arm_binomial": "one_arm", "two_arm_binomial": "two_arm"}


def _precision_value(kind: str, point: dict, design: str) -> Fraction | None:
    """The measure at the planning point, for a relative margin; None if the point is
    malformed."""
    if kind == "proportion":
        return Fraction(point.get("proportion", point.get("response_rate", "0")))
    if kind in ("matched", "rate"):
        return Fraction(point["odds_ratio" if kind == "matched" else "rate_ratio"])
    keys = ("p_control", "p_treatment") if design == "two_arm" else GROUP_POINT_KEYS.get(design)
    if keys is None or not set(keys) <= set(point):
        return None
    first, second = Fraction(point[keys[0]]), Fraction(point[keys[1]])
    if kind == "difference":
        return second - first
    if kind == "ratio":
        return second / first if first else None
    if 0 < first < 1 and 0 < second < 1:
        return (second / (1 - second)) / (first / (1 - first))
    return None


def _precision_point_valid(kind, point, design, model, method, search) -> bool:
    """The planning point fits the measure and the method, as the compiler requires."""
    extras = {"design_effect", "population_size"}
    core = {key: value for key, value in point.items() if key not in extras}
    survey = model.get("survey", "simple_random") != "simple_random"
    effect, population = point.get("design_effect"), point.get("population_size")
    if method == "exact" and (effect is not None or population is not None):
        return False
    if survey and effect is None:
        return False
    if effect is not None and Fraction(effect) <= 0:
        return False
    if population is not None and (
        kind != "proportion"
        or not _whole(population, 2)
        or (search is None and "n" in model and population <= model["n"])
    ):
        return False
    if kind == "proportion":
        keys = {"proportion"} if design != "one_arm" else ({"proportion"}, {"response_rate"})
        allowed = keys if isinstance(keys, tuple) else (keys,)
        return (
            any(set(core) == wanted for wanted in allowed)
            and 0 < _precision_value(kind, core, design) < 1
        )
    if kind == "matched":
        return (
            set(core) == {"discordant", "odds_ratio"}
            and 0 < Fraction(core["discordant"]) <= 1
            and Fraction(core["odds_ratio"]) > 0
        )
    if kind == "rate":
        wanted = {"rate_ratio", "exposed_time", "unexposed_time"} | (
            set() if search else {"events"}
        )
        return set(core) == wanted and all(
            Fraction(core[key]) > 0 for key in ("rate_ratio", "exposed_time", "unexposed_time")
        )
    if design == "two_arm":
        keys = ("p_control", "p_treatment")
        if set(core) != set(keys):
            return False
    else:
        keys = GROUP_POINT_KEYS.get(design)
        wanted = (
            None if keys is None else set(keys) | ({"exposed_share"} if "n" in model else set())
        )
        if wanted is None or set(core) != wanted:
            return False
        if "n" in model and not 0 < Fraction(core["exposed_share"]) < 1:
            return False
    first, second = (Fraction(core[key]) for key in keys)
    if not (_probability(core[keys[0]]) and _probability(core[keys[1]])):
        return False
    if kind == "ratio":
        return first > 0 and second > 0
    if kind == "odds":
        return 0 < first < 1 and 0 < second < 1
    return True


def _precision_expected(name: str, subject: dict, search):
    """A precision claim, re-evaluated from the planned interval and the target."""
    interval = subject["analysis"] if search is None else search["interval"]
    target, model = subject["target"], interval["model"]
    measure, method, group = interval["interval"], interval["method"], interval.get("group")
    design = model.get("study") or PRECISION_DESIGNS.get(model.get("module"), "")
    kind, designs = PRECISION_MEASURES.get(measure, (None, ()))
    observational = "study" in model
    scales_ok = not observational or (
        model.get("outcome_scale", "binary") == "binary"
        and (kind == "proportion" or model.get("exposure_scale", "binary") == "binary")
    )
    needs_group = kind == "proportion" and design == "cohort" and "n" not in model
    fits = (
        design in designs
        and method in PRECISION_METHODS
        and scales_ok
        and (method == "normal" or model.get("survey", "simple_random") == "simple_random")
        and (group in ("exposed", "unexposed") if needs_group else group is None)
        and not (design == "two_arm" and _features(model))
    )
    spaced = measure.replace("_", " ")
    shown = model.get("study", model.get("module", "")).replace("_", "-")
    steps = [
        (
            "interval-fits",
            {
                "subject": name,
                "measure": spaced,
                "method": method,
                "design": shown,
                "interval": interval,
            },
            fits,
            (),
        )
    ]
    point = target["at"]
    point_ok = fits and _precision_point_valid(kind, point, design, model, method, search)
    steps.append(
        ("precision-point", {"subject": name, "measure": spaced, "point": point}, point_ok, ())
    )
    margins = [key for key in ("margin_of_error", "relative_margin_of_error") if key in target]
    value = _precision_value(kind, point, design) if point_ok else None
    target_ok = (
        len(margins) == 1
        and Fraction(target[margins[0]]) > 0
        and 0 < Fraction(target["level"]) < 1
        and ("assurance" not in target or 0 < Fraction(target["assurance"]) < 1)
    )
    if target_ok and margins[0] == "relative_margin_of_error":
        relative = Fraction(target["relative_margin_of_error"])
        if kind in ("proportion", "difference"):
            target_ok = value is not None and value != 0
        else:
            target_ok = relative < 1
    steps.append(("precision-target", {"subject": name, "target": target}, target_ok, ()))
    used = [0, 1, 2]
    if search is not None:
        bounds = {key: value for key, value in search.items() if key != "interval"}
        two_groups = design == "two_arm" or (
            observational
            and "n" not in model
            and kind in ("difference", "ratio", "odds")
            and design in ("cohort", "case_control")
        )
        ratio = bounds.get("ratio")
        limit = PRECISION_PAIRS if method == "exact" and kind == "matched" else PRECISION_LIMIT
        holds = (
            set(bounds) == {"min_size", "max_size", "ratio"}
            and _whole(bounds["min_size"], 1)
            and _whole(bounds["max_size"], bounds["min_size"])
            and _whole(ratio, 1)
            and ratio <= RATIO_LIMIT
            and (two_groups or ratio == 1)
            and bounds["max_size"] * ((1 + ratio) if two_groups else 1) <= limit
            and not ("assurance" in target and subject.get("claim") == "smallest_in_range")
        )
        steps.append(("search-range", {"subject": name, "search": bounds}, holds, ()))
        used.append(3)
    steps.append(("precision-contract", {"subject": name}, True, tuple(used)))
    total_only = (
        "assurance" in target
        and observational
        and "n" in model
        and kind in ("difference", "ratio", "odds")
    )
    listed = PRECISION_EXACT if method == "exact" else PRECISION_NORMAL
    return steps, [], (*listed, *((PRECISION_GROUPS,) if total_only else ()), PRECISION_POINT)


def _cited_association_search_valid(bounds: dict, kind: str, study: dict, covariates: int) -> bool:
    if "min_n" in bounds:
        low, high = bounds["min_n"], bounds["max_n"]
        fewest = covariates + 3
        return (
            set(bounds) == {"min_n", "max_n"}
            and "n" in study
            and _whole(low, fewest)
            and _whole(high, low)
            and high <= CITED_TOTAL_LIMIT
        )
    if study["study"] in GROUP_SEARCH_KEYS and "n" not in study:
        low_key, high_key, ratio_key = GROUP_SEARCH_KEYS[study["study"]]
        if set(bounds) != {low_key, high_key, ratio_key}:
            return False
        low, high, ratio = bounds[low_key], bounds[high_key], bounds[ratio_key]
        return (
            _whole(low, 1)
            and _whole(high, low)
            and _whole(ratio, 1)
            and ratio <= RATIO_LIMIT
            and high * (1 + ratio) <= CITED_TOTAL_LIMIT
        )
    unit = "pairs" if study["study"] == "matched_case_control" else "events"
    low, high = bounds.get(f"min_{unit}"), bounds.get(f"max_{unit}")
    return (
        set(bounds) == {f"min_{unit}", f"max_{unit}"}
        and _whole(low, 1)
        and _whole(high, low)
        and high <= CITED_TOTAL_LIMIT
    )


def _cited_association_planning_expected(name: str, subject: dict, search, analysis: dict):
    """Power of a cited observational test, from its formula in the method registry."""
    method = OBSERVATIONAL_METHODS[analysis["test"]]
    target, point = subject["target"], subject["target"]["at"]
    study = analysis["design"]["model"]
    kind = _point_kind(point)
    scale = study.get("exposure_scale", "binary")
    # The formula at this kind of point, for the study's exposure scale.
    formula = next(
        (
            f
            for f in method.formulas
            if f.point == kind and ASSOCIATION_POINT_KEYS[kind][2] == scale
        ),
        None,
    )
    if formula is None:
        raise ValueError("the method has no power formula at this point")
    inner = f"{name}.analysis"
    steps, test_assumptions = _cited_association_expected(
        inner, analysis, f"{method.module}/{method.key}"
    )
    used = [len(steps) - 1]
    covariates = len(analysis.get("adjusted_for", []))
    facts = {
        "subject": name,
        "method": method.key,
        "formula": formula.key,
        "version": formula.version,
        "point": point,
    }
    # A survey test of a complex sample takes the design effect; no other test does.
    survey = method.module == "tests.survey"
    effect_given = "design_effect" in point
    design_ok = (not effect_given or (survey and Fraction(point["design_effect"]) > 0)) and (
        effect_given or not survey or study.get("survey", "simple_random") == "simple_random"
    )
    bare = {key: value for key, value in point.items() if key != "design_effect"}
    valid, effect = _association_point_valid(bare, kind, study, search)
    valid = valid and design_ok
    if kind in ("correlation", "slope", "outcome_means") and search is None and not survey:
        total = study.get("n") or study.get("exposed", 0) + study.get("unexposed", 0)
        valid = valid and total - covariates - 2 >= 1
    if method.key == "modified_poisson" and kind == "association_groups":
        keys = GROUP_POINT_KEYS.get(study["study"], ())
        valid = valid and all(Fraction(point[key]) > 0 for key in keys if key in point)
    steps.append(("power-formula", facts, valid, ()))
    statement = steps[1][1]["statement"]
    steps.append(
        ("alternative", {"subject": name, "point": point, "null": statement}, effect != 0, ())
    )
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used += [len(steps) - 3, len(steps) - 2, len(steps) - 1]
    if search is not None:
        bounds = {key: value for key, value in search.items() if key != "analysis"}
        holds = _cited_association_search_valid(bounds, kind, study, covariates)
        steps.append(("search-range", {"subject": name, "search": bounds}, holds, ()))
        used.append(len(steps) - 1)
    steps.append(("cited-planning-contract", {"subject": name}, True, tuple(used)))
    obligations = [
        (
            "cited-error-budget",
            {"subject": name, "alpha": analysis["alpha"], "maximum_typeI": maximum},
            Fraction(analysis["alpha"]) <= Fraction(maximum),
        ),
        _sampling_expectation(inner, analysis),
    ]
    assumptions = (
        *test_assumptions,
        *(item.text for item in formula.assumptions),
        PLANNING_POINT_ASSUMPTION,
    )
    return steps, obligations, assumptions


FAMILY_METHODS = ("bonferroni", "fixed_sequence", "graphical")


def _endpoint_kind(analysis: dict) -> str | None:
    """A member simulated in a family: Fisher's test, or a t-test."""
    if analysis.get("test") == "fisher" and analysis.get("alternative", "two_sided") in (
        "two_sided",
        "greater",
    ):
        return "binary"
    method = METHODS.get(analysis.get("test"))
    if method is not None and method.module == "tests.t":
        return "measured"
    return None


def _endpoint_outside(analysis: dict, kind: str, point: dict) -> bool:
    if kind == "binary":
        control, treatment = Fraction(point["p_control"]), Fraction(point["p_treatment"])
        if analysis.get("alternative") == "greater":
            return treatment > control
        return treatment != control
    null = analysis["null"]
    effect, margin = Fraction(point["mean_difference"]), Fraction(null.get("value", "0"))
    return {"higher": effect > margin, "lower": effect < margin, None: effect != margin}[
        _favours(null)
    ]


def _family_planning_expected(name: str, subject: dict, search, family: dict):
    """Simulated power of a family: the family's own steps, then one point per member."""
    if search is not None:
        raise ValueError("a family is simulated as declared, not searched")
    inner = f"{name}.analysis"
    if "joint_law" in family:
        steps, obligations = _fisher_family_expected(inner, family)
        texts = FAMILY_ASSUMPTIONS
    else:
        block = _combination(inner, family, 0)
        steps, obligations = list(block["steps"]), list(block["obligations"])
        texts = (*block["own"], *block["nested"], *block["cited"])
    used = [len(steps) - 1]
    members = [(item["name"], item["analysis"]) for item in family["analyses"]]
    target = subject["target"]
    point = target["at"]
    points = point.get("endpoints") or []
    correlation = Fraction(point.get("correlation", "-1"))
    kinds = [_endpoint_kind(analysis) for _, analysis in members]
    wanted = {"binary": {"p_control", "p_treatment"}, "measured": {"mean_difference", "sd"}}
    shaped = (
        len(points) == len(members)
        and None not in kinds
        and all(set(p) == wanted[k] for p, k in zip(points, kinds, strict=False))
    )
    valid = (
        shaped
        and all(
            _probability(p["p_control"]) and _probability(p["p_treatment"])
            if k == "binary"
            else Fraction(p["sd"]) > 0
            for p, k in zip(points, kinds, strict=True)
        )
        and 0 <= correlation < 1
    )
    if valid and correlation > 0:
        sizes = {
            (a["design"]["model"]["n_control"], a["design"]["model"]["n_treatment"])
            for _, a in members
        }
        valid = len(sizes) == 1
    if valid:
        valid = any(
            _endpoint_outside(a, k, p) for (_, a), k, p in zip(members, kinds, points, strict=True)
        )
    steps.append(
        (
            "endpoint-points",
            {
                "subject": name,
                "members": [member for member, _ in members],
                "points": points,
                "correlation": point.get("correlation"),
            },
            valid,
            (),
        )
    )
    rejecting = target.get("rejecting")
    steps.append(
        ("family-power", {"subject": name, "rejecting": rejecting}, rejecting in ("any", "all"), ())
    )
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used += [len(steps) - 3, len(steps) - 2, len(steps) - 1]
    steps.append(("family-planning-contract", {"subject": name}, True, tuple(used)))
    obligations.append(
        (
            "cited-error-budget",
            {"subject": name, "alpha": family["alpha"], "maximum_typeI": maximum},
            Fraction(family["alpha"]) <= Fraction(maximum),
        )
    )
    assumptions = (
        *texts,
        *(item.text for item in FAMILY.assumptions),
        PLANNING_POINT_ASSUMPTION,
    )
    return steps, obligations, assumptions


REESTIMATED_TESTS = ("t_test", "t_test_one_sided")
PLAIN_MEAN_DIFFERENCE = {"mean_difference", "sd"}


def _reestimation_planning_expected(name: str, subject: dict, search, design: dict):
    """Simulated power and Type I error of a re-estimated design: its t-test's contract, the
    rule's bounds, the model's point, and nulls that each lie on the null."""
    if search is not None:
        raise ValueError("a re-estimated design chooses its own size; it is not searched")
    analysis = design["analysis"]
    method = _method(analysis)
    if method is None or method.key not in REESTIMATED_TESTS or method.simulation is None:
        raise ValueError("blinded re-estimation is simulated for Student's t-test only")
    model = method.simulation
    if model.reestimation is None:
        raise ValueError("the test's simulation model does not re-estimate sizes")
    inner = f"{name}.analysis"
    steps, _, test_assumptions, _ = _cited_expected(
        inner, analysis, f"{method.module}/{method.key}"
    )
    used = [len(steps) - 1]
    sizes = analysis["design"]["model"]
    initial = sizes["n_control"]
    interim, largest = design["interim_per_arm"], design["max_per_arm"]
    rule = {
        "subject": name,
        "interim_per_arm": interim,
        "initial_per_arm": initial,
        "max_per_arm": largest,
        "difference": design["difference"],
        "power": design["power"],
    }
    rule_valid = (
        sizes["n_treatment"] == initial
        and _whole(interim, 2)
        and interim < initial
        and _whole(largest, initial)
        and largest <= CITED_ARM_LIMIT
        and Fraction(design["difference"]) != 0
        and 0 < Fraction(design["power"]) < 1
    )
    steps.append(("reestimation-rule", rule, rule_valid, ()))
    target, point = subject["target"], subject["target"]["at"]
    facts = {
        "subject": name,
        "method": method.key,
        "model": model.key,
        "version": model.version,
        "point": point,
    }
    plain = set(point) == PLAIN_MEAN_DIFFERENCE and Fraction(point["sd"]) > 0
    steps.append(("simulation-model", facts, plain, ()))
    null = analysis["null"]
    statement = _null_statement(null)
    margin = Fraction(null.get("value", "0"))
    nulls = target.get("nulls") or []
    on_null = 1 <= len(nulls) <= 20 and all(
        set(item) == PLAIN_MEAN_DIFFERENCE
        and Fraction(item["sd"]) > 0
        and Fraction(item["mean_difference"]) == margin
        for item in nulls
    )
    steps.append(
        (
            "null-scenarios",
            {"subject": name, "count": len(nulls), "nulls": nulls, "null": statement},
            on_null,
            (),
        )
    )
    effect = Fraction(point["mean_difference"])
    outside = {"higher": effect > margin, "lower": effect < margin, None: effect != margin}[
        _favours(null)
    ]
    steps.append(("alternative", {"subject": name, "point": point, "null": statement}, outside, ()))
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used += [len(steps) - 5, len(steps) - 4, len(steps) - 3, len(steps) - 2, len(steps) - 1]
    steps.append(("adaptive-planning-contract", {"subject": name}, True, tuple(used)))
    obligations = [_sampling_expectation(inner, analysis)]
    assumptions = (
        *test_assumptions,
        *(item.text for item in model.assumptions),
        REESTIMATION_TYPE_I.text,
        PLANNING_POINT_ASSUMPTION,
    )
    return steps, obligations, assumptions


def _sequential_planning_expected(name: str, subject: dict, search, design: dict):
    """Simulated power of a design with looks: its looks form one sequential test, re-derived
    as for typeI(...), and their test has a simulation model for looks at this point."""
    if search is not None and set(search) != {
        "analysis",
        "min_per_arm",
        "max_per_arm",
        "step",
        "criterion",
    }:
        raise ValueError("a search over looks lists its grid and criterion")
    inner = f"{name}.analysis"
    block = _combination(inner, design, 0, nested=True)
    steps = list(block["steps"])
    used = [len(steps) - 1]
    final = design["analyses"][-1]["analysis"]
    target, point = subject["target"], subject["target"]["at"]
    sizes = _sizes(final["design"]["model"])
    if final.get("test") == "fisher":
        # Fisher's test at looks: its power is summed exactly; no simulation model.
        model = None
        valid = (
            set(point) == {"p_control", "p_treatment"}
            and _probability(point["p_control"])
            and _probability(point["p_treatment"])
            and max(sizes.values()) <= MAX_LOOK_ARM
        )
        steps.append(("exact-looks", {"subject": name, "point": point}, valid, ()))
        alternative = final.get("alternative", "two_sided")
        control, treatment = (
            Fraction(point.get("p_control", "0")),
            Fraction(point.get("p_treatment", "0")),
        )
        outside = treatment > control if alternative == "greater" else treatment != control
        statement = _statement(final["null"])
    else:
        method = _method(final)
        if method is None or method.simulation is None or method.simulation.looks is None:
            raise ValueError("the looks' test has no simulation model for looks")
        model = method.simulation
        facts = {
            "subject": name,
            "method": method.key,
            "model": model.key,
            "version": model.version,
            "point": point,
        }
        valid = _point_valid(point, model.point, sum(sizes.values()), False, True)
        steps.append(("simulation-model", facts, valid, ()))
        null = final["null"]
        margin = Fraction(null.get("value", "0"))
        effect = Fraction(point.get("mean_difference", "0"))
        outside = {"higher": effect > margin, "lower": effect < margin, None: effect != 0}[
            _favours(null)
        ]
        statement = _null_statement(null)
    steps.append(("alternative", {"subject": name, "point": point, "null": statement}, outside, ()))
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used += [len(steps) - 3, len(steps) - 2, len(steps) - 1]
    if search is not None:
        looks = len(design["analyses"])
        low, high, step = search["min_per_arm"], search["max_per_arm"], search["step"]
        allocation = Fraction(sizes["n_treatment"], sizes["n_control"])
        whole = all(isinstance(v, int) and v >= 1 for v in (low, high, step)) and low <= high
        listed = comb(len(range(low, high + 1, step)), looks) if whole else 0
        valid = (
            whole
            and allocation.denominator == 1
            and search["criterion"] in ("minimax", "optimal")
            and 1 <= listed <= MAX_LOOK_CANDIDATES
        )
        facts = {
            "subject": name,
            "looks": looks,
            "min_per_arm": low,
            "max_per_arm": high,
            "step": step,
            "allocation": allocation.numerator if allocation.denominator == 1 else None,
            "criterion": search["criterion"],
            "candidates": listed,
        }
        steps.append(("look-candidates", facts, valid, ()))
        used.append(len(steps) - 1)
    steps.append(("sequential-planning-contract", {"subject": name}, True, tuple(used)))
    obligations = [
        *block["obligations"],
        (
            "cited-error-budget",
            {"subject": name, "alpha": design["alpha"], "maximum_typeI": maximum},
            Fraction(design["alpha"]) <= Fraction(maximum),
        ),
    ]
    assumptions = (
        *block["own"],
        *block["nested"],
        *block["cited"],
        *((EXACT_LOOKS,) if model is None else (item.text for item in model.assumptions)),
        PLANNING_POINT_ASSUMPTION,
    )
    return steps, obligations, assumptions


def _cited_planning_expected(name: str, subject: dict, search, analysis: dict):
    """Approximate power for a cited test. The registry's formula is data, like its methods."""
    method = METHODS[analysis["test"]]
    point = subject["target"]["at"]
    # The formula whose kind of point this is, told apart by the point's arguments.
    formula = next((f for f in method.formulas if POINT_KEYS[f.point] <= set(point)), None)
    if formula is None:
        raise ValueError("the method has no power formula at this point")
    inner = f"{name}.analysis"
    steps, _, test_assumptions, _ = _cited_expected(
        inner, analysis, f"{method.module}/{method.key}"
    )
    used = [len(steps) - 1]
    target, point = subject["target"], subject["target"]["at"]
    sizes = _sizes(analysis["design"]["model"])
    facts = {
        "subject": name,
        "method": method.key,
        "formula": formula.key,
        "version": formula.version,
        "point": point,
    }
    clustered = method.unit == "cluster"
    steps.append(
        (
            "power-formula",
            facts,
            _point_valid(
                point, formula.point, sum(sizes.values()), clustered, method.module == "tests.t"
            ),
            (),
        )
    )
    null = analysis["null"]
    margin = Fraction(null.get("value", "0"))
    if formula.point == "mean_difference":
        effect = Fraction(point["mean_difference"])
    elif formula.point == "binomial_rates":
        effect = Fraction(point["p_treatment"]) - Fraction(point["p_control"])
    else:
        effect = Fraction(point["hazard_ratio"]) - 1
    outside = {"higher": effect > margin, "lower": effect < margin, None: effect != 0}[
        _favours(null)
    ]
    statement = _null_statement(null)
    steps.append(("alternative", {"subject": name, "point": point, "null": statement}, outside, ()))
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used += [len(steps) - 3, len(steps) - 2, len(steps) - 1]
    if search is not None:
        bounds = {key: value for key, value in search.items() if key != "analysis"}
        steps.append(
            (
                "search-range",
                {"subject": name, "search": bounds},
                (
                    _cluster_search_valid(bounds, method.min_per_arm)
                    if clustered
                    else _search_valid(bounds, CITED_ARM_LIMIT)
                )
                and formula.point != "hazard_ratio",
                (),
            )
        )
        used.append(len(steps) - 1)
    steps.append(("cited-planning-contract", {"subject": name}, True, tuple(used)))
    obligations = [
        (
            "cited-error-budget",
            {"subject": name, "alpha": analysis["alpha"], "maximum_typeI": maximum},
            Fraction(analysis["alpha"]) <= Fraction(maximum),
        ),
        _sampling_expectation(inner, analysis),
    ]
    assumptions = (
        *test_assumptions,
        *(item.text for item in formula.assumptions),
        PLANNING_POINT_ASSUMPTION,
    )
    return steps, obligations, assumptions


def _group_search_valid(bounds: dict, kind: str) -> bool:
    low_key, high_key, ratio_key = GROUP_SEARCH_KEYS[kind]
    if set(bounds) != {low_key, high_key, ratio_key}:
        return False
    low, high, ratio = bounds[low_key], bounds[high_key], bounds[ratio_key]
    return (
        _whole(low, 1)
        and _whole(high, low)
        and _whole(ratio, 1)
        and ratio <= RATIO_LIMIT
        and high * ratio <= PER_ARM_LIMIT
    )


def _count_point(test: str, point: dict, search, study: dict) -> tuple[bool, bool]:
    """Whether a McNemar or rate-test point is valid, and whether it lies outside the null."""
    if test == "mcnemar":
        valid = (
            set(point) == {"discordant", "odds_ratio"}
            and 0 < Fraction(point["discordant"]) <= 1
            and Fraction(point["odds_ratio"]) > 0
            and (search is not None or study["pairs"] <= PAIRS_LIMIT)
        )
        return valid, valid and Fraction(point["odds_ratio"]) != 1
    keys = {"rate_ratio", "exposed_time", "unexposed_time"}
    valid = (
        set(point) == (keys if search is not None else keys | {"events"})
        and all(Fraction(point[key]) > 0 for key in keys)
        and (search is not None or (_whole(point["events"], 1) and point["events"] <= EVENTS_LIMIT))
    )
    return valid, valid and Fraction(point["rate_ratio"]) != 1


def _count_search_valid(bounds: dict, unit: str, limit: int) -> bool:
    low_key, high_key = f"min_{unit}", f"max_{unit}"
    return (
        set(bounds) == {low_key, high_key}
        and _whole(bounds[low_key], 1)
        and _whole(bounds[high_key], bounds[low_key])
        and bounds[high_key] <= limit
    )


def _association_planning_expected(name: str, subject: dict, search, analysis: dict):
    """Exact power of a proved observational test, from the serialized claim."""
    target, inner = subject["target"], f"{name}.analysis"
    test = analysis["test"]
    study, point = analysis["design"]["model"], target["at"]
    if test != "fisher_exact":
        if test == "mcnemar":
            steps = _matched_expected(inner, analysis)
            assumptions = (
                PAIRS_SAMPLED,
                WITHIN_PAIRS,
                SOURCE_POPULATION,
                PRESPECIFIED,
                MATCHED_NULL,
            )
            unit, limit = "pairs", PAIRS_LIMIT
        else:
            steps = _rate_expected(inner, analysis)
            assumptions = (POISSON_EVENTS, PERSON_TIME, PRESPECIFIED, RATE_NULL)
            unit, limit = "events", EVENTS_LIMIT
        valid, outside = _count_point(test, point, search, study)
        search_ok = search is not None and _count_search_valid(
            {key: value for key, value in search.items() if key != "analysis"}, unit, limit
        )
        return _planning_steps(
            name,
            inner,
            steps,
            assumptions,
            point,
            valid,
            outside,
            NULL_STATEMENTS[study["study"]],
            target,
            search,
            search_ok,
            analysis,
        )
    steps, assumptions = _association_expected(inner, analysis)
    kind = study["study"]
    keys = GROUP_POINT_KEYS.get(kind)
    if "n" in study:  # only the total is fixed: the point also gives the share exposed
        share = point.get("exposed_share")
        valid = (
            keys is not None
            and set(point) == {*keys, "exposed_share"}
            and all(_probability(point[key]) for key in keys)
            and 0 < Fraction(share) < 1
            and (search is not None or study["n"] <= TOTAL_LIMIT)
        )
        outside = valid and Fraction(point[keys[0]]) != Fraction(point[keys[1]])
        bounds = {key: value for key, value in (search or {}).items() if key != "analysis"}
        search_ok = (
            search is not None
            and set(bounds) == {"min_n", "max_n"}
            and _whole(bounds["min_n"], 1)
            and _whole(bounds["max_n"], bounds["min_n"])
            and bounds["max_n"] <= TOTAL_LIMIT
        )
        return _planning_steps(
            name,
            inner,
            steps,
            assumptions,
            point,
            valid,
            outside,
            NULL_STATEMENTS[kind],
            target,
            search,
            search_ok,
            analysis,
        )
    groups = (
        (study["cases"], study["controls"])
        if kind == "case_control"
        else (study.get("exposed"), study.get("unexposed"))
    )
    valid = (
        keys is not None
        and None not in groups
        and set(point) == set(keys)
        and all(_probability(point[key]) for key in keys)
        and (search is not None or max(groups) <= PER_ARM_LIMIT)
    )
    outside = valid and Fraction(point[keys[0]]) != Fraction(point[keys[1]])
    search_ok = (
        search is not None
        and keys is not None
        and _group_search_valid(
            {key: value for key, value in search.items() if key != "analysis"}, kind
        )
    )
    return _planning_steps(
        name,
        inner,
        steps,
        assumptions,
        point,
        valid,
        outside,
        NULL_STATEMENTS[kind],
        target,
        search,
        search_ok,
        analysis,
    )


def _planning_steps(
    name,
    inner,
    steps,
    assumptions,
    point,
    valid,
    outside,
    statement,
    target,
    search,
    search_ok,
    analysis,
):
    """The planning steps that follow an observational test's own contract steps."""
    used = [len(steps) - 1]
    steps.append(
        (
            "planning-point",
            {"subject": name, "analysis": "association", "point": point},
            valid,
            (),
        )
    )
    used.append(len(steps) - 1)
    steps.append(("alternative", {"subject": name, "point": point, "null": statement}, outside, ()))
    used.append(len(steps) - 1)
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used.append(len(steps) - 1)
    if search is not None:
        bounds = {key: value for key, value in search.items() if key != "analysis"}
        steps.append(("search-range", {"subject": name, "search": bounds}, search_ok, ()))
        used.append(len(steps) - 1)
    steps.append(("planning-contract", {"subject": name}, True, tuple(used)))
    obligations = [
        (
            "error-budget",
            {"subject": name, "alpha": analysis["alpha"], "maximum_typeI": maximum},
            Fraction(analysis["alpha"]) <= Fraction(maximum),
        ),
        _sampling_expectation(inner, analysis),
    ]
    return steps, obligations, (*assumptions, PLANNING_POINT_ASSUMPTION)


def _planning_expected(derivation: dict) -> tuple[list[tuple], list[tuple], tuple[str, ...]]:
    name, claim = derivation["name"], derivation["subject"]
    if derivation["contract"] != f"planning/{claim['kind']}":
        raise ValueError("the contract does not match the claim")
    subject = claim["subject"]
    search = subject.get("candidates")
    if (search is not None) != (claim["kind"] == "sample_size"):
        raise ValueError("a search accompanies exactly the sample_size claim")
    if "interval" in (subject.get("analysis") or search or {}):
        return _precision_expected(name, subject, search)
    analysis = subject["analysis"] if search is None else search.get("analysis")
    if analysis is not None and analysis.get("method") in ("alpha_spending", "group_sequential"):
        return _sequential_planning_expected(name, subject, search, analysis)
    if analysis is not None and analysis.get("rule") == "blinded_reestimation":
        return _reestimation_planning_expected(name, subject, search, analysis)
    if analysis is not None and analysis.get("method") in FAMILY_METHODS:
        return _family_planning_expected(name, subject, search, analysis)
    if analysis is not None and analysis.get("test") in METHODS:
        return _cited_planning_expected(name, subject, search, analysis)
    if analysis is not None and analysis.get("test") in OBSERVATIONAL_METHODS:
        return _cited_association_planning_expected(name, subject, search, analysis)
    if analysis is not None and analysis.get("test") in ("fisher_exact", "mcnemar", "rate_test"):
        return _association_planning_expected(name, subject, search, analysis)
    target, inner = subject["target"], f"{name}.analysis"
    steps, used = [], []
    if analysis is not None:
        steps = _block(inner, analysis)
        used.append(len(steps) - 1)
        assumptions = BLOCKS[analysis["test"]][1]
    else:
        assumptions = TWO_STAGE_ASSUMPTIONS
    two_arm = analysis is not None and analysis["test"] == "fisher"
    point = target["at"]
    kind = "two_arm" if two_arm else "single_arm"
    steps.append(
        (
            "planning-point",
            {"subject": name, "analysis": kind, "point": point},
            ("p_control" in point and "p_treatment" in point) == two_arm
            and ("response_rate" in point) != two_arm,
            (),
        )
    )
    used.append(len(steps) - 1)
    if "p_control" in point:
        facts = {
            "subject": name,
            "p_control": point["p_control"],
            "p_treatment": point["p_treatment"],
            "null": "p_treatment = p_control",
        }
        outside = Fraction(point["p_control"]) != Fraction(point["p_treatment"])
        kind = analysis.get("alternative", "two_sided") if two_arm else "two_sided"
        gap = Fraction(point["p_treatment"]) - Fraction(point["p_control"])
        if kind == "greater":
            facts["null"] = "p_treatment <= p_control"
            outside = gap > 0
        elif kind == "margin":
            facts["null"] = f"p_treatment - p_control <= {analysis['null']['value']}"
            outside = gap > Fraction(analysis["null"]["value"])
    else:
        null_rate = search["null_rate"] if analysis is None else analysis["null_rate"]
        facts = {
            "subject": name,
            "rate": point["response_rate"],
            "null_rate": null_rate,
            "null": f"response rate <= {null_rate}",
        }
        outside = Fraction(point["response_rate"]) > Fraction(null_rate)
    steps.append(("alternative", facts, outside, ()))
    used.append(len(steps) - 1)
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used.append(len(steps) - 1)
    if search is not None:
        bounds = {key: value for key, value in search.items() if key != "analysis"}
        steps.append(
            ("search-range", {"subject": name, "search": bounds}, _search_valid(bounds), ())
        )
        used.append(len(steps) - 1)
    steps.append(("planning-contract", {"subject": name}, True, tuple(used)))
    obligations = []
    if two_arm:
        obligations.append(
            (
                "error-budget",
                {"subject": name, "alpha": analysis["alpha"], "maximum_typeI": maximum},
                Fraction(analysis["alpha"]) <= Fraction(maximum),
            )
        )
        obligations.append(_sampling_expectation(inner, analysis))
    return steps, obligations, (*assumptions, PLANNING_POINT_ASSUMPTION)


def _sizes(model: dict) -> dict:
    return {"n_control": model["n_control"], "n_treatment": model["n_treatment"]}


def _statement(null: dict) -> str:
    if null["predicate"] == "equal_proportions":
        return "p_treatment = p_control"
    operator = "=" if null["predicate"] == "proportion_difference" else "<="
    return f"p_treatment - p_control {operator} {null['value']}"


def _analysis_expectations(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    """(rule, facts, premise holds) for the three premises of the analysis contract."""
    design, null = analysis["design"], analysis["null"]
    if _features(design["model"]) or _features(null["model"]):
        raise ValueError("an exact two-arm test cannot take clusters or repeated measurements")
    alternative = analysis.get("alternative", "two_sided")
    supported = SUPPORTED_NULLS[alternative]
    null_ok = null["predicate"] in supported and (
        alternative == "two_sided"
        or (alternative == "greater" and Fraction(null["value"]) == 0)
        or (alternative == "margin" and -1 < Fraction(null["value"]) < 1)
    )
    alpha = Fraction(analysis["alpha"])
    return [
        (
            "same-model",
            {
                "subject": name,
                "design_model": _sizes(design["model"]),
                "null_model": _sizes(null["model"]),
            },
            _sizes(design["model"]) == _sizes(null["model"]),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": _statement(null),
                "supported": supported,
                **_direction_facts(null),
            },
            null_ok and _direction_ok(null),
        ),
        ("level-range", {"subject": name, "alpha": analysis["alpha"]}, 0 <= alpha <= 1),
    ]


def _randomised(model: dict) -> tuple[str, int, int]:
    """The kind of unit randomised, how many, and how many treated, from the serialized model."""
    if "clusters_control" in model:
        control, treated = model["clusters_control"], model["clusters_treatment"]
        return "cluster", control + treated, treated
    return "participant", model["n_control"] + model["n_treatment"], model["n_treatment"]


def _blocks(model: dict, units: int, treated: int) -> list[tuple[int, int]] | None:
    """The independently randomised groups the model declares, worked out here from the
    serialized model, or None if they do not describe a randomisation."""
    scheme, strata, size = model.get("randomisation"), model.get("strata"), model.get("block_size")
    if scheme == "complete":
        return [(units, treated)] if strata is None and size is None else None
    if scheme == "stratified" and (size is not None or strata is None or len(strata) < 2):
        return None
    if scheme == "blocked" and not (_whole(size, 2)):
        return None
    if scheme not in ("stratified", "blocked"):
        return None
    layers = strata if strata is not None else [[units - treated, treated]]
    if not all(
        isinstance(layer, list)
        and len(layer) == 2
        and all(_whole(count, 0) for count in layer)
        and sum(layer) > 0
        for layer in layers
    ):
        return None
    if [sum(layer[0] for layer in layers), sum(layer[1] for layer in layers)] != [
        units - treated,
        treated,
    ]:
        return None
    if scheme == "stratified":
        groups = [(control + treat, treat) for control, treat in layers]
    else:
        groups = []
        for control, treat in layers:
            whole = control + treat
            if whole % size or (treat * size) % whole:
                return None
            groups += [(size, treat * size // whole)] * (whole // size)
    return groups if len(groups) <= GROUP_LIMIT else None


def _randomisation_expected(name: str, subject: dict) -> list[tuple]:
    """The randomisation test's premises, re-evaluated from the serialized subject."""
    if subject.get("test") != "randomisation":
        raise ValueError("the contract does not match the declaration")
    design, null = subject["design"], subject["null"]
    model, alpha = design["model"], Fraction(subject["alpha"])
    unit, units, treated = _randomised(model)
    possible = _whole(treated, 1) and _whole(units, treated + 1) and units <= UNIT_LIMIT
    groups = _blocks(model, units, treated) if possible else None
    splits = 1
    for size, treat in groups or []:
        splits *= comb(size, treat)
    steps = [
        (
            "same-model",
            {"subject": name, "design_model": _sizes(model), "null_model": _sizes(null["model"])},
            model == null["model"],
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": SHARP_NULL.statement,
                "supported": [SHARP_NULL.key],
                **_direction_facts(null),
            },
            null["predicate"] == SHARP_NULL.key and set(null) == {"predicate", "model"},
            (),
        ),
        ("level-range", {"subject": name, "alpha": subject["alpha"]}, 0 <= alpha <= 1, ()),
        (
            "declared-randomisation",
            {
                "subject": name,
                "randomisation": model.get("randomisation"),
                "unit": unit,
                "units": units,
                "treated": treated,
                **({"strata": model["strata"]} if "strata" in model else {}),
                **({"block_size": model["block_size"]} if "block_size" in model else {}),
            },
            model.get("randomisation") in SCHEMES and groups is not None,
            (),
        ),
    ]
    if "draws" in subject:
        draws = subject["draws"]
        drawn = _whole(draws, 1) and draws <= DRAW_LIMIT
        smallest = Fraction(1, draws + 1) if drawn else Fraction(1)
        steps.append(
            (
                "can-reject-drawn",
                {
                    "subject": name,
                    "draws": draws,
                    "smallest": str(smallest),
                    "alpha": subject["alpha"],
                },
                groups is not None and drawn and smallest <= alpha,
                (),
            )
        )
    else:
        steps.append(
            (
                "can-reject",
                {"subject": name, "splits": str(splits), "alpha": subject["alpha"]},
                groups is not None and Fraction(1, splits) <= alpha,
                (),
            )
        )
    if "population" in model:
        # Only everyone randomised, in the assigned arms, has the declared randomisation.
        steps.append(
            (
                "randomised-population",
                {"subject": name, "population": model["population"], "unit": unit},
                model["population"] == "randomised",
                (),
            )
        )
    steps.append(("randomisation-contract", {"subject": name}, True, (0, 1, 2, 3, 4)))
    return steps


def _null_statement(null: dict) -> str:
    """The statement of a registered null form, from the registry's data."""
    if null["predicate"] == SHARP_NULL.key:
        # Only a declared test may take the sharp null besides the randomisation test.
        return SHARP_NULL.statement
    form = NULL_FORMS[null["predicate"]][1]
    return form.state(Fraction(null["value"]) if form.takes_value else Fraction(0))


def _method(subject: dict) -> CitedMethod | None:
    """The registry's method, or for a declared test the method the file describes."""
    test = subject.get("test")
    if test in METHODS:
        return METHODS[test]
    if test != "declared_test":
        return None
    title, scope, references = subject["method"], subject["scope"], subject["references"]
    valid = (
        isinstance(title, str)
        and title.strip()
        and scope in SCOPES
        and isinstance(references, list)
        and len(references) <= 1
    )
    if not valid:
        raise ValueError("the declared test is not described properly")
    return CitedMethod(
        key="declared_test",
        module="tests.declared",
        title=title,
        version=1,
        outcome="",
        null=subject["null"]["predicate"],
        relation="at_most",
        scope=scope,
        assumptions=(DECLARED_VALID,),
        references=tuple(references),
        min_per_arm=1,
        min_total=2,
        grade="declared",
    )


def _cited_expected(name: str, subject: dict, contract: str):
    """Steps, obligations, assumptions and guarantee for a cited method's contract.

    The method registry is data, like the rules. The premises are re-evaluated here.
    """
    method = _method(subject)
    if method is None or contract != f"{method.module}/{method.key}":
        raise ValueError("the contract does not match the declaration")
    design, null = subject["design"], subject["null"]
    sizes, alpha = _sizes(design["model"]), Fraction(subject["alpha"])
    # A declared test fits any model; a cited one fits its own outcome's model.
    expected_model = (
        design["model"]["module"]
        if method.grade == "declared"
        else OUTCOMES[method.outcome].constructor
    )
    continuous = all(
        model["module"] == expected_model for model in (design["model"], null["model"])
    )
    value_ok = method.null_value is None or (Fraction(null.get("value", "0")) == method.null_value)
    minimum = {"min_per_arm": method.min_per_arm, "min_total": method.min_total}
    if method.unit == "cluster":
        # Counted in clusters, which the model must declare.
        model = design["model"]
        counts = (model.get("clusters_control"), model.get("clusters_treatment"))
        enough = all(_whole(count, 1) for count in counts) and (
            min(counts) >= method.min_per_arm and sum(counts) >= method.min_total
        )
        size_step = (
            "enough-clusters",
            {
                "subject": name,
                "clusters_control": counts[0],
                "clusters_treatment": counts[1],
                **minimum,
            },
            enough,
            (),
        )
    else:
        enough = (
            min(sizes.values()) >= method.min_per_arm and sum(sizes.values()) >= method.min_total
        )
        size_step = ("enough-data", {"subject": name, **sizes, **minimum}, enough, ())
    steps = [
        (
            "same-model",
            {"subject": name, "design_model": sizes, "null_model": _sizes(null["model"])},
            continuous and sizes == _sizes(null["model"]),
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": _null_statement(null),
                "supported": list(method.nulls),
                **_direction_facts(null),
            },
            null["predicate"] in method.nulls and value_ok and _direction_ok(null),
            (),
        ),
        ("level-interior", {"subject": name, "alpha": subject["alpha"]}, 0 < alpha < 1, ()),
        size_step,
    ]
    design_step = _design_facts(name, design["model"], method)
    steps += [design_step] if design_step else []
    contract_rule = "cluster-contract" if method.unit == "cluster" else "cited-contract"
    steps.append((contract_rule, {"subject": name}, True, (0, 1, 2, 3)))
    fixed = _sampling_expectation(name, subject)
    extra = (*_direction_assumed(null), *_vouched(design["model"], method))
    guarantee = None
    if fixed[2]:
        statement = Guarantee(
            "type_I_error",
            method.relation,
            alpha,
            _null_statement(null),
            method.scope,
            method.limit,
        )
        guarantee = {
            **statement.to_dict(),
            "sentence": statement.sentence,
            "grade": method.grade,
            "method": method.to_dict(),
            "given": [item.id for item in (*method.assumptions, *extra)],
            "references": list(method.references),
        }
    texts = tuple(item.text for item in (*method.assumptions, *extra))
    return steps, [fixed], texts, guarantee


MEMBER_GRADES = {
    "proved": "provable in Lean; verify the member's own Type I claim",
    "cited": "cited from the literature; not machine-checked",
    "conditional": "holds if each of its own members' bounds holds; verify its own claim",
    "declared": "declared by the author; not checked and not cited",
}


BRETZ = (
    "Bretz, F., Maurer, W., Brannath, W. and Posch, M. (2009). A graphical approach to "
    "sequentially rejective multiple test procedures. Statistics in Medicine 28(4), 586-604."
)
BURMAN = (
    "Burman, C.-F., Sonesson, C. and Guilbaud, O. (2009). A recycling framework for the "
    "construction of Bonferroni-based multiple tests. Statistics in Medicine 28(5), 739-761."
)
COMPOSITIONS = {
    # method: (contract, the assumption it adds, member assumptions it replaces,
    #          concluding rule, levels are split, error quantity, what must grow,
    #          grade of the combination rule)
    "bonferroni": (
        "multiplicity.bonferroni/bonferroni",
        PRESPECIFIED_FAMILY,
        (),
        "composed-family-contract",
        True,
        "familywise_error",
        "each member's sample size or number of events grows",
        "conditional",
    ),
    "alpha_spending": (
        "designs.group_sequential/alpha_spending",
        PRESPECIFIED_LOOKS,
        (FIXED_SIZES.text, SINGLE_ANALYSIS.text),
        "sequential-contract",
        True,
        "type_I_error",
        "the sample size at each look grows",
        "conditional",
    ),
    "group_sequential": (
        "designs.group_sequential/group_sequential",
        PRESPECIFIED_SPENDING,
        (FIXED_SIZES.text, SINGLE_ANALYSIS.text),
        "spending-contract",
        False,
        "type_I_error",
        "the sample size at each look grows",
        "cited",
    ),
    "fixed_sequence": (
        "multiplicity.fixed_sequence/fixed_sequence",
        PRESPECIFIED_ORDER,
        (),
        "fixed-sequence-contract",
        False,
        "familywise_error",
        "each member's sample size or number of events grows",
        "conditional",
    ),
    "graphical": (
        "multiplicity.graphical/graphical",
        PRESPECIFIED_GRAPH,
        (),
        "graphical-contract",
        False,
        "familywise_error",
        "each member's sample size or number of events grows",
        "cited",
    ),
}
GRAPHICAL_METHOD = {
    "key": "graphical",
    "version": 1,
    "title": "Graphical multiple testing procedure",
}
SPENDING_METHOD = {
    "key": "group_sequential",
    "version": 1,
    "title": "Group-sequential boundaries from an error-spending function",
}


# The limits a derivation records for each design with spending boundaries, by name. The
# checker trusts none of them: each is accepted only once _spending_checked confirms it.
_RECORDED: ContextVar[dict[str, object] | None] = ContextVar(
    "statclaim_recorded_limits", default=None
)
_NORMAL = NormalDist()
GRID_POINTS = 201  # odd, for Simpson's rule on a uniform grid
SPENT_TOLERANCE = 1e-6  # absolute, on the error spent by each look


def _spent(spending: str, alpha: float, fraction: float, sides: int) -> float:
    """The error Lan and DeMets's spending functions spend by an information fraction,
    written from their definitions. A two-sided design spends half on each side."""
    if sides == 2:
        return 2.0 * _spent(spending, alpha / 2.0, fraction, 1)
    if fraction >= 1.0:
        return alpha
    if spending == "obrien_fleming":
        z = _NORMAL.inv_cdf(1.0 - alpha / 2.0)
        return 2.0 * (1.0 - _NORMAL.cdf(z / math.sqrt(fraction)))
    if spending == "pocock":
        return alpha * math.log(1.0 + (math.e - 1.0) * fraction)
    raise ValueError(f"unknown spending function {spending!r}")


def _simpson(low: float, high: float) -> tuple[list[float], list[float]]:
    step = (high - low) / (GRID_POINTS - 1)
    nodes = [low + i * step for i in range(GRID_POINTS)]
    weights = [
        step / 3.0 * (1 if i in (0, GRID_POINTS - 1) else 4 if i % 2 else 2)
        for i in range(GRID_POINTS)
    ]
    return nodes, weights


def _first_crossings(shares: list[float], levels: list[float], sides: int) -> list[float]:
    """The null chance of first crossing at each look, each look at its nominal level. The
    score at information t is N(0, t) with independent increments; the sub-density of the
    paths that have not crossed is carried from look to look on a uniform grid."""
    found: list[float] = []
    nodes: list[float] = []
    weights: list[float] = []
    density: list[float] = []
    before = 0.0
    for share, level in zip(shares, levels, strict=True):
        spread = math.sqrt(share)
        critical = _NORMAL.inv_cdf(1.0 - level / sides) if level > 0 else math.inf
        bound = critical * spread
        if not nodes:
            crossing = level
        else:
            step = math.sqrt(share - before)
            crossing = sum(
                w
                * f
                * (
                    1.0
                    - _NORMAL.cdf((bound - s) / step)
                    + (_NORMAL.cdf((-bound - s) / step) if sides == 2 else 0.0)
                )
                for s, f, w in zip(nodes, density, weights, strict=True)
            )
        found.append(crossing)
        low = max(-bound if sides == 2 else -math.inf, -12.0 * spread)
        grid, grid_weights = _simpson(low, min(bound, 12.0 * spread))
        if not nodes:
            density = [_NORMAL.pdf(u / spread) / spread for u in grid]
        else:
            density = [
                sum(
                    w * f * _NORMAL.pdf((u - s) / step)
                    for s, f, w in zip(nodes, density, weights, strict=True)
                )
                / step
                for u in grid
            ]
        nodes, weights, before = grid, grid_weights, share
    return found


def _spending_checked(
    limits: list[str], sizes: list[tuple], alpha: Fraction, sides: int, spending: str
) -> bool:
    """Whether looks at these nominal levels spend the error as the spending function does:
    the chance of first crossing by each look is what the function spends there."""
    information = [Fraction(c * t, c + t) for c, t in sizes]
    shares = [float(info / information[-1]) for info in information]
    crossed = 0.0
    for share, crossing in zip(
        shares, _first_crossings(shares, [float(Fraction(x)) for x in limits], sides), strict=True
    ):
        crossed += crossing
        if abs(crossed - _spent(spending, float(alpha), share, sides)) > SPENT_TOLERANCE:
            return False
    return True


def _limit_text(value: object) -> bool:
    """A level from 0 to 1 written exactly, rounded down to 1e-9."""
    if not isinstance(value, str):
        return False
    level = Fraction(value)
    return 0 <= level <= 1 and (level * 10**9).denominator == 1


def _spending_limits(name: str, subject: dict, members: list) -> tuple[list | None, bool]:
    """Each look's largest level, as the derivation records it, and whether those are the
    spending function's boundaries: the levels rounded down to 1e-9, checked from the
    definition. (None, False) when the test's boundary is not one the rule covers."""
    final = members[-1][1]
    if final.get("test") == "fisher":
        alternative = final.get("alternative", "two_sided")
        if alternative not in ("two_sided", "greater"):
            return None, False
        sides = 2 if alternative == "two_sided" else 1
    else:
        method = _method(final)
        if method is None or method.module != "tests.t":
            return None, False
        sides = 1 if NULL_FORMS[final["null"]["predicate"]][1].favours else 2
    recorded = (_RECORDED.get() or {}).get(name)
    if subject.get("spending") not in SPENDING or not isinstance(recorded, list):
        return None, False
    if len(recorded) != len(members) or not all(_limit_text(x) for x in recorded):
        return recorded, False
    sizes = [
        (a["design"]["model"]["n_control"], a["design"]["model"]["n_treatment"]) for _, a in members
    ]
    return recorded, _spending_checked(
        recorded, sizes, Fraction(subject["alpha"]), sides, subject["spending"]
    )


def _share(text) -> bool:
    return isinstance(text, str) and 0 <= Fraction(text) <= 1


def _combination(name: str, subject: dict, offset: int = 0, nested: bool = False) -> dict:
    """What a combination's declaration implies, re-derived from the serialized subject.

    Step indices are absolute: `offset` is the number of steps before this block.
    """
    method_name = subject.get("method")
    if method_name not in COMPOSITIONS or subject.get("composition") != "conditional":
        raise ValueError("not a conditional combination")
    contract, own, discharged, rule, splits, quantity, limit, grade_of_rule = COMPOSITIONS[
        method_name
    ]
    spending = method_name == "group_sequential"
    sequential = method_name == "alpha_spending" or spending
    graphical = method_name == "graphical"
    members = [(item["name"], item["analysis"]) for item in subject["analyses"]]
    names = [member for member, _ in members]
    steps: list[tuple] = []
    finals, inner_obligations, components = [], [], []
    own_texts, nested_texts, cited_texts = [own.text], [], []
    if spending:
        own_texts.append(CANONICAL_JOINT.text)
    exact, keys, nulls = True, [], []
    for member, analysis in members:
        start = offset + len(steps)
        member_quantity = "type_I_error"
        if "test" not in analysis:
            if sequential or graphical:
                raise ValueError("a look or a graph's test must be a single analysis")
            block = _combination(member, analysis, start, nested=True)
            steps += block["steps"]
            inner_obligations += block["obligations"]
            nested_texts += [
                text for text in (*block["own"], *block["nested"]) if text not in nested_texts
            ]
            cited_texts += [text for text in block["cited"] if text not in cited_texts]
            null, grade, scope = block["null"], block["grade"], block["scope"]
            member_quantity = block["quantity"]
            basis = block["contract"] + (f" version {block['version']}" if grade == "cited" else "")
            keys.append("design")
        elif _method(analysis) is not None:
            method = _method(analysis)
            block_steps, fixed, texts, _ = _cited_expected(
                member, analysis, f"{method.module}/{method.key}"
            )
            steps += [(r, f, h, tuple(start + u for u in uses)) for r, f, h, uses in block_steps]
            inner_obligations += fixed
            cited_texts += [
                text for text in texts if text not in cited_texts and text not in discharged
            ]
            null, grade, scope = _null_statement(analysis["null"]), method.grade, method.scope
            basis = (
                f"declared by the author: {method.title}"
                if grade == "declared"
                else f"{method.module}/{method.key} version {method.version}"
            )
            keys.append(method.key)
        elif analysis["test"] == "fisher":
            for rule_name, facts, holds in _analysis_expectations(member, analysis):
                steps.append((rule_name, facts, holds, ()))
            steps.append(
                ("analysis-contract", {"subject": member}, True, tuple(range(start, start + 3)))
            )
            inner_obligations.append(_sampling_expectation(member, analysis))
            null, grade, scope = _statement(analysis["null"]), "proved", "finite_sample"
            basis = CONTRACT_IDS[analysis.get("alternative", "two_sided")]
            keys.append(basis.split("/")[1])
        elif analysis["test"] == "randomisation":
            if sequential:
                raise ValueError("a randomisation test cannot be a look")
            block_steps = _randomisation_expected(member, analysis)
            steps += [(r, f, h, tuple(start + u for u in uses)) for r, f, h, uses in block_steps]
            inner_obligations.append(_sampling_expectation(member, analysis))
            null, grade, scope = SHARP_NULL.statement, "proved", "finite_sample"
            basis = RANDOMISATION_CONTRACT_ID
            keys.append("randomisation_test")
        else:
            raise ValueError("a member's analysis cannot be combined")
        finals.append(offset + len(steps) - 1)
        if "test" in analysis:
            nulls.append((analysis["null"]["predicate"], analysis["null"].get("value")))
        exact = exact and scope == "finite_sample"
        components.append(
            {
                "name": member,
                "level": analysis["alpha"],
                "scope": scope,
                "grade": grade,
                "basis": basis,
                "null": null,
                "quantity": member_quantity,
            }
        )
        bound = Guarantee(
            member_quantity, "at_most", Fraction(analysis["alpha"]), null, "finite_sample"
        )
        own_texts.append(f"{member}: {bound.sentence} ({MEMBER_GRADES[grade]})")
    if method_name == "bonferroni" and not nested and all(key == "fisher" for key in keys):
        raise ValueError("a family of two-sided Fisher analyses is proved, not conditional")
    low, high = FAMILY_LIMITS
    base = offset + len(steps)
    distinct = len(set(names)) == len(names)
    steps += [
        ("distinct-members", {"subject": name, "members": names}, distinct, ()),
        ("family-size", {"subject": name, "count": len(names)}, low <= len(names) <= high, ()),
    ]
    used = [*finals, base, base + 1]
    alpha = Fraction(subject["alpha"])
    if sequential:
        sizes = [
            [a["design"]["model"]["n_control"], a["design"]["model"]["n_treatment"]]
            for _, a in members
        ]
        modules = {a["design"]["model"]["module"] for _, a in members}
        grows = all(
            later[0] >= earlier[0] and later[1] >= earlier[1] and sum(later) > sum(earlier)
            for earlier, later in zip(sizes, sizes[1:], strict=False)
        )
        steps += [
            (
                "same-question",
                {"subject": name, "test": keys[0], "statement": components[0]["null"]},
                len(set(keys)) == 1 and len(set(nulls)) == 1 and len(modules) == 1,
                (),
            ),
            ("increasing-looks", {"subject": name, "sizes": sizes}, grows, ()),
        ]
        used += [base + 2, base + 3]
    if spending:
        limits, checked = _spending_limits(name, subject, members)
        levels = [analysis["alpha"] for _, analysis in members]
        within = (
            limits is not None
            and checked
            and all(
                Fraction(level) <= Fraction(top) for level, top in zip(levels, limits, strict=True)
            )
        )
        facts = {
            "subject": name,
            "spending": subject.get("spending"),
            "alpha": subject["alpha"],
            "limits": limits,
            "levels": levels,
        }
        steps.append(("spending-boundaries", facts, within, ()))
        used.append(base + 4)
    elif not splits:
        full = all(Fraction(analysis["alpha"]) == alpha for _, analysis in members)
        steps.append(("full-level", {"subject": name, "alpha": subject["alpha"]}, full, ()))
        used.append(base + 2)
    if graphical:
        weights, table = subject["weights"], subject["transitions"]
        count = len(members)
        weights_ok = (
            len(weights) == count
            and all(_share(weight) for weight in weights)
            and sum(Fraction(weight) for weight in weights) <= 1
        )
        table_ok = len(table) == count and all(
            len(row) == count
            and all(_share(share) for share in row)
            and Fraction(row[index]) == 0
            and sum(Fraction(share) for share in row) <= 1
            for index, row in enumerate(table)
        )
        total = str(sum((Fraction(weight) for weight in weights), Fraction()))
        steps += [
            (
                "graph-weights",
                {"subject": name, "weights": weights, "total": total},
                weights_ok,
                (),
            ),
            ("graph-transitions", {"subject": name, "transitions": table}, table_ok, ()),
        ]
        used += [base + 3, base + 4]
    questions = _questions(name, subject["analyses"])
    steps += [questions] if questions else []
    steps.append((rule, {"subject": name, "members": names}, True, tuple(used)))
    obligations = []
    if splits:
        allocated = sum((Fraction(analysis["alpha"]) for _, analysis in members), Fraction())
        obligations.append(
            (
                "allocation",
                {"subject": name, "allocated": str(allocated), "alpha": subject["alpha"]},
                allocated <= alpha,
            )
        )
    obligations += inner_obligations
    scope = "finite_sample" if exact and not spending else "asymptotic"
    null = components[0]["null"] if sequential else "any subset of the member nulls is true"
    statement = Guarantee(quantity, "at_most", alpha, null, scope, limit)
    extra = (
        {"method": SPENDING_METHOD, "references": [LAN_DEMETS, JENNISON_TURNBULL]}
        if spending
        else {"method": GRAPHICAL_METHOD, "references": [BRETZ, BURMAN]}
        if grade_of_rule == "cited"
        else {}
    )
    return {
        "contract": contract,
        "version": 1,
        "grade": grade_of_rule,
        "quantity": quantity,
        "steps": steps,
        "obligations": obligations,
        "own": own_texts,
        "nested": nested_texts,
        "cited": cited_texts,
        "scope": scope,
        "null": null,
        "guarantee": {
            **statement.to_dict(),
            "sentence": statement.sentence,
            "grade": grade_of_rule,
            "members": components,
            "given": [
                own.id,
                *([CANONICAL_JOINT.id] if spending else []),
                *(f"member_guarantee:{n}" for n in names),
            ],
            **extra,
        },
    }


def _single(analyses: list) -> list[dict]:
    """The single analyses of a combination, inside nested ones too."""
    found = []
    for item in analyses:
        analysis = item["analysis"]
        found += [analysis] if "test" in analysis else _single(analysis["analyses"])
    return found


def _questions(name: str, analyses: list) -> tuple | None:
    """The distinct-questions step, when some analysis names its outcome."""
    named = [a for a in _single(analyses) if "outcome_name" in a["design"]["model"]]
    if not named:
        return None
    definitions: dict = {}
    agree = True
    for analysis in named:
        model = analysis["design"]["model"]
        definition = (model["module"], model.get("better"))
        agree = agree and definitions.setdefault(model["outcome_name"], definition) == definition
    asked = [
        json.dumps({k: v for k, v in analysis.items() if k != "alpha"}, sort_keys=True)
        for analysis in named
    ]
    outcomes = ", ".join(dict.fromkeys(a["design"]["model"]["outcome_name"] for a in named))
    return (
        "distinct-questions",
        {"subject": name, "outcomes": outcomes},
        agree and len(set(asked)) == len(asked),
        (),
    )


def _composed_expected(name: str, subject: dict, contract: str):
    """Steps, obligations, assumptions and guarantee of a combination's contract."""
    block = _combination(name, subject)
    if contract != block["contract"]:
        raise ValueError("the contract does not match the declaration")
    met = all(holds for _, _, holds in block["obligations"])
    return (
        block["steps"],
        block["obligations"],
        (*block["own"], *block["nested"], *block["cited"]),
        block["guarantee"] if met else None,
    )


def _carried(derivation: dict):
    """What a contract that carries a guarantee implies; None for any other contract."""
    subject = derivation.get("subject")
    if not isinstance(subject, dict):
        return None
    if _method(subject) is not None:
        return _cited_expected(derivation["name"], subject, derivation["contract"])
    if subject.get("composition") == "conditional":
        return _composed_expected(derivation["name"], subject, derivation["contract"])
    return None


def _association_expected(name: str, subject: dict) -> tuple[list[tuple], tuple[str, ...]]:
    """Fisher's test of association, re-evaluated from the serialized subject."""
    if subject.get("test") != "fisher_exact":
        raise ValueError("the contract does not match the declaration")
    study, null = subject["design"]["model"], subject["null"]
    kind = study["study"]
    sizes = {
        "case_control": ("cases", "controls"),
        "cohort": ("exposed", "unexposed") if "exposed" in study else ("n",),
        "cross_sectional": ("n",),
    }[kind]
    positive = all(isinstance(study.get(key), int) and study[key] >= 1 for key in sizes)
    if kind == "case_control":
        fixed = f"{study['cases']} cases and {study['controls']} controls"
    elif "exposed" in study:
        fixed = f"{study['exposed']} exposed and {study['unexposed']} unexposed"
    else:
        fixed = f"only the total, {study['n']}"
    alpha = Fraction(subject["alpha"])
    steps = [
        (
            "same-model",
            {"subject": name, "design_model": study, "null_model": null["model"]},
            study == null["model"],
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": NULL_STATEMENTS[kind],
                "supported": ["no_association"],
            },
            null["predicate"] == "no_association",
            (),
        ),
        ("level-range", {"subject": name, "alpha": subject["alpha"]}, 0 <= alpha <= 1, ()),
        (
            "observational-sampling",
            {"subject": name, "study": kind.replace("_", "-"), "fixed": fixed},
            positive,
            (),
        ),
        ("association-contract", {"subject": name}, True, (0, 1, 2, 3)),
    ]
    if kind == "case_control":
        assumptions = (
            CASE_CONTROL_GROUPS,
            INDEPENDENT_EXPOSURES,
            SOURCE_POPULATION,
            PRESPECIFIED,
            CASE_CONTROL_NULL,
        )
    else:
        sampled = COHORT_GROUPS if "exposed" in study else RANDOM_SAMPLE
        stated = CROSS_SECTIONAL_NULL if kind == "cross_sectional" else COHORT_NULL
        assumptions = (sampled, INDEPENDENT_OUTCOMES, PRESPECIFIED, stated)
    return steps, assumptions


def _matched_expected(name: str, subject: dict) -> list[tuple]:
    """McNemar's test, re-evaluated from the serialized subject."""
    if subject.get("test") not in ("mcnemar", "mcnemar_asymptotic"):
        raise ValueError("the contract does not match the declaration")
    study, null = subject["design"]["model"], subject["null"]
    if study.get("study") != "matched_case_control":
        raise ValueError("McNemar's test needs a matched design")
    pairs = study.get("pairs")
    alpha = Fraction(subject["alpha"])
    steps = [
        (
            "same-model",
            {"subject": name, "design_model": study, "null_model": null["model"]},
            study == null["model"],
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": NULL_STATEMENTS["matched_case_control"],
                "supported": ["no_association"],
            },
            null["predicate"] == "no_association",
            (),
        ),
        ("level-range", {"subject": name, "alpha": subject["alpha"]}, 0 <= alpha <= 1, ()),
        (
            "matched-sampling",
            {"subject": name, "pairs": pairs},
            isinstance(pairs, int) and pairs >= 1,
            (),
        ),
    ]
    if subject["test"] == "mcnemar_asymptotic":
        cutoff = subject["squared_cutoff"]
        steps.append(
            (
                "mcnemar-cutoff",
                {"subject": name, "squared_cutoff": cutoff},
                Fraction(cutoff) > 0,
                (),
            )
        )
    steps.append(("mcnemar-contract", {"subject": name}, True, tuple(range(len(steps)))))
    return steps


def _rate_expected(name: str, subject: dict) -> list[tuple]:
    """The exact rate test, re-evaluated from the serialized subject."""
    if subject.get("test") != "rate_test":
        raise ValueError("the contract does not match the declaration")
    study, null = subject["design"]["model"], subject["null"]
    alpha = Fraction(subject["alpha"])
    return [
        (
            "same-model",
            {"subject": name, "design_model": study, "null_model": null["model"]},
            study == null["model"],
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": NULL_STATEMENTS["person_time_cohort"],
                "supported": ["no_association"],
            },
            null["predicate"] == "no_association",
            (),
        ),
        ("level-range", {"subject": name, "alpha": subject["alpha"]}, 0 <= alpha <= 1, ()),
        (
            "person-time-sampling",
            {"subject": name},
            study.get("study") == "person_time_cohort",
            (),
        ),
        ("rate-test-contract", {"subject": name}, True, (0, 1, 2, 3)),
    ]


def _cited_association_expected(name: str, subject: dict, contract: str):
    """A cited observational test, re-evaluated from the subject and the method registry."""
    method = OBSERVATIONAL_METHODS.get(subject.get("test"))
    if method is None or contract != f"{method.module}/{method.key}":
        raise ValueError("the contract does not match the declaration")
    study, null = subject["design"]["model"], subject["null"]
    kind = study["study"]
    outcome_scale = study.get("outcome_scale", "binary")
    exposure_scale = study.get("exposure_scale", "binary")
    survey = study.get("survey", "simple_random")
    covariates = subject.get("adjusted_for", [])
    if kind == "matched_case_control":
        total = study.get("pairs")
    elif kind == "case_control":
        total = study.get("cases", 0) + study.get("controls", 0)
    elif kind == "person_time_cohort":
        total = None
    else:
        total = study.get("n") or study.get("exposed", 0) + study.get("unexposed", 0)
    fits = (
        kind in method.designs
        and outcome_scale in method.outcome_scales
        and exposure_scale in method.exposure_scales
        and survey in method.surveys
        and (total is None or total >= method.min_total)
        and (
            not method.min_clusters
            or survey != "cluster"
            or study.get("clusters", 0) >= method.min_clusters
        )
        and (method.covariates or not covariates)
    )
    statement = (
        "exposure_coefficient = 0"
        if "continuous" in (outcome_scale, exposure_scale)
        else NULL_STATEMENTS[kind]
    )
    alpha = Fraction(subject["alpha"])
    steps = [
        (
            "same-model",
            {"subject": name, "design_model": study, "null_model": null["model"]},
            study == null["model"],
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": statement,
                "supported": ["no_association"],
            },
            null["predicate"] == "no_association",
            (),
        ),
        ("level-interior", {"subject": name, "alpha": subject["alpha"]}, 0 < alpha < 1, ()),
        (
            "method-fits-study",
            {
                "subject": name,
                "study": kind.replace("_", "-"),
                "method": method.key,
                "covariates": len(covariates),
            },
            fits,
            (),
        ),
        (
            "cited-association-contract",
            {"subject": name, "method": method.key},
            True,
            (0, 1, 2, 3),
        ),
    ]
    return steps, tuple(item.text for item in method.assumptions)


def _sampling_expectation(name: str, analysis: dict) -> tuple[str, dict, bool]:
    stopping = analysis["design"]["stopping"]
    return ("fixed-sampling", {"subject": name, "stopping": stopping}, stopping == "fixed")


def _expected(derivation: dict) -> tuple[list[tuple], list[tuple], tuple[str, ...]]:
    """What the subject implies: required steps, obligation rules, assumptions.

    A required step is (rule, facts, holds, rules or step groups it must use).
    """
    name, subject, contract = derivation["name"], derivation["subject"], derivation["contract"]
    carried = _carried(derivation)
    if carried is not None:
        return carried[:3]
    if contract in PROPORTION_Z_CONTRACT_IDS.values():
        if contract != PROPORTION_Z_CONTRACT_IDS.get(subject["test"]):
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract == LIKELIHOOD_RATIO_CONTRACT_ID:
        if subject.get("test") != "likelihood_ratio_test":
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract == PEARSON_CONTRACT_ID:
        if subject.get("test") != "pearson_test":
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract == FARRINGTON_MANNING_CONTRACT_ID:
        if subject.get("test") != "farrington_manning":
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract in CONTRACT_IDS.values():
        if subject["test"] != "fisher" or contract != CONTRACT_IDS.get(
            subject.get("alternative", "two_sided")
        ):
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract.split("/")[0] in ("tests.regression", "tests.correlation", "tests.survey"):
        steps, assumptions = _cited_association_expected(name, subject, contract)
        return steps, [_sampling_expectation(name, subject)], assumptions
    if contract == RATE_CONTRACT_ID:
        assumptions = (POISSON_EVENTS, PERSON_TIME, PRESPECIFIED, RATE_NULL)
        return _rate_expected(name, subject), [_sampling_expectation(name, subject)], assumptions
    if contract in (MCNEMAR_CONTRACT_ID, ASYMPTOTIC_MCNEMAR_CONTRACT_ID):
        if contract != f"tests.association/{subject.get('test')}":
            raise ValueError("the contract does not match the declaration")
        assumptions = (PAIRS_SAMPLED, WITHIN_PAIRS, SOURCE_POPULATION, PRESPECIFIED, MATCHED_NULL)
        return _matched_expected(name, subject), [_sampling_expectation(name, subject)], assumptions
    if contract == ASSOCIATION_CONTRACT_ID:
        steps, assumptions = _association_expected(name, subject)
        return steps, [_sampling_expectation(name, subject)], assumptions
    if contract == RANDOMISATION_CONTRACT_ID:
        model = subject["design"]["model"]
        grouped = model.get("randomisation") != "complete"
        counted = (
            (POPULATION, COUNTS_DRAWS if "draws" in subject else COUNTS_EVERY_SPLIT)
            if "population" in model
            else (AS_DRAWN if "draws" in subject else AS_RANDOMISED,)
        )
        assumptions = (
            GROUPED if grouped else RANDOMISED,
            PRESPECIFIED,
            *counted,
            SHARP_NULL_TEXT,
        )
        return (
            _randomisation_expected(name, subject),
            [_sampling_expectation(name, subject)],
            assumptions,
        )
    policy_contracts = {
        "tests.binomial/binomial_test": "binomial_exact_one_sided",
        "tests.binomial/binomial_score_test": "binomial_score_test",
        "designs.two_stage/two_stage_test": "two_stage",
    }
    if contract in policy_contracts:
        expected = policy_contracts[contract]
        if subject["test"] != expected:
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [], BLOCKS[expected][1]
    if contract in ("planning/meets", "planning/sample_size"):
        return _planning_expected(derivation)
    if contract == "multiplicity.bonferroni/bonferroni":
        steps, obligations = _fisher_family_expected(name, subject)
        return steps, obligations, FAMILY_ASSUMPTIONS
    raise ValueError(f"unknown contract {contract!r}")


def _fisher_family_expected(name: str, subject: dict) -> tuple[list, list]:
    """A proved family of Fisher analyses: its steps and obligations."""
    members = [(item["name"], item["analysis"]) for item in subject["analyses"]]
    names = [member for member, _ in members]
    steps, finals = [], []
    for member, analysis in members:
        start = len(steps)
        for rule, facts, holds in _analysis_expectations(member, analysis):
            steps.append((rule, facts, holds, ()))
        steps.append(
            ("analysis-contract", {"subject": member}, True, tuple(range(start, start + 3)))
        )
        finals.append(len(steps) - 1)
    low, high = FAMILY_LIMITS
    base = len(steps)
    steps += [
        (
            "distinct-members",
            {"subject": name, "members": names},
            len(set(names)) == len(names),
            (),
        ),
        ("family-size", {"subject": name, "count": len(names)}, low <= len(names) <= high, ()),
        (
            "joint-law",
            {"subject": name, "joint_law": subject["joint_law"]},
            subject["joint_law"] in SUPPORTED_JOINT_LAWS,
            (),
        ),
    ]
    questions = _questions(name, subject["analyses"])
    steps += [questions] if questions else []
    steps.append(
        (
            "family-contract",
            {"subject": name, "members": names},
            True,
            (*finals, base, base + 1, base + 2),
        )
    )
    allocated = sum((Fraction(analysis["alpha"]) for _, analysis in members), Fraction())
    obligations = [
        (
            "allocation",
            {"subject": name, "allocated": str(allocated), "alpha": subject["alpha"]},
            allocated <= Fraction(subject["alpha"]),
        )
    ]
    obligations += [_sampling_expectation(member, analysis) for member, analysis in members]
    return steps, obligations


def check_derivation(derivation: dict) -> list[str]:
    """Return the problems found; an empty list means the derivation is valid."""
    problems: list[str] = []
    recorded = {
        step["facts"]["subject"]: step["facts"].get("limits")
        for step in derivation.get("steps", [])
        if isinstance(step, dict)
        and step.get("rule") == "spending-boundaries"
        and isinstance(step.get("facts"), dict)
        and "subject" in step["facts"]
    }
    token = _RECORDED.set(recorded)
    try:
        # A guarantee may be carried only by a contract that supplies one, and then
        # only the guarantee the declaration implies.
        carried = _carried(derivation)
        guarantee = carried[3] if carried else None
        if derivation.get("guarantee") != guarantee:
            problems.append("The recorded guarantee is not the one the declaration implies.")
        scope = "conditional_guarantee" if guarantee else "compatibility"
        if derivation.get("scope") != scope:
            problems.append("The derivation's scope does not match what it establishes.")
        if derivation.get("not_established") != (
            NOT_ESTABLISHED
            if not guarantee
            else {
                "conditional": COMPOSED_NOT_ESTABLISHED,
                "declared": DECLARED_NOT_ESTABLISHED,
            }.get(guarantee["grade"], CITED_NOT_ESTABLISHED)
        ):
            problems.append("The statement of what is not established is missing or altered.")
        required, obligation_rules, assumptions = _expected(derivation)
        steps = derivation["steps"]
        for index, step in enumerate(steps):
            rule = RULES.get(step.get("rule"))
            if rule is None:
                problems.append(f"Step {index + 1} names an unknown rule.")
            elif step.get("premise") != rule.premise:
                problems.append(f"Step {index + 1} misstates the premise of {step['rule']}.")
            elif step.get("rule_version") != rule.version:
                problems.append(f"Step {index + 1} uses another version of {step['rule']}.")
            if any(not isinstance(use, int) or not 0 <= use < index for use in step["uses"]):
                problems.append(f"Step {index + 1} uses a step that does not precede it.")
        # The required steps must appear, in order, as the leading steps.
        for index, (rule, facts, holds, uses) in enumerate(required):
            label = f"Step {index + 1} ({rule})"
            if index >= len(steps):
                problems.append(f"{label} is missing.")
                continue
            step = steps[index]
            if step["rule"] != rule:
                problems.append(f"{label}: found rule {step['rule']!r} instead.")
                continue
            if step["facts"] != facts:
                problems.append(f"{label}: the recorded facts do not match the declaration.")
            if not holds:
                problems.append(f"{label}: the premise does not hold for the declaration.")
            if step["conclusion"] != RULES[rule].conclusion.format(**facts):
                problems.append(f"{label}: the conclusion is not the rule's conclusion.")
            if tuple(step["uses"]) != uses:
                problems.append(f"{label}: it does not rest on the required earlier steps.")
        if required and len(steps) >= len(required):
            final = RULES[required[-1][0]].conclusion.format(**required[-1][1])
            if derivation["conclusion"] != final:
                problems.append("The stated conclusion is not the conclusion of the contract rule.")
        # Obligation rules: a step when the premise holds, an open obligation when not.
        extra = steps[len(required) :]
        expected_steps = [(rule, facts) for rule, facts, holds in obligation_rules if holds]
        expected_open = [(rule, facts) for rule, facts, holds in obligation_rules if not holds]
        if [(step["rule"], step["facts"]) for step in extra] != expected_steps:
            problems.append("The steps for obligation rules do not match the declaration.")
        for step in extra:
            rule = RULES.get(step["rule"])
            if rule and step["conclusion"] != rule.conclusion.format(**step["facts"]):
                problems.append(f"The conclusion recorded for {step['rule']} is altered.")
        recorded = [(item["rule"], item["facts"]) for item in derivation["obligations"]]
        if recorded != expected_open:
            problems.append("The unresolved obligations do not match the declaration.")
        for item in derivation["obligations"]:
            rule = RULES.get(item["rule"])
            if rule is None or rule.obligation is None:
                problems.append("An obligation names a rule that cannot leave an obligation.")
            elif item["code"] != rule.code or item["statement"] != rule.obligation.format(
                **item["facts"]
            ):
                problems.append(f"The obligation recorded for {item['rule']} is altered.")
        if tuple(derivation["assumptions"]) != assumptions:
            problems.append("The required assumptions do not match the contract.")
    except (KeyError, TypeError, ValueError, IndexError, ZeroDivisionError) as error:
        problems.append(f"Malformed derivation: {error}")
    finally:
        _RECORDED.reset(token)
    return problems
