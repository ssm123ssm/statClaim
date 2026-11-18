"""Evaluation scenarios: common specification errors, each injected into a valid study.

Every scenario states what should happen. `evaluate.py` runs them and records
what did happen, including the errors StatClaim cannot see. Add a scenario by
appending to SCENARIOS; nothing else needs to change.

Outcomes, from strongest to weakest:
  rejected    the file is invalid, with a diagnostic at the cause
  unresolved  the file is valid but the claim is refused until a requirement is met
  calculated  an exact calculation shows that the stated target is not met
  surfaced    nothing is flagged, but the report lists the assumption that is violated,
              for a claim or in a justification
  invisible   nothing is flagged and nothing in the report points at the problem
"""

from dataclasses import dataclass
from math import ceil
from statistics import NormalDist

BINARY = """use models.two_arm_binomial
use sampling
use tests.fisher
let study = two_arm_binomial(n_control=100, n_treatment=100)
let plan = fixed(model=study)
let null = equal_proportions(model=study)
let analysis = fisher(design=plan, null=null, alpha=1/20)
"""
CONTINUOUS = """use models.two_arm_continuous
use sampling
use tests.t
let study = two_arm_continuous(n_control=60, n_treatment=60)
let plan = fixed(model=study)
let null = equal_means(model=study)
let analysis = t_test(design=plan, null=null, alpha=1/20)
"""
TWO_LOOKS = """use models.two_arm_continuous
use sampling
use tests.t
use designs.group_sequential
let halfway = two_arm_continuous(n_control=50, n_treatment=50)
let complete = two_arm_continuous(n_control=100, n_treatment=100)
let interim = t_test(design=fixed(model=halfway), null=equal_means(model=halfway), alpha=1/200)
let final = t_test(design=fixed(model=complete), null=equal_means(model=complete), alpha=9/200)
"""
PLANNING = """use models.two_arm_binomial
use sampling
use tests.fisher
use planning
let study = two_arm_binomial(n_control={n}, n_treatment={n})
let analysis = fisher(design=fixed(model=study), null=equal_proportions(model=study), alpha=1/20)
let expected = binomial_rates(p_control=1/10, p_treatment=2/5)
let target = power_target(at=expected, minimum=4/5, maximum_typeI=1/20)
"""
LOGISTIC = """use models.two_arm_binomial
use sampling
use tests.logistic
let study = two_arm_binomial(n_control=600, n_treatment=600)
let plan = fixed(model=study)
let null = proportion_difference_at_most(model=study, value=-3/100)
let analysis = logistic_regression_one_sided(design=plan, null=null, alpha=1/40)
"""
SYMPTOMS = """use models.two_arm_continuous
use sampling
use tests.mixed_model
let study = two_arm_continuous(n_control=200, n_treatment=200{better})
let plan = fixed(model=study)
let null = mean_difference_at_most(model=study, value=-1/10)
let analysis = mmrm_test_one_sided(design=plan, null=null, alpha=1/40)
"""
# The same continuous study, with its design declared on the model's pieces.
PIECES = """use models.two_arm_continuous
use sampling
use tests.t
let arms = {assignment}
let study = two_arm(assignment=arms, outcome=continuous_outcome({outcome}))
let plan = fixed(model=study)
let null = equal_means(model=study)
let analysis = t_test(design=plan, null=null, alpha=1/20)
"""
CLINICS = (
    "cluster_assignment(clusters_control=10, clusters_treatment=10, n_control=200, n_treatment=200)"
)
PER_PROTOCOL = """use models.two_arm_binomial
use sampling
use tests.difference
let study = two_arm_binomial(n_control=96, n_treatment=96)
let plan = fixed(model=study)
let null = proportion_difference_at_most(model=study, value=-1/10)
let analysis = difference_test(design=plan, null=null, alpha=1/40)
"""
POSTERIOR = """use designs.two_stage
use planning
let stages = two_stage_binomial(n_stage1=10, n_stage2=20)
let rule = posterior_rule(
    prior=beta_prior(a=1, b=1),
    reference=1/5,
    continue_at_least=1/2,
    success_at_least=19/20,
)
let analysis = two_stage_test(design=stages, rule=rule, null_rate=1/5)
let target = power_target(at=response_rate(value=2/5), minimum=4/5, maximum_typeI={level})
let check = calculate(meets(analysis=analysis, target=target))
"""


def normal_approximation_size(p_control: float, p_treatment: float, alpha: float, power: float):
    """The textbook per-arm size for comparing two proportions, unpooled variance."""
    z = NormalDist().inv_cdf
    variance = p_control * (1 - p_control) + p_treatment * (1 - p_treatment)
    return ceil((z(1 - alpha / 2) + z(power)) ** 2 * variance / (p_treatment - p_control) ** 2)


APPROXIMATE_N = normal_approximation_size(0.1, 0.4, 0.05, 0.8)


@dataclass(frozen=True)
class Scenario:
    key: str
    category: str
    error: str  # the mistake, in a researcher's words
    source: str
    expected: str  # rejected, unresolved, calculated, surfaced or invisible
    code: str | None = None  # the diagnostic expected, when one is
    surfaces: str | None = None  # the assumption id the report should list
    note: str = ""


def endpoints(count: int, each: str, family: str) -> str:
    names = [f"endpoint_{i}" for i in range(1, count + 1)]
    lines = [f"let {name} = fisher(design=plan, null=null, alpha={each})" for name in names]
    return (
        BINARY
        + "use multiplicity.bonferroni\n"
        + "\n".join(lines)
        + f"\nlet family = bonferroni(analyses=[{', '.join(names)}], alpha={family})\n"
        + "verify familywise(family)\n"
    )


SCENARIOS = (
    # ---- The null does not match the question the test answers
    Scenario(
        "ni_null_superiority_test",
        "Hypothesis",
        "A non-inferiority null is given to a two-sided superiority test.",
        CONTINUOUS.replace(
            "equal_means(model=study)", "mean_difference_at_most(model=study, value=-2)"
        ),
        "rejected",
        "hypothesis_mismatch",
    ),
    Scenario(
        "equality_null_one_sided_test",
        "Hypothesis",
        "An equality null is given to a one-sided test.",
        CONTINUOUS.replace("t_test(", "t_test_one_sided("),
        "rejected",
        "hypothesis_mismatch",
    ),
    Scenario(
        "nonzero_difference_fisher",
        "Hypothesis",
        "Fisher's exact test is used to test a nonzero difference in proportions.",
        BINARY.replace(
            "equal_proportions(model=study)", "proportion_difference(model=study, value=1/10)"
        ),
        "rejected",
        "hypothesis_mismatch",
    ),
    Scenario(
        "null_from_another_study",
        "Hypothesis",
        "The null is stated for a model with different arm sizes than the design.",
        CONTINUOUS.replace(
            "let null = equal_means(model=study)",
            "let pilot = two_arm_continuous(n_control=20, n_treatment=20)\n"
            "let null = equal_means(model=pilot)",
        ),
        "rejected",
        "model_mismatch",
    ),
    Scenario(
        "binary_test_continuous_outcome",
        "Hypothesis",
        "A test for proportions is declared for a continuous outcome.",
        CONTINUOUS.replace(
            "use tests.t", "use tests.t\nuse models.two_arm_binomial\nuse tests.fisher"
        ).replace(
            "t_test(design=plan, null=null",
            "fisher(design=plan, null=equal_proportions(model=study)",
        ),
        "rejected",
        "type",
    ),
    Scenario(
        "survival_test_continuous_outcome",
        "Hypothesis",
        "The log-rank test is declared for a continuous outcome.",
        CONTINUOUS.replace("use tests.t", "use tests.t\nuse tests.survival").replace(
            "t_test(", "log_rank("
        ),
        "rejected",
        "hypothesis_mismatch",
    ),
    # ---- Sampling plan
    Scenario(
        "optional_stopping_exact",
        "Sampling",
        "Data are checked repeatedly and the study stops when significant (exact test).",
        BINARY.replace("fixed(", "adaptive(") + "verify typeI(analysis)\n",
        "unresolved",
        "sampling_scope",
    ),
    Scenario(
        "optional_stopping_cited",
        "Sampling",
        "Data are checked repeatedly and the study stops when significant (t-test).",
        CONTINUOUS.replace("fixed(", "adaptive(") + "verify typeI(analysis)\n",
        "unresolved",
        "sampling_scope",
    ),
    Scenario(
        "looks_at_full_level",
        "Sampling",
        "An interim and a final analysis are each run at the full 5% level.",
        TWO_LOOKS.replace("alpha=1/200", "alpha=1/20").replace("alpha=9/200", "alpha=1/20")
        + "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\nverify typeI(trial)\n",
        "unresolved",
        "allocation",
    ),
    Scenario(
        "looks_out_of_order",
        "Sampling",
        "The looks are listed with the final analysis before the interim one.",
        TWO_LOOKS + "let trial = alpha_spending(looks=[final, interim], alpha=1/20)\n",
        "rejected",
        "sequential_order",
    ),
    Scenario(
        "looks_change_the_test",
        "Sampling",
        "The interim look uses a different test from the final analysis.",
        TWO_LOOKS.replace("let interim = t_test(", "let interim = welch_test(")
        + "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\n",
        "rejected",
        "sequential_question",
    ),
    Scenario(
        "result_feeds_design",
        "Sampling",
        "A design value is taken from the result of an earlier analysis.",
        BINARY
        + "let data = observe(analysis, control_successes=10, treatment_successes=25)\n"
        + "let first = calculate(result(data))\n"
        + "let second = fisher(design=plan, null=null, alpha=first.calculation.p_value)\n",
        "rejected",
        "type",
    ),
    Scenario(
        "undeclared_peeking",
        "Sampling",
        "The file declares a fixed design, but the data were in fact checked along the way.",
        CONTINUOUS + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="single_analysis",
        note="StatClaim sees only the declaration. The report lists 'run once' as declared "
        "by the file, which is the statement the study broke.",
    ),
    # ---- Multiplicity
    Scenario(
        "ten_endpoints_at_five_percent",
        "Multiplicity",
        "Ten endpoints are each tested at 5% and a 5% familywise error is claimed.",
        endpoints(10, "1/20", "1/20"),
        "unresolved",
        "allocation",
    ),
    Scenario(
        "duplicate_endpoint",
        "Multiplicity",
        "One analysis is listed twice in a family to appear as two endpoints.",
        BINARY
        + "use multiplicity.bonferroni\nlet again = analysis\n"
        + "let family = bonferroni(analyses=[analysis, again], alpha=1/10)\n",
        "rejected",
        "duplicate_analysis",
    ),
    Scenario(
        "sequence_with_split_levels",
        "Multiplicity",
        "A hierarchical procedure is declared but the level is split between endpoints.",
        CONTINUOUS.replace("alpha=1/20", "alpha=1/40")
        + "use multiplicity.fixed_sequence\n"
        + "let second = welch_test(design=plan, null=null, alpha=1/40)\n"
        + "let order = fixed_sequence(analyses=[analysis, second], alpha=1/20)\n",
        "rejected",
        "sequence_level",
    ),
    Scenario(
        "familywise_claim_on_looks",
        "Multiplicity",
        "A familywise claim is requested for repeated looks at one question.",
        TWO_LOOKS
        + "use multiplicity.bonferroni\n"
        + "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\n"
        + "let claim = familywise(trial)\n",
        "rejected",
        "type",
    ),
    Scenario(
        "same_outcome_declared_twice",
        "Multiplicity",
        "The same outcome is declared as two separate analyses to gain a second chance.",
        BINARY
        + "use multiplicity.bonferroni\n"
        + "let again = fisher(design=plan, null=null, alpha=1/20)\n"
        + "let family = bonferroni(analyses=[analysis, again], alpha=1/10)\n"
        + "verify familywise(family)\n",
        "invisible",
        note="Two declarations with identical content are indistinguishable from two real "
        "outcomes measured on the same participants.",
    ),
    Scenario(
        "graph_shares_exceed_whole",
        "Multiplicity",
        "A graphical procedure starts three endpoints with half the level each.",
        CONTINUOUS.replace(
            "equal_means(model=study)", "mean_difference_at_most(model=study, value=0)"
        )
        .replace("t_test(", "welch_test_one_sided(")
        .replace("alpha=1/20", "alpha=1/40")
        + "use multiplicity.graphical\n"
        + "let second = welch_test_one_sided(design=plan, null=null, alpha=1/40)\n"
        + "let third = welch_test_one_sided(design=plan, null=null, alpha=1/40)\n"
        + "let graph = graphical(analyses=[analysis, second, third], weights=[1/2, 1/2, 1/2], "
        + "transitions=[[0, 1, 0], [0, 0, 1], [1, 0, 0]], alpha=1/40)\n",
        "rejected",
        "graph_definition",
    ),
    Scenario(
        "graph_recycles_to_itself",
        "Multiplicity",
        "A graphical procedure lets an endpoint keep its own level after it is rejected.",
        CONTINUOUS.replace(
            "equal_means(model=study)", "mean_difference_at_most(model=study, value=0)"
        )
        .replace("t_test(", "welch_test_one_sided(")
        .replace("alpha=1/20", "alpha=1/40")
        + "use multiplicity.graphical\n"
        + "let second = welch_test_one_sided(design=plan, null=null, alpha=1/40)\n"
        + "let graph = graphical(analyses=[analysis, second], weights=[1/2, 1/2], "
        + "transitions=[[1, 0], [1, 0]], alpha=1/40)\n",
        "rejected",
        "graph_definition",
    ),
    # ---- Planning and error targets
    Scenario(
        "approximate_sample_size",
        "Planning",
        f"The per-arm size {APPROXIMATE_N} from the normal-approximation formula is used "
        "with Fisher's exact test, expecting 80% power.",
        PLANNING.format(n=APPROXIMATE_N)
        + "let check = calculate(meets(analysis=analysis, target=target))\n",
        "calculated",
        "target_not_met",
        note="The size is computed in scenarios.py from the standard formula, not typed in.",
    ),
    Scenario(
        "target_stricter_than_level",
        "Planning",
        "A 2.5% Type I error is promised from a test run at 5%.",
        PLANNING.format(n=40).replace("maximum_typeI=1/20", "maximum_typeI=1/40")
        + "let check = verify(meets(analysis=analysis, target=target))\n",
        "unresolved",
        "typeI_target_not_established",
    ),
    Scenario(
        "planning_point_in_null",
        "Planning",
        "Power is planned at a point where the two arms have equal rates.",
        PLANNING.format(n=40).replace("p_treatment=2/5", "p_treatment=1/10")
        + "let check = calculate(meets(analysis=analysis, target=target))\n",
        "rejected",
        "alternative_in_null",
    ),
    Scenario(
        "range_too_small",
        "Planning",
        "A sample-size search is limited to sizes that cannot reach the target.",
        PLANNING.format(n=20)
        + "let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=10, max_per_arm=20)\n"
        + "let search = calculate(sample_size(candidates=sizes, target=target))\n",
        "calculated",
        "no_feasible_candidate",
    ),
    Scenario(
        "posterior_threshold_as_error_rate",
        "Planning",
        "A 95% posterior probability rule is assumed to give a 5% false-positive rate.",
        POSTERIOR.format(level="1/20"),
        "calculated",
        "target_not_met",
    ),
    # ---- Values and data
    Scenario(
        "level_of_zero",
        "Values",
        "A t-test is declared with a significance level of zero.",
        CONTINUOUS.replace("alpha=1/20", "alpha=0"),
        "rejected",
        "domain",
    ),
    Scenario(
        "one_participant_per_arm",
        "Values",
        "Welch's test is declared with one participant per arm.",
        CONTINUOUS.replace("60", "1").replace("t_test(", "welch_test("),
        "rejected",
        "domain",
    ),
    Scenario(
        "more_events_than_participants",
        "Values",
        "The observed number of responders exceeds the arm size.",
        BINARY + "let data = observe(analysis, control_successes=10, treatment_successes=125)\n",
        "rejected",
        "domain",
    ),
    # ---- What a declaration cannot show
    Scenario(
        "non_normal_outcomes",
        "Assumptions",
        "The pooled t-test is used for a strongly skewed outcome.",
        CONTINUOUS + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="normal_outcomes",
        note="Nothing in a design can show the outcome's distribution. The report lists "
        "normality as assumed.",
    ),
    Scenario(
        "small_sample_large_sample_test",
        "Assumptions",
        "Welch's test, whose guarantee is large-sample, is used with three per arm.",
        CONTINUOUS.replace("60", "3").replace("t_test(", "welch_test(")
        + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="finite_variance",
        note="No sample size is too small to declare. The result is worded as a large-sample "
        "approximation with no bound at the declared size.",
    ),
    Scenario(
        "informative_censoring",
        "Assumptions",
        "The log-rank test is used although sicker participants drop out earlier.",
        """use models.two_arm_survival
use sampling
use tests.survival
let study = two_arm_survival(n_control=200, n_treatment=200)
let analysis = log_rank(design=fixed(model=study), null=equal_survival(model=study), alpha=1/20)
verify typeI(analysis)
""",
        "surfaced",
        surfaces="independent_censoring",
    ),
    Scenario(
        "one_sided_at_five_percent",
        "Assumptions",
        "A one-sided non-inferiority test is run at 5% where 2.5% is the convention.",
        CONTINUOUS.replace(
            "equal_means(model=study)", "mean_difference_at_most(model=study, value=-2)"
        ).replace("t_test(", "t_test_one_sided(")
        + "verify typeI(analysis)\n",
        "invisible",
        note="The guarantee at 5% is correct as stated. Which level a regulator expects is a "
        "convention, not a property of the test.",
    ),
    Scenario(
        "wrong_sample_size_transcribed",
        "Assumptions",
        "The file declares 100 per arm but the protocol enrols 80.",
        BINARY + "verify typeI(analysis)\n",
        "invisible",
        note="StatClaim checks the declared study, not its agreement with another document.",
    ),
    # ---- What the outcome means
    Scenario(
        "risk_margin_logistic",
        "Meaning",
        "A non-inferiority margin on the risk difference is given to a one-sided logistic "
        "regression.",
        LOGISTIC,
        "rejected",
        "hypothesis_mismatch",
        note="The logistic test is of a coefficient. A margin on the risk difference is a "
        "different question, and a rule that combines an odds-ratio threshold with a "
        "risk-difference margin cannot be stated.",
    ),
    Scenario(
        "lower_is_better_wrong_way",
        "Meaning",
        "A score where lower is better is declared so, but its null asks whether the "
        "treatment's scores are higher.",
        SYMPTOMS.format(better=', better="lower"'),
        "rejected",
        "direction_mismatch",
    ),
    Scenario(
        "lower_is_better_undeclared",
        "Meaning",
        "A score where lower is better is tested with a null that asks whether the "
        "treatment's scores are higher, and the file does not say which direction is better.",
        SYMPTOMS.format(better="") + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="higher_is_better",
        note="The register lists that higher values are taken to be better, marked assumed. "
        'Declaring better="lower" makes this a rejection.',
    ),
    # ---- Several values per participant, or clusters assigned instead of participants
    Scenario(
        "repeated_measures_declared",
        "Unit of analysis",
        "Three measurements on each of 100 participants per arm are declared as such, but the "
        "analysis is a t-test, which counts every measurement as a separate participant.",
        PIECES.format(
            assignment="assignment(n_control=100, n_treatment=100)", outcome="measurements=3"
        ),
        "rejected",
        "unit_mismatch",
    ),
    Scenario(
        "repeated_measures_as_participants",
        "Unit of analysis",
        "Three measurements on each of 100 participants per arm are declared as 300 "
        "independent observations per arm.",
        CONTINUOUS.replace("n_control=60, n_treatment=60", "n_control=300, n_treatment=300")
        + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="independent_observations",
        note="Nothing in the file says that observations share participants. The register "
        "lists independent observations as assumed. Declaring the outcome's measurements "
        "makes this a rejection.",
    ),
    Scenario(
        "cluster_randomised_declared",
        "Unit of analysis",
        "Ten clinics per arm are randomised and the file says so, but the analysis is a "
        "t-test on participants, as if each had been randomised alone.",
        PIECES.format(assignment=CLINICS, outcome=""),
        "rejected",
        "unit_mismatch",
    ),
    Scenario(
        "cluster_randomised_undeclared",
        "Unit of analysis",
        "Ten clinics per arm are randomised, but the file declares 200 participants per arm "
        "and a t-test on participants.",
        CONTINUOUS.replace("n_control=60, n_treatment=60", "n_control=200, n_treatment=200")
        + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="independent_observations",
        note="Nothing in the file says that clinics were randomised. The register lists "
        "independent observations as assumed. Declaring cluster_assignment(...) makes this a "
        "rejection.",
    ),
    # ---- How the study is run, which a declaration does not show
    Scenario(
        "endpoint_chosen_after_interim",
        "Study conduct",
        "The endpoint analysed was chosen after an interim comparison of two candidates; "
        "the file declares only the chosen one.",
        BINARY + "verify typeI(analysis)\n",
        "surfaced",
        surfaces="prespecified_analysis",
        note="A verified test of the chosen endpoint does not cover the choice. The report's "
        "justification lists that the analysis was chosen before outcomes were observed: the "
        "statement the study broke.",
    ),
    Scenario(
        "per_protocol_population",
        "Study conduct",
        "Participants excluded after randomisation are left out and only the remaining "
        "numbers are declared, although the question is about everyone randomised.",
        PER_PROTOCOL + "verify typeI(analysis)\n",
        "invisible",
        note="Nothing in the file describes the exclusions or the population the question is "
        "about. The guarantee holds for the declared numbers.",
    ),
)
