"""Cited methods for observational studies: regression with covariates, correlation and
analyses of complex survey samples. Their guarantees are cited, not proved.

Each method says which designs, measurement scales and survey samples it fits. The
compiler checks that fit and the null; the guarantee is the published result, restated
with its assumptions. A bound concerns association, never an effect of the exposure.
"""

from dataclasses import dataclass, field
from fractions import Fraction

from statclaim.methods.association_power import CORRELATION as CORRELATION_POWER
from statclaim.methods.association_power import (
    EXPOSURE_MEANS,
    LOGISTIC_GROUPS,
    LOGISTIC_TREND,
    MATCHED_PAIRS,
    POISSON_RATES,
    RISK_RATIO,
    SPEARMAN,
    SURVEY_GROUPS,
    SURVEY_MEANS,
    SURVEY_SLOPE,
    SURVEY_TREND,
)
from statclaim.methods.association_power import SLOPE as SLOPE_POWER
from statclaim.methods.core import Assumption, Guarantee, PowerFormula

SCALES = {
    "binary": "A yes-or-no variable.",
    "continuous": "A measured quantity, such as blood pressure.",
}
SURVEYS = {
    "simple_random": "Participants sampled independently with equal probability.",
    "stratified": "Participants sampled separately within declared strata.",
    "cluster": "Whole clusters, such as households or schools, sampled first.",
    "weighted": "Participants sampled with unequal, known probabilities.",
}

# Assumptions --------------------------------------------------------------------------------
INDEPENDENT_SAMPLE = Assumption(
    "independent_sample",
    "sampling",
    "Participants were sampled independently of one another, with equal probability.",
)
PRESPECIFIED_MODEL = Assumption(
    "prespecified_model",
    "design",
    "The analysis, its covariates and its level were chosen before the data were seen.",
)
COEFFICIENT_NULL = Assumption(
    "coefficient_null",
    "scope",
    "The test is of the exposure's coefficient: under the null, the outcome does not depend "
    "on the exposure given the covariates.",
)
LOGIT_MODEL = Assumption(
    "logit_model",
    "distribution",
    "The log odds of the outcome are linear in the exposure and covariates.",
)
LOG_LINEAR_MODEL = Assumption(
    "log_linear_model",
    "distribution",
    "The log of the outcome's probability, or of the rate, is linear in the exposure and "
    "covariates.",
)
LINEAR_MODEL = Assumption(
    "linear_model",
    "distribution",
    "The outcome's mean is linear in the exposure and covariates, with independent, normally "
    "distributed errors of one variance.",
)
BIVARIATE_NORMAL = Assumption(
    "bivariate_normal",
    "distribution",
    "Exposure and outcome are jointly normally distributed.",
)
NO_TIES = Assumption(
    "exact_permutation",
    "approximation",
    "The p-value is the exact permutation p-value of the rank correlation; ties, if any, "
    "are handled by randomly breaking them.",
)
ENOUGH_OUTCOMES = Assumption(
    "enough_outcomes",
    "distribution",
    "There are enough participants with and without the outcome for the estimate to be "
    "approximately normal, with no separation.",
)
CASE_CONTROL_LOGISTIC = Assumption(
    "case_control_logistic",
    "sampling",
    "Cases and controls were sampled without regard to exposure, so the exposure's "
    "coefficient estimates the population log odds ratio; the intercept has no meaning.",
)
MATCHED_SETS = Assumption(
    "matched_sets",
    "sampling",
    "The model conditions on the matched pairs; characteristics used for matching are not "
    "adjusted for again.",
)
POISSON_COUNTS = Assumption(
    "poisson_counts",
    "distribution",
    "Events follow a Poisson process with person-time as the exposure offset; any "
    "overdispersion is accounted for.",
)
ROBUST_VARIANCE = Assumption(
    "robust_variance",
    "approximation",
    "The variance comes from a robust (sandwich) estimator.",
)
DESIGN_BASED = Assumption(
    "design_based",
    "design",
    "The analysis uses the survey's weights, strata and clusters as declared.",
)
ENOUGH_CLUSTERS = Assumption(
    "enough_clusters",
    "approximation",
    "There are enough sampled clusters for the design-based variance to be stable.",
)

# References ---------------------------------------------------------------------------------
COX = (
    "Cox, D. R. (1958). The regression analysis of binary sequences. Journal of the Royal "
    "Statistical Society B 20(2), 215-242."
)
PRENTICE_PYKE = (
    "Prentice, R. L. and Pyke, R. (1979). Logistic disease incidence models and case-control "
    "studies. Biometrika 66(3), 403-411."
)
BRESLOW_DAY = (
    "Breslow, N. E. and Day, N. E. (1980). Statistical Methods in Cancer Research, Vol. I: "
    "The Analysis of Case-Control Studies. IARC."
)
BRESLOW_DAY_COHORT = (
    "Breslow, N. E. and Day, N. E. (1987). Statistical Methods in Cancer Research, Vol. II: "
    "The Design and Analysis of Cohort Studies. IARC."
)
ZOU = (
    "Zou, G. (2004). A modified Poisson regression approach to prospective studies with "
    "binary data. American Journal of Epidemiology 159(7), 702-706."
)
SEBER = "Seber, G. A. F. and Lee, A. J. (2003). Linear Regression Analysis, 2nd ed. Wiley."
FISHER_1915 = (
    "Fisher, R. A. (1915). Frequency distribution of the values of the correlation coefficient "
    "in samples from an indefinitely large population. Biometrika 10(4), 507-521."
)
HOLLANDER = (
    "Hollander, M., Wolfe, D. A. and Chicken, E. (2014). Nonparametric Statistical Methods, "
    "3rd ed. Wiley."
)
BINDER = (
    "Binder, D. A. (1983). On the variances of asymptotically normal estimators from complex "
    "surveys. International Statistical Review 51(3), 279-292."
)
RAO_SCOTT = (
    "Rao, J. N. K. and Scott, A. J. (1984). On chi-squared tests for multiway contingency "
    "tables with cell proportions estimated from survey data. Annals of Statistics 12(1), "
    "46-60."
)
LUMLEY = "Lumley, T. (2010). Complex Surveys: A Guide to Analysis Using R. Wiley."


@dataclass(frozen=True)
class ObservationalMethod:
    """A cited test of no association for observational designs.

    Bump `version` whenever the guarantee, assumptions, references or limits change.
    """

    key: str
    module: str
    title: str
    version: int
    designs: tuple[str, ...]
    outcome_scales: tuple[str, ...]
    exposure_scales: tuple[str, ...]
    surveys: tuple[str, ...]
    null: str  # the null, in words
    relation: str
    scope: str
    assumptions: tuple[Assumption, ...]
    references: tuple[str, ...]
    covariates: bool = True
    min_total: int = 10
    min_clusters: int | None = None
    limit: str = "the sample size grows"
    grade: str = "cited"
    # How to calculate the test's power, if it can be, and further formulas at other kinds
    # of planning point, such as a measured exposure. Each is versioned on its own, since
    # the guarantee does not depend on them.
    power: PowerFormula | None = field(default=None, repr=False, compare=False)
    more_power: tuple[PowerFormula, ...] = field(default=(), repr=False, compare=False)

    @property
    def formulas(self) -> tuple[PowerFormula, ...]:
        """Every power formula of the test, the main one first."""
        return (*((self.power,) if self.power else ()), *self.more_power)

    def guarantee(self, alpha: Fraction) -> Guarantee:
        return Guarantee("type_I_error", self.relation, alpha, self.null, self.scope, self.limit)

    def to_dict(self) -> dict:
        return {"key": self.key, "version": self.version, "title": self.title}


SIMPLE = ("simple_random",)
COMPLEX = ("simple_random", "stratified", "cluster", "weighted")
BOTH = ("binary", "continuous")

REGRESSION = (
    ObservationalMethod(
        key="logistic_association",
        module="tests.regression",
        title="Wald or likelihood-ratio test of the exposure in a logistic regression",
        version=1,
        designs=("cross_sectional", "cohort", "case_control"),
        outcome_scales=("binary",),
        exposure_scales=BOTH,
        surveys=SIMPLE,
        null="the log odds ratio of the exposure, given the covariates, is 0",
        relation="equals",
        scope="asymptotic",
        assumptions=(
            INDEPENDENT_SAMPLE,
            PRESPECIFIED_MODEL,
            LOGIT_MODEL,
            ENOUGH_OUTCOMES,
            COEFFICIENT_NULL,
        ),
        references=(COX, PRENTICE_PYKE),
        limit="the numbers with and without the outcome grow",
        power=LOGISTIC_GROUPS,
        more_power=(LOGISTIC_TREND,),
    ),
    ObservationalMethod(
        key="conditional_logistic",
        module="tests.regression",
        title="Test of the exposure in a conditional logistic regression of matched pairs",
        version=1,
        designs=("matched_case_control",),
        outcome_scales=("binary",),
        exposure_scales=BOTH,
        surveys=SIMPLE,
        null="the conditional log odds ratio of the exposure, given the covariates, is 0",
        relation="equals",
        scope="asymptotic",
        assumptions=(MATCHED_SETS, PRESPECIFIED_MODEL, LOGIT_MODEL, COEFFICIENT_NULL),
        references=(BRESLOW_DAY,),
        limit="the number of discordant pairs grows",
        power=MATCHED_PAIRS,
    ),
    ObservationalMethod(
        key="poisson_rate_regression",
        module="tests.regression",
        title="Test of the exposure in a Poisson regression of rates with a person-time offset",
        version=1,
        designs=("person_time_cohort",),
        outcome_scales=("binary",),
        exposure_scales=BOTH,
        surveys=SIMPLE,
        null="the log rate ratio of the exposure, given the covariates, is 0",
        relation="equals",
        scope="asymptotic",
        assumptions=(POISSON_COUNTS, PRESPECIFIED_MODEL, LOG_LINEAR_MODEL, COEFFICIENT_NULL),
        references=(BRESLOW_DAY_COHORT,),
        limit="the number of events grows",
        power=POISSON_RATES,
    ),
    ObservationalMethod(
        key="modified_poisson",
        module="tests.regression",
        title="Test of the exposure's risk or prevalence ratio by Poisson regression with a "
        "robust variance",
        version=1,
        designs=("cross_sectional", "cohort"),
        outcome_scales=("binary",),
        exposure_scales=BOTH,
        surveys=SIMPLE,
        null="the log risk or prevalence ratio of the exposure, given the covariates, is 0",
        relation="equals",
        scope="asymptotic",
        assumptions=(
            INDEPENDENT_SAMPLE,
            PRESPECIFIED_MODEL,
            LOG_LINEAR_MODEL,
            ROBUST_VARIANCE,
            COEFFICIENT_NULL,
        ),
        references=(ZOU,),
        power=RISK_RATIO,
    ),
    ObservationalMethod(
        key="linear_association",
        module="tests.regression",
        title="t-test of the exposure's slope in a linear regression",
        version=1,
        designs=("cross_sectional", "cohort"),
        outcome_scales=("continuous",),
        exposure_scales=BOTH,
        surveys=SIMPLE,
        null="the exposure's slope, given the covariates, is 0",
        relation="equals",
        scope="finite_sample",
        assumptions=(INDEPENDENT_SAMPLE, PRESPECIFIED_MODEL, LINEAR_MODEL, COEFFICIENT_NULL),
        references=(SEBER,),
        min_total=4,
        power=SLOPE_POWER,
        more_power=(EXPOSURE_MEANS,),
    ),
)
CORRELATION = (
    ObservationalMethod(
        key="pearson_correlation",
        module="tests.correlation",
        title="t-test of Pearson's correlation coefficient",
        version=1,
        designs=("cross_sectional",),
        outcome_scales=("continuous",),
        exposure_scales=("continuous",),
        surveys=SIMPLE,
        null="the correlation between exposure and outcome is 0",
        relation="equals",
        scope="finite_sample",
        assumptions=(INDEPENDENT_SAMPLE, PRESPECIFIED_MODEL, BIVARIATE_NORMAL),
        references=(FISHER_1915,),
        covariates=False,
        min_total=4,
        power=CORRELATION_POWER,
    ),
    ObservationalMethod(
        key="spearman_correlation",
        module="tests.correlation",
        title="Exact permutation test of Spearman's rank correlation",
        version=1,
        designs=("cross_sectional",),
        outcome_scales=("continuous",),
        exposure_scales=("continuous",),
        surveys=SIMPLE,
        null="exposure and outcome are independent",
        relation="at_most",
        scope="finite_sample",
        assumptions=(INDEPENDENT_SAMPLE, PRESPECIFIED_MODEL, NO_TIES),
        references=(HOLLANDER,),
        covariates=False,
        min_total=4,
        power=SPEARMAN,
    ),
)
SURVEY = (
    ObservationalMethod(
        key="survey_logistic",
        module="tests.survey",
        title="Design-based Wald test of the exposure in a survey-weighted logistic regression",
        version=1,
        designs=("cross_sectional",),
        outcome_scales=("binary",),
        exposure_scales=BOTH,
        surveys=COMPLEX,
        null="the population log odds ratio of the exposure, given the covariates, is 0",
        relation="equals",
        scope="asymptotic",
        assumptions=(DESIGN_BASED, PRESPECIFIED_MODEL, ENOUGH_CLUSTERS, COEFFICIENT_NULL),
        references=(BINDER, LUMLEY),
        min_clusters=20,
        limit="the number of sampled clusters grows",
        power=SURVEY_GROUPS,
        more_power=(SURVEY_TREND,),
    ),
    ObservationalMethod(
        key="survey_linear",
        module="tests.survey",
        title="Design-based Wald test of the exposure in a survey-weighted linear regression",
        version=1,
        designs=("cross_sectional",),
        outcome_scales=("continuous",),
        exposure_scales=BOTH,
        surveys=COMPLEX,
        null="the population slope of the exposure, given the covariates, is 0",
        relation="equals",
        scope="asymptotic",
        assumptions=(DESIGN_BASED, PRESPECIFIED_MODEL, ENOUGH_CLUSTERS, COEFFICIENT_NULL),
        references=(BINDER, LUMLEY),
        min_clusters=20,
        limit="the number of sampled clusters grows",
        power=SURVEY_SLOPE,
        more_power=(SURVEY_MEANS,),
    ),
    ObservationalMethod(
        key="rao_scott_test",
        module="tests.survey",
        title="Rao-Scott adjusted chi-squared test of association in a 2x2 survey table",
        version=1,
        designs=("cross_sectional",),
        outcome_scales=("binary",),
        exposure_scales=("binary",),
        surveys=COMPLEX,
        null="exposure and outcome are independent in the population",
        relation="equals",
        scope="asymptotic",
        assumptions=(DESIGN_BASED, PRESPECIFIED_MODEL, ENOUGH_CLUSTERS),
        references=(RAO_SCOTT, LUMLEY),
        covariates=False,
        min_clusters=20,
        limit="the number of sampled clusters grows",
        power=SURVEY_GROUPS,
    ),
)
MODULE_SUMMARIES = {
    "tests.regression": "Regression tests of the exposure with covariates for observational "
    "studies: logistic (cross-sectional, cohort, case-control), conditional logistic "
    "(matched pairs), Poisson rates (person-time cohorts), modified Poisson for risk and "
    "prevalence ratios, and linear regression for a continuous outcome. Guarantees are cited.",
    "tests.correlation": "Pearson's correlation under bivariate normality and Spearman's rank "
    "correlation by exact permutation, for two continuous variables of a cross-sectional "
    "study. Guarantees are cited.",
    "tests.survey": "Design-based tests for complex survey samples, with strata, clusters or "
    "weights: survey-weighted logistic and linear regression and the Rao-Scott test of a 2x2 "
    "table. Guarantees are cited and need enough sampled clusters.",
}
METHODS = {method.key: method for method in (*REGRESSION, *CORRELATION, *SURVEY)}
MAX_COVARIATES = 20
