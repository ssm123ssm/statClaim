"""Mixed models for repeated measures. Guarantees are cited, not proved."""

from statclaim.methods.assumptions import (
    APPROXIMATELY_NORMAL_ESTIMATE,
    CORRECT_MEAN_MODEL,
    COVARIANCE_STRUCTURE,
    FIXED_SIZES,
    INDEPENDENT_PARTICIPANTS,
    MISSING_AT_RANDOM,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import CitedMethod, MethodModule

LAIRD_WARE = (
    "Laird, N. M. and Ware, J. H. (1982). Random-effects models for longitudinal data. "
    "Biometrics 38(4), 963-974."
)
KENWARD_ROGER = (
    "Kenward, M. G. and Roger, J. H. (1997). Small sample inference for fixed effects from "
    "restricted maximum likelihood. Biometrics 53(3), 983-997."
)
MALLINCKRODT = (
    "Mallinckrodt, C. H., Lane, P. W., Schnell, D., Peng, Y. and Mancuso, J. P. (2008). "
    "Recommendations for the primary analysis of continuous endpoints in longitudinal "
    "clinical trials. Drug Information Journal 42(4), 303-319."
)

_COMMON = dict(
    module="tests.mixed_model",
    version=1,
    outcome="continuous",
    scope="asymptotic",
    limit="the number of participants grows",
    assumptions=(
        INDEPENDENT_PARTICIPANTS,
        FIXED_SIZES,
        SINGLE_ANALYSIS,
        MISSING_AT_RANDOM,
        CORRECT_MEAN_MODEL,
        COVARIANCE_STRUCTURE,
        APPROXIMATELY_NORMAL_ESTIMATE,
    ),
    references=(LAIRD_WARE, KENWARD_ROGER, MALLINCKRODT),
    min_per_arm=2,
    min_total=4,
)

MODULE = MethodModule(
    "tests.mixed_model",
    "A test of a treatment contrast from a mixed model for repeated measures, such as the "
    "mean difference over all visits. The arm means in the null are the means of that "
    "contrast. The compiler checks the null and the sampling plan. The Type I guarantee is "
    "cited and is a large-sample approximation that also rests on the missing-data and "
    "model assumptions listed with each result.",
    (
        CitedMethod(
            key="mmrm_test",
            title="Two-sided test of a treatment contrast in a mixed model for repeated measures",
            null="equal_means",
            relation="equals",
            **_COMMON,
        ),
        CitedMethod(
            key="mmrm_test_one_sided",
            title="One-sided test of a treatment contrast in a mixed model for repeated measures",
            null="mean_difference_at_most",
            relation="at_most",
            **_COMMON,
        ),
    ),
)
