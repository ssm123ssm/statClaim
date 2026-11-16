"""Contract-tier methods: guarantees cited from the literature, not proved in Lean.

Each method states what it claims, whether the claim is a finite-sample bound or a
large-sample approximation, the assumptions it rests on and where it is published.
The compiler checks that a declared study fits the contract. Nothing here is
machine-checked, and a cited guarantee never receives a verified status.
"""

from dataclasses import dataclass
from fractions import Fraction

STUDENT = "Student (1908). The probable error of a mean. Biometrika 6(1), 1-25."
FISHER = "Fisher, R. A. (1925). Applications of 'Student's' distribution. Metron 5, 90-104."
WELCH = (
    "Welch, B. L. (1947). The generalization of 'Student's' problem when several different "
    "population variances are involved. Biometrika 34(1-2), 28-35."
)
SATTERTHWAITE = (
    "Satterthwaite, F. E. (1946). An approximate distribution of estimates of variance "
    "components. Biometrics Bulletin 2(6), 110-114."
)
LEHMANN_ROMANO = (
    "Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses, 3rd ed. "
    "Springer. Chapters 5 and 11."
)

SAMPLING = (
    "Observations are independent within and between the two arms.",
    "Arm sizes are fixed before observing outcomes, and the test is run once.",
)


@dataclass(frozen=True)
class CitedMethod:
    key: str
    title: str
    sided: str  # "two_sided" or "greater"
    guarantee: str  # a key of language.GUARANTEE_SCOPES
    assumptions: tuple[str, ...]
    references: tuple[str, ...]
    min_per_arm: int
    min_total: int

    def null(self, value: Fraction) -> str:
        if self.sided == "two_sided":
            return "the two arm means are equal"
        return f"the treatment mean exceeds the control mean by at most {value}"

    def property(self, alpha: Fraction, value: Fraction) -> str:
        """The cited statement. Exact and approximate claims are worded differently."""
        null = self.null(value)
        if self.guarantee == "finite_sample":
            relation = "equals" if self.sided == "two_sided" else "is at most"
            return f"Null rejection probability {relation} {alpha} whenever {null}."
        limit = "approaches" if self.sided == "two_sided" else "is at most"
        return (
            f"Null rejection probability {limit} {alpha} in the limit as both arm sizes grow, "
            f"whenever {null}. No bound is claimed at the declared arm sizes."
        )


_NORMAL = "Outcomes in each arm are normally distributed."
_FINITE = "Outcomes in each arm are identically distributed with finite, positive variance."
_STUDENT = dict(
    guarantee="finite_sample",
    assumptions=(*SAMPLING, _NORMAL, "The two arms have the same variance."),
    references=(STUDENT, FISHER, LEHMANN_ROMANO),
    min_per_arm=1,
    min_total=3,
)
_WELCH = dict(
    guarantee="asymptotic",
    assumptions=(*SAMPLING, _FINITE),
    references=(WELCH, SATTERTHWAITE, LEHMANN_ROMANO),
    min_per_arm=2,
    min_total=4,
)
METHODS = {
    method.key: method
    for method in (
        CitedMethod("t_test", "Two-sided pooled-variance t-test", "two_sided", **_STUDENT),
        CitedMethod("t_test_one_sided", "One-sided pooled-variance t-test", "greater", **_STUDENT),
        CitedMethod("welch_test", "Two-sided Welch t-test", "two_sided", **_WELCH),
        CitedMethod("welch_test_one_sided", "One-sided Welch t-test", "greater", **_WELCH),
    )
}
