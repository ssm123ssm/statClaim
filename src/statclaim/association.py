"""Fisher's exact test of no association in an observational 2×2 study.

The design decides what the sampling fixed. A cohort study fixes how many exposed and
unexposed participants are followed, and a case-control study how many cases and
controls are sampled: the table then holds two independent binomial counts, and Fisher's
theorem applies with the groups in place of arms. A cross-sectional study, or a cohort
that does not fix how many are exposed, fixes only the total: given the number exposed
the test has level alpha, so averaged over it the test does too. Lean proves both once
(StatClaim.Modules.Association); a certificate instantiates them for the declared sizes.

Exposure was not assigned, so a bound on Type I error concerns association only.
"""

import re
from dataclasses import dataclass
from fractions import Fraction

from statclaim.fisher import parse_alpha, validate_alpha
from statclaim.planning import _audit
from statclaim.randomisation import PRESPECIFIED

ASSOCIATION_KIND = "statclaim_association_certificate"
TEST_ID = "fisher_exact"
TEST_VERSION = "0.1.0"
NULL_ID = "no_association"
DESIGNS = ("cross_sectional", "cohort", "case_control")
# Participants in one study. Certificates only compare these sizes with zero.
MAX_PARTICIPANTS = 1_000_000
NAME = re.compile(r"[A-Za-z][A-Za-z0-9 _'()-]{0,59}")

# The null of each design, as a formula and in words. All say: odds ratio 1.
NULL_STATEMENTS = {
    "cohort": "risk_exposed = risk_unexposed",
    "case_control": "exposure_cases = exposure_controls",
    "cross_sectional": "prevalence_exposed = prevalence_unexposed",
}

# Bound into certificates and derivations; methods/identify.py recognises each one.
COHORT_GROUPS = (
    "The exposed and unexposed groups were sampled separately, in the declared numbers, "
    "before outcomes occurred."
)
CASE_CONTROL_GROUPS = (
    "Cases and controls were sampled separately, in the declared numbers, without regard "
    "to exposure."
)
RANDOM_SAMPLE = (
    "Participants were sampled independently from one population, in the declared number; "
    "how many are exposed is not fixed."
)
INDEPENDENT_OUTCOMES = (
    "Participants' outcomes are independent of one another, and within each group everyone "
    "has the same probability of the outcome."
)
INDEPENDENT_EXPOSURES = (
    "Participants' exposures are independent of one another, and among cases, as among "
    "controls, everyone has the same probability of having been exposed."
)
SOURCE_POPULATION = (
    "Controls come from the population that gave rise to the cases; otherwise the null "
    "concerns the groups sampled, not that population."
)
COHORT_NULL = (
    "The error bound is under the null of no association: the same risk of the outcome with "
    "and without exposure, for every common risk."
)
CASE_CONTROL_NULL = (
    "The error bound is under the null of no association: exposure as common among cases as "
    "among controls, an odds ratio of 1."
)
CROSS_SECTIONAL_NULL = (
    "The error bound is under the null of no association: exposure and outcome independent, "
    "so the outcome is as common with exposure as without it."
)
NOT_CAUSAL = (
    "The bound concerns association, not an effect of the exposure: exposure was not "
    "assigned, so confounding is not excluded."
)
GROUP_THEOREMS = ["checked_sizes", "checked_typeI"]
MIXTURE_THEOREMS = ["checked_size", "checked_law", "checked_typeI"]
GROUP_THEOREM = "StatClaim.Modules.Association.groups_typeI_le_alpha"
MIXTURE_THEOREM = "StatClaim.Modules.Association.mixture_typeI_le_alpha"


def null_statement(design: str) -> str:
    return NULL_STATEMENTS[design]


@dataclass(frozen=True)
class AssociationTest:
    """Fisher's exact test of no association for one declared observational study.

    `groups` is (unexposed, exposed) for a cohort and (controls, cases) for a case-control
    study, when the design fixes them; otherwise `n` is the total.
    """

    design: str
    alpha: Fraction
    groups: tuple[int, int] | None = None
    n: int | None = None
    exposure: str = "exposure"
    outcome: str = "outcome"

    def __post_init__(self):
        validate_alpha(self.alpha)
        if self.design not in DESIGNS:
            raise ValueError(f"Unknown observational design {self.design!r}.")
        if (self.groups is None) == (self.n is None):
            raise ValueError("Declare either the two group sizes or the total, not both.")
        if self.design == "case_control" and self.groups is None:
            raise ValueError("A case-control study fixes the numbers of cases and controls.")
        if self.design == "cross_sectional" and self.n is None:
            raise ValueError("A cross-sectional study fixes only the total.")
        sizes = self.groups if self.groups is not None else (self.n,)
        if len(sizes) not in (1, 2) or any(type(s) is not int or s < 1 for s in sizes):
            raise ValueError("Each declared size must be a positive whole number.")
        if sum(sizes) > MAX_PARTICIPANTS:
            raise ValueError(f"At most {MAX_PARTICIPANTS} participants are supported.")
        for name in (self.exposure, self.outcome):
            if not isinstance(name, str) or not NAME.fullmatch(name):
                raise ValueError("Exposure and outcome names are short plain words.")

    @property
    def fixed_groups(self) -> bool:
        return self.groups is not None

    @property
    def total(self) -> int:
        return sum(self.groups) if self.groups is not None else self.n

    def describe(self) -> str:
        if self.design == "case_control":
            controls, cases = self.groups
            return f"{cases} cases of {self.outcome} and {controls} controls"
        if self.groups is not None:
            unexposed, exposed = self.groups
            return f"{exposed} exposed to {self.exposure} and {unexposed} not"
        kind = "cross-sectional sample" if self.design == "cross_sectional" else "cohort"
        return f"a {kind} of {self.n}, with the number exposed to {self.exposure} not fixed"


def association_payload(test: AssociationTest) -> dict:
    design = {
        "kind": test.design,
        "exposure": test.exposure,
        "outcome": test.outcome,
        "stopping": "fixed",
    }
    if test.groups is not None:
        design["groups"] = list(test.groups)
    else:
        design["n"] = test.n
    return {
        "schema_version": 1,
        "scope": "association_test",
        "design": design,
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": NULL_ID,
            "alpha": str(test.alpha),
        },
    }


def parse_association_payload(payload: dict) -> AssociationTest:
    design, analysis = payload["design"], payload["analysis"]
    groups = design.get("groups")
    test = AssociationTest(
        design["kind"],
        parse_alpha(analysis["alpha"]),
        tuple(groups) if isinstance(groups, list) else groups,
        design.get("n"),
        design["exposure"],
        design["outcome"],
    )
    if payload != association_payload(test):
        raise ValueError("Bound association-test inputs are inconsistent.")
    return test


def association_assumptions(test: AssociationTest) -> tuple[str, ...]:
    """How the study sampled, independence, the prespecified analysis and the null."""
    if test.design == "case_control":
        return (
            CASE_CONTROL_GROUPS,
            INDEPENDENT_EXPOSURES,
            SOURCE_POPULATION,
            PRESPECIFIED,
            CASE_CONTROL_NULL,
        )
    sampled = COHORT_GROUPS if test.groups is not None else RANDOM_SAMPLE
    null = CROSS_SECTIONAL_NULL if test.design == "cross_sectional" else COHORT_NULL
    return (sampled, INDEPENDENT_OUTCOMES, PRESPECIFIED, null)


def association_theorems(test: AssociationTest) -> list[str]:
    return GROUP_THEOREMS if test.fixed_groups else MIXTURE_THEOREMS


def general_theorem(test: AssociationTest) -> str:
    return GROUP_THEOREM if test.fixed_groups else MIXTURE_THEOREM


def null_words(test: AssociationTest) -> str:
    exposure, outcome = test.exposure, test.outcome
    if test.design == "case_control":
        return f"{exposure} is as common among cases of {outcome} as among controls (odds ratio 1)"
    noun = "prevalence" if test.design == "cross_sectional" else "risk"
    return f"the {noun} of {outcome} is the same with and without {exposure}"


def association_claims(test: AssociationTest) -> list[str]:
    alpha, exposure, outcome = test.alpha, test.exposure, test.outcome
    test_words = f"Fisher's exact test of no association between {exposure} and {outcome}"
    if test.design == "case_control":
        controls, cases = test.groups
        return [
            f"The numbers of cases ({cases}) and controls ({controls}) that the design fixes "
            "are Lean checked.",
            f"{test_words} has Type I error at most {alpha} whenever {null_words(test)}, for "
            "every common probability of exposure in [0, 1].",
        ]
    if test.groups is not None:
        unexposed, exposed = test.groups
        return [
            f"The group sizes that the cohort fixes, {exposed} exposed to {exposure} and "
            f"{unexposed} not, are Lean checked.",
            f"{test_words} has Type I error at most {alpha} whenever {null_words(test)}, for "
            f"every common risk in [0, 1].",
        ]
    return [
        f"The sample size, {test.n}, is Lean checked; how many are exposed is not fixed, and "
        "the law of the table under no association is a probability law.",
        f"Given the number exposed, {test_words} rejects with probability at most {alpha}; "
        f"averaged over the number exposed, its Type I error is at most {alpha} whenever "
        f"{null_words(test)}, for every probability of exposure and every common probability "
        f"of {outcome} in [0, 1].",
    ]


def render_association_proof(test: AssociationTest, input_sha256: str) -> str:
    """Only validated integers and one rational level enter the template; the exposure and
    outcome names never do."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    numerator, denominator = test.alpha.as_integer_ratio()
    header = f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- An observational {test.design.replace("_", "-")} study. The theorem covers every probability
-- under no association; nothing here depends on observed data.
namespace StatClaimCertificate
open StatClaim StatClaim.Modules

def declaredLevel : SignificanceLevel :=
  ⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩
"""
    if test.groups is not None:
        first, second = test.groups
        body = f"""
-- The two groups the design fixes: (unexposed, exposed) or (controls, cases).
def firstGroup : ℕ := {first}
def secondGroup : ℕ := {second}

theorem checked_sizes : firstGroup = {first} ∧ secondGroup = {second} ∧ 0 < firstGroup ∧
    0 < secondGroup := by decide

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw firstGroup secondGroup p).real
        (fisherRejectionRegionAt firstGroup secondGroup declaredLevel.value) ≤
      (declaredLevel.value : ℝ) :=
  Association.groups_typeI_le_alpha firstGroup secondGroup p declaredLevel.value
    declaredLevel.nonnegative
"""
    else:
        body = f"""
-- Only the total is fixed; the number exposed is binomial.
def sampleSize : ℕ := {test.n}

theorem checked_size : sampleSize = {test.n} ∧ 0 < sampleSize := by decide

theorem checked_law (q p : unitInterval) :
    Association.mixtureLaw sampleSize q p Set.univ = 1 :=
  Association.mixtureLaw_univ sampleSize q p

theorem checked_typeI (q p : unitInterval) :
    (Association.mixtureLaw sampleSize q p).real
        (Association.mixtureRejection sampleSize declaredLevel.value) ≤
      (declaredLevel.value : ℝ) :=
  Association.mixture_typeI_le_alpha sampleSize q p declaredLevel.value
    declaredLevel.nonnegative
"""
    return f"""{header}{body}
end StatClaimCertificate
{_audit(association_theorems(test), input_sha256)}"""
