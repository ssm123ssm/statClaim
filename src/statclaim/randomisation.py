"""The randomisation test: its design, certificate payload, claims and proof.

Under complete randomisation every split of the units into arms of the declared
sizes is equally likely. If treatment changes no participant's outcome (the
sharp null), the randomisation p-value has Type I error at most alpha, for any
statistic fixed in advance. Lean proves this once
(StatClaim.Modules.Randomisation.typeI); a certificate instantiates it for the
declared numbers of units and checks how many splits there are.

The units are participants, or clusters when whole clusters were randomised.
"""

import re
from dataclasses import dataclass
from fractions import Fraction
from math import comb

from statclaim.fisher import parse_alpha, validate_alpha
from statclaim.planning import _audit

RANDOMISATION_KIND = "statclaim_randomisation_certificate"
TEST_ID = "randomisation"
TEST_VERSION = "0.1.0"
NULL_ID = "no_effect"
# The randomisation schemes an assignment can declare. Only one is supported.
SCHEMES = {
    "complete": "every split of the units into arms of the declared sizes was equally likely",
}
UNITS = ("participant", "cluster")
# Kernel arithmetic on the number of splits stays fast well beyond this.
MAX_UNITS = 10_000

# Bound into certificates and derivations; methods/identify.py recognises each one.
RANDOMISED = (
    "Every split of the randomised units into arms of the declared sizes was equally likely: "
    "complete randomisation, as the assignment declares. With clusters, the units are the "
    "clusters."
)
PRESPECIFIED = "The analysis and its level are chosen before outcomes are observed."
AS_RANDOMISED = (
    "Every randomised unit is analysed, in the arm it was assigned to; the p-value counts "
    "every split, not a random sample of splits."
)
SHARP_NULL = (
    "The error bound is under the null that treatment changes no participant's outcome "
    "(the sharp null), not under equal means or proportions."
)
ASSUMPTIONS = (RANDOMISED, PRESPECIFIED, AS_RANDOMISED, SHARP_NULL)
THEOREMS = ["checked_sizes", "checked_law", "checked_splits", "checked_attainable", "checked_typeI"]
GENERAL_THEOREM = "StatClaim.Modules.Randomisation.typeI"
NULL_STATEMENT = "treatment changes no participant's outcome"


@dataclass(frozen=True)
class RandomisationTest:
    """A randomisation test of the sharp null for one declared assignment."""

    units: int  # randomised units: participants, or clusters
    treated: int  # randomised units in the treatment arm
    alpha: Fraction
    unit: str = "participant"
    module: str = "two_arm_continuous"  # the model's constructor, for the record
    n_control: int = 0  # participants per arm, for the record
    n_treatment: int = 0

    def __post_init__(self):
        validate_alpha(self.alpha)
        if self.unit not in UNITS:
            raise ValueError("Units are participants or clusters.")
        for value in (self.units, self.treated, self.n_control, self.n_treatment):
            if type(value) is not int:
                raise ValueError("Unit and participant counts must be whole numbers.")
        if not 0 < self.treated < self.units <= MAX_UNITS:
            raise ValueError(
                f"Each arm needs at least one unit, and there may be at most {MAX_UNITS} units."
            )
        if self.n_control < self.units - self.treated or self.n_treatment < self.treated:
            raise ValueError("Each arm has at least as many participants as units.")
        if not self.can_reject:
            raise ValueError("The test can never reject at this level.")
        if not isinstance(self.module, str) or not re.fullmatch(r"[a-z_]+", self.module):
            raise ValueError("The model must be named by its constructor.")

    @property
    def splits(self) -> int:
        """How many assignments with these arm sizes there are."""
        return comb(self.units, self.treated)

    @property
    def smallest_p_value(self) -> Fraction:
        """No p-value is smaller: the observed split always counts itself."""
        return Fraction(1, self.splits)

    @property
    def can_reject(self) -> bool:
        return self.smallest_p_value <= self.alpha

    @property
    def unit_words(self) -> str:
        return f"{self.unit}s"

    def describe(self) -> str:
        plural = self.unit_words
        return (
            f"{self.units} {plural}, {self.treated} treated and {self.units - self.treated} control"
        )


def splits_needed(alpha: Fraction) -> int:
    """The fewest splits that let a test at this level reject."""
    return -(-alpha.denominator // alpha.numerator) if alpha > 0 else 0


def randomisation_payload(test: RandomisationTest) -> dict:
    return {
        "schema_version": 1,
        "scope": "randomisation_test",
        "design": {
            "module": test.module,
            "unit": test.unit,
            "units": test.units,
            "treated_units": test.treated,
            "n_control": test.n_control,
            "n_treatment": test.n_treatment,
            "randomisation": "complete",
            "stopping": "fixed",
        },
        "analysis": {
            "test": TEST_ID,
            "test_version": TEST_VERSION,
            "null": NULL_ID,
            "alpha": str(test.alpha),
            # A string: the count can have more digits than a JSON reader keeps.
            "splits": str(test.splits),
        },
    }


def parse_randomisation_payload(payload: dict) -> RandomisationTest:
    design, analysis = payload["design"], payload["analysis"]
    test = RandomisationTest(
        design["units"],
        design["treated_units"],
        parse_alpha(analysis["alpha"]),
        design["unit"],
        design["module"],
        design["n_control"],
        design["n_treatment"],
    )
    if payload != randomisation_payload(test):
        raise ValueError("Bound randomisation-test inputs are inconsistent.")
    return test


def randomisation_claims(test: RandomisationTest) -> list[str]:
    plural = test.unit_words
    return [
        f"Under complete randomisation of {test.describe()}, the {test.splits} possible splits "
        "are equally likely, and that uniform law is a probability law.",
        f"No p-value is below 1/{test.splits}, which does not exceed the level {test.alpha}, "
        "so the test can reject.",
        f"For every test statistic fixed in advance, the randomisation p-value, the share of "
        "splits whose statistic is at least the observed one, is at most "
        f"{test.alpha} with probability at most {test.alpha} whenever {NULL_STATEMENT}.",
        f"The bound holds whatever the outcomes are and however the {plural} affect one "
        "another; no distribution is assumed.",
    ]


def render_randomisation_proof(test: RandomisationTest, input_sha256: str) -> str:
    """Only validated integers and one rational level enter the template."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    numerator, denominator = test.alpha.as_integer_ratio()
    units, treated, splits = test.units, test.treated, test.splits
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- Units are {test.unit_words}. The theorem covers every statistic and all potential
-- outcomes under the sharp null; nothing here depends on observed data.
set_option maxRecDepth 100000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

def units : ℕ := {units}
def treatedUnits : ℕ := {treated}
def declaredLevel : SignificanceLevel :=
  ⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩

theorem checked_sizes : units = {units} ∧ treatedUnits = {treated} ∧ 0 < treatedUnits ∧
    treatedUnits < units := by decide

theorem checked_law : Randomisation.law units treatedUnits Set.univ = 1 :=
  Randomisation.law_univ units treatedUnits (by decide)

theorem checked_splits : (Randomisation.splits units treatedUnits).card = {splits} := by
  rw [Randomisation.splits_card, Nat.choose_eq_factorial_div_factorial (by decide)]
  decide +kernel

-- No p-value is below one over the number of splits (Randomisation.pValue_ge).
theorem checked_attainable : (1 : ℚ) / {splits} ≤ declaredLevel.value := by
  norm_num [declaredLevel]

theorem checked_typeI {{Value : Type}} {{Statistic : Type}} [LinearOrder Statistic]
    (statistic : Randomisation.Assignment units → (Fin units → Value) → Statistic)
    (outcomes : Randomisation.PotentialOutcomes units Value)
    (sharp : Randomisation.SharpNull outcomes) :
    (Randomisation.law units treatedUnits).real
        (Randomisation.rejection units treatedUnits statistic outcomes declaredLevel.value) ≤
      (declaredLevel.value : ℝ) :=
  Randomisation.typeI_of_level units treatedUnits statistic outcomes sharp
    declaredLevel.value declaredLevel.nonnegative

end StatClaimCertificate
{_audit(THEOREMS, input_sha256)}"""
