"""The randomisation test: its design, certificate payload, claims and proof.

Under complete randomisation every split of the units into arms of the declared
sizes is equally likely. Under stratified or blocked randomisation the same holds
within each stratum or block, independently between them. If treatment changes
no participant's outcome (the sharp null), the randomisation p-value has Type I
error at most alpha, for any statistic fixed in advance. Lean proves this once
(StatClaim.Modules.Randomisation.typeI and groupedTypeI_of_level); a certificate
instantiates it for the declared units and checks how many assignments there are.

The units are participants, or clusters when whole clusters were randomised.
"""

import re
from dataclasses import dataclass
from fractions import Fraction
from math import comb, prod

from statclaim.fisher import validate_alpha
from statclaim.lean_translation import statements as S
from statclaim.lean_translation.statements import CERTIFICATE as C
from statclaim.planning import _audit

TEST_ID = "randomisation"
TEST_VERSION = "0.1.0"
NULL_ID = "no_effect"
# The randomisation schemes an assignment can declare.
SCHEMES = {
    "complete": "every split of the units into arms of the declared sizes was equally likely",
    "stratified": "within each declared stratum, every split into its declared numbers per arm "
    "was equally likely, independently between strata",
    "blocked": "the units were randomised in blocks of block_size, each with its stratum's "
    "allocation, every split within a block equally likely, independently between blocks",
}
UNITS = ("participant", "cluster")
# Kernel arithmetic on the number of splits stays fast well beyond this.
MAX_UNITS = 10_000
# Strata or blocks, each randomised on its own. A certificate lists every one.
MAX_GROUPS = 1_000
# Assignments drawn for a Monte Carlo p-value. Nothing enumerates them.
MAX_DRAWS = 10_000_000

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
AS_DRAWN = (
    "Every randomised unit is analysed, in the arm it was assigned to; the p-value compares "
    "the observed assignment with the declared number of assignments drawn independently and "
    "uniformly at random, with replacement, and counts the observed one among them."
)
SHARP_NULL = (
    "The error bound is under the null that treatment changes no participant's outcome "
    "(the sharp null), not under equal means or proportions."
)
GROUPED = (
    "Within each stratum or block, every split of its randomised units into its declared "
    "numbers per arm was equally likely, independently between strata and blocks, as the "
    "assignment declares. With clusters, the units are the clusters."
)
# With population="randomised" the file states who is analysed, so AS_RANDOMISED and
# AS_DRAWN split into that declaration and what is still assumed: how the p-value counts.
POPULATION = (
    "Every randomised unit is analysed, in the arm it was assigned to: the randomised "
    "population, as the assignment declares."
)
COUNTS_EVERY_SPLIT = "The p-value counts every split, not a random sample of splits."
COUNTS_DRAWS = (
    "The p-value compares the observed assignment with the declared number of assignments "
    "drawn independently and uniformly at random, with replacement, and counts the observed "
    "one among them."
)
ASSUMPTIONS = (RANDOMISED, PRESPECIFIED, AS_RANDOMISED, SHARP_NULL)
THEOREMS = ["checked_sizes", "checked_law", "checked_splits", "checked_attainable", "checked_typeI"]
GROUPED_THEOREMS = [
    "checked_groups",
    "checked_law",
    "checked_splits",
    "checked_attainable",
    "checked_typeI",
]
GENERAL_THEOREM = "StatClaim.Modules.Randomisation.typeI"
GROUPED_GENERAL_THEOREM = "StatClaim.Modules.Randomisation.groupedTypeI_of_level"
DRAWN_GENERAL_THEOREM = "StatClaim.Modules.Randomisation.drawnRejection_le_of_level"
NULL_STATEMENT = "treatment changes no participant's outcome"


def groups_of(
    units: int,
    treated: int,
    scheme: str,
    strata: tuple[tuple[int, int], ...] = (),
    block_size: int | None = None,
) -> tuple[tuple[int, int], ...]:
    """The groups randomised independently, as (units, treated). Raises ValueError saying why
    the declaration does not describe a randomisation. Strata are (control, treatment)."""
    if scheme == "complete":
        if strata or block_size is not None:
            raise ValueError(
                'Complete randomisation has no strata or blocks: use randomisation="stratified" '
                'or "blocked".'
            )
        return ((units, treated),)
    if scheme == "stratified":
        if block_size is not None:
            raise ValueError('Blocks within strata are declared with randomisation="blocked".')
        if len(strata) < 2:
            raise ValueError("Stratified randomisation needs at least two strata.")
        parts = strata
    elif scheme == "blocked":
        if block_size is None or block_size < 2:
            raise ValueError("Blocked randomisation needs block_size, at least 2.")
        parts = strata or ((units - treated, treated),)
    else:
        raise ValueError(f"Unknown randomisation {scheme!r}.")
    if any(
        type(c) is not int or type(t) is not int or c < 0 or t < 0 or c + t == 0 for c, t in parts
    ):
        raise ValueError("Each stratum needs a whole number of units per arm, at least one in all.")
    if sum(c for c, _ in parts) != units - treated or sum(t for _, t in parts) != treated:
        raise ValueError(
            f"The strata add up to {sum(c for c, _ in parts)} control and "
            f"{sum(t for _, t in parts)} treatment units, but the assignment randomises "
            f"{units - treated} and {treated}."
        )
    if scheme == "stratified":
        groups = tuple((c + t, t) for c, t in parts)
    else:
        found: list[tuple[int, int]] = []
        for c, t in parts:
            size = c + t
            if size % block_size or (t * block_size) % size:
                where = "the design" if not strata else "a stratum"
                raise ValueError(
                    f"The {c} control and {t} treatment units of {where} cannot be split into "
                    f"whole blocks of {block_size} with the same allocation in every block."
                )
            found += [(block_size, t * block_size // size)] * (size // block_size)
        groups = tuple(found)
    if len(groups) > MAX_GROUPS:
        raise ValueError(f"At most {MAX_GROUPS} strata or blocks are supported.")
    return groups


def count_splits(groups: tuple[tuple[int, int], ...]) -> int:
    """Equally likely assignments: the product of each group's splits."""
    return prod(comb(size, treated) for size, treated in groups)


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
    scheme: str = "complete"
    strata: tuple[tuple[int, int], ...] = ()  # (control, treatment) units per stratum
    block_size: int | None = None
    # Assignments drawn at random for a Monte Carlo p-value; None when every one is counted.
    draws: int | None = None
    # "randomised" when the assignment declares that everyone randomised is analysed.
    population: str | None = None

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
        groups_of(self.units, self.treated, self.scheme, self.strata, self.block_size)
        if self.draws is not None and not (
            type(self.draws) is int and 1 <= self.draws <= MAX_DRAWS
        ):
            raise ValueError(f"draws must be a whole number from 1 to {MAX_DRAWS}.")
        if self.population not in (None, "randomised"):
            raise ValueError(
                "A randomisation test analyses every randomised unit, in the arm it was "
                "assigned to."
            )
        if not self.can_reject:
            raise ValueError("The test can never reject at this level.")
        if not isinstance(self.module, str) or not re.fullmatch(r"[a-z_]+", self.module):
            raise ValueError("The model must be named by its constructor.")

    @property
    def groups(self) -> tuple[tuple[int, int], ...]:
        return groups_of(self.units, self.treated, self.scheme, self.strata, self.block_size)

    @property
    def grouped(self) -> bool:
        return self.scheme != "complete"

    @property
    def splits(self) -> int:
        """How many equally likely assignments there are."""
        return count_splits(self.groups)

    @property
    def smallest_p_value(self) -> Fraction:
        """No p-value is smaller: the observed assignment always counts itself."""
        return Fraction(1, self.draws + 1 if self.draws else self.splits)

    @property
    def can_reject(self) -> bool:
        return self.smallest_p_value <= self.alpha

    @property
    def unit_words(self) -> str:
        return f"{self.unit}s"

    def describe(self) -> str:
        plural = self.unit_words
        text = (
            f"{self.units} {plural}, {self.treated} treated and {self.units - self.treated} control"
        )
        if self.scheme == "stratified":
            return f"{text}, in {len(self.strata)} strata"
        if self.scheme == "blocked":
            text += f", in {len(self.groups)} blocks of {self.block_size}"
            return text + (f" within {len(self.strata)} strata" if self.strata else "")
        return text


def splits_needed(alpha: Fraction) -> int:
    """The fewest splits that let a test at this level reject."""
    return -(-alpha.denominator // alpha.numerator) if alpha > 0 else 0


def randomisation_assumptions(test: RandomisationTest) -> tuple[str, ...]:
    """How units were randomised, the prespecified analysis, who is analysed and how the
    p-value counts, and the null. They depend only on the scheme, draws and population."""
    randomised = GROUPED if test.grouped else RANDOMISED
    if test.population == "randomised":
        counted = COUNTS_DRAWS if test.draws else COUNTS_EVERY_SPLIT
        return (randomised, PRESPECIFIED, POPULATION, counted, SHARP_NULL)
    return (randomised, PRESPECIFIED, AS_DRAWN if test.draws else AS_RANDOMISED, SHARP_NULL)


def general_theorem(test: RandomisationTest) -> str:
    if test.draws:
        return DRAWN_GENERAL_THEOREM
    return GROUPED_GENERAL_THEOREM if test.grouped else GENERAL_THEOREM


def render_randomisation_proof(test: RandomisationTest, input_sha256: str) -> str:
    """Only validated integers and one rational level enter the template."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    if test.grouped:
        return _render_grouped_proof(test, input_sha256)
    numerator, denominator = test.alpha.as_integer_ratio()
    units, treated, splits = test.units, test.treated, test.splits
    if test.draws:
        claimed = S.randomisation_typeI(
            C, "declaredLevel.value", "draws", units="units", treated="treatedUnits"
        )
        tail = _drawn_tail(test.draws, claimed, "Randomisation.splits units treatedUnits")
    else:
        tail = f"""-- No p-value is below one over the number of splits (Randomisation.pValue_ge).
theorem checked_attainable : (1 : ℚ) / {splits} ≤ declaredLevel.value := by
  norm_num [declaredLevel]

{S.randomisation_typeI(C, "declaredLevel.value", units="units", treated="treatedUnits").header()} :=
  Randomisation.typeI_of_level units treatedUnits statistic outcomes sharp
    declaredLevel.value declaredLevel.nonnegative
"""
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

{tail}
end StatClaimCertificate
{_audit(THEOREMS, input_sha256)}"""


def _render_grouped_proof(test: RandomisationTest, input_sha256: str) -> str:
    numerator, denominator = test.alpha.as_integer_ratio()
    groups = ", ".join(f"({size}, {treated})" for size, treated in test.groups)
    splits = test.splits
    if test.draws:
        claimed = S.randomisation_typeI(C, "declaredLevel.value", "draws", groups="groups")
        tail = _drawn_tail(test.draws, claimed, "Randomisation.groupedSplits groups")
    else:
        tail = (
            (
                "-- The observed assignment always counts itself, so no p-value is below one over "
                "the count.\n"
            )
            + f"""theorem checked_attainable : (1 : ℚ) / {splits} ≤ declaredLevel.value := by
  norm_num [declaredLevel]

{S.randomisation_typeI(C, "declaredLevel.value", groups="groups").header()} :=
  Randomisation.groupedTypeI_of_level groups statistic outcomes sharp declaredLevel.value
    declaredLevel.nonnegative
"""
        )
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- {test.scheme.capitalize()} randomisation of {test.unit_words}: each group is a stratum or block,
-- given as (units, treated). The theorem covers every statistic and every record under
-- the sharp null; nothing here depends on observed data.
set_option maxRecDepth 100000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

def groups : Randomisation.Groups := [{groups}]
def declaredLevel : SignificanceLevel :=
  ⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩

theorem checked_groups : ∀ group ∈ groups, group.2 ≤ group.1 := by decide

theorem checked_law : Randomisation.groupedLaw groups Set.univ = 1 :=
  Randomisation.groupedLaw_univ groups checked_groups

theorem checked_splits : (Randomisation.groupedSplits groups).card = {splits} := by
  rw [Randomisation.groupedSplits_card groups checked_groups]
  decide +kernel

{tail}
end StatClaimCertificate
{_audit(GROUPED_THEOREMS, input_sha256)}"""


def _drawn_tail(draws: int, claimed: S.Theorem, support: str) -> str:
    """The attainable-level and Type I theorems of a Monte Carlo p-value with `draws` draws.
    The law is the product of independent uniform draws (Randomisation.pi_uniform)."""
    return f"""def draws : ℕ := {draws}

-- No Monte Carlo p-value is below one over the draws plus one (Randomisation.drawnShare_ge).
theorem checked_attainable : (1 : ℚ) / (draws + 1) ≤ declaredLevel.value := by
  norm_num [draws, declaredLevel]

-- The observed assignment and the draws are independent, each with the design's law.
{claimed.header()} :=
  Randomisation.drawnRejection_le_of_level ({support}) draws statistic outcomes sharp
    declaredLevel.value declaredLevel.nonnegative
"""
