module

public import StatClaim.Modules.Association
public import StatClaim.Modules.FisherPower

/-!
Exact power of Fisher's test of no association in an observational study whose design
fixes two group sizes: the unexposed and exposed groups of a cohort, or the controls and
cases of a case-control study. The table then holds two independent binomial counts with
their own probabilities (`productBinomial`), and the test rejects on Fisher's region
(`fisherRejectionRegionAt`), the same objects as `Association.groups_typeI_le_alpha`.

At rational probabilities the rejection probability is a ratio of natural numbers
(`rejection_probability`), so one comparison checked by the kernel bounds the power at a
planning point (`power_of_check`), and another shows that a candidate falls short
(`power_lt_of_fails`); a search proves this for every smaller candidate. Power at one
point says nothing about other points, or about cause.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.AssociationPower

open MeasureTheory FisherPower

/-- Fisher's region, decided by the natural-number rule `checkedReject`. -/
theorem rejection_probability (first second levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (alpha : ℚ) (level_eq : alpha = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e) :
    (productBinomial first second (ratPoint a d le₁ positive₁) (ratPoint b e le₂ positive₂)).real
        (fisherRejectionRegionAt first second alpha) =
      (rejectionNumerator first second a d b e (checkedReject first second levelNum levelDen) : ℝ) /
        (rejectionDenominator first second d e : ℝ) := by
  rw [rejectionDenominator_cast]
  refine productBinomial_real_ratPoint _ _ a d b e le₁ positive₁ le₂ positive₂ _ _ ?_
  intro x x_le y y_le
  rw [checkedReject_iff _ _ _ _ _ _ levelDen_pos x_le y_le, ← level_eq]
  simp [fisherRejectionRegionAt, binomialCountSupport, x_le, y_le]

/-- Power at a rational planning point, from one natural-number check. -/
theorem power_of_check (first second levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (alpha : ℚ) (level_eq : alpha = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * rejectionDenominator first second d e ≤
      rejectionNumerator first second a d b e (checkedReject first second levelNum levelDen) *
        boundDen) :
    (boundNum : ℝ) / boundDen ≤
      (productBinomial first second (ratPoint a d le₁ positive₁)
        (ratPoint b e le₂ positive₂)).real (fisherRejectionRegionAt first second alpha) := by
  rw [rejection_probability first second levelNum levelDen levelDen_pos alpha level_eq]
  exact le_ratio_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos check

/-- One candidate design falls short of the power bound, checked with supplied thresholds
that the kernel validates. A search proves this for each smaller candidate as a separate
theorem, so the kernel never holds the arithmetic of every candidate at once. -/
def FailsHinted (first second levelNum levelDen a d b e boundNum boundDen : ℕ)
    (cuts nexts : List ℕ) : Prop :=
  HintsValid first second levelNum levelDen cuts nexts ∧
    rejectionNumerator first second a d b e (hintReject first second cuts) * boundDen <
      boundNum * rejectionDenominator first second d e

instance (first second levelNum levelDen a d b e boundNum boundDen : ℕ) (cuts nexts : List ℕ) :
    Decidable (FailsHinted first second levelNum levelDen a d b e boundNum boundDen cuts nexts) := by
  unfold FailsHinted
  infer_instance

/-- A candidate that fails the check has power below the bound at the planning point. -/
theorem power_lt_of_fails (first second levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (alpha : ℚ) (level_eq : alpha = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen) (cuts nexts : List ℕ)
    (check : FailsHinted first second levelNum levelDen a d b e boundNum boundDen cuts nexts) :
    (productBinomial first second (ratPoint a d le₁ positive₁)
        (ratPoint b e le₂ positive₂)).real (fisherRejectionRegionAt first second alpha) <
      (boundNum : ℝ) / boundDen := by
  obtain ⟨valid, strict⟩ := check
  rw [rejection_probability first second levelNum levelDen levelDen_pos alpha level_eq,
    rejectionNumerator_hint _ _ _ _ _ _ _ _ _ _ valid]
  exact ratio_lt_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos strict

end StatClaim.Modules.AssociationPower
