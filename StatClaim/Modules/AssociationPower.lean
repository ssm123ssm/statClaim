module

public import StatClaim.Modules.Association
public import StatClaim.Modules.FisherPower
public import StatClaim.Modules.BinomialPower

/-!
Exact power of Fisher's test of no association in an observational study whose design
fixes two group sizes: the unexposed and exposed groups of a cohort, or the controls and
cases of a case-control study. The table then holds two independent binomial counts with
their own probabilities (`productBinomial`), and the test rejects on Fisher's region
(`fisherRejectionRegionAt`), the same objects as `Association.groups_typeI_le_alpha`.

At rational probabilities the rejection probability is a ratio of natural numbers
(`rejection_probability`), so one comparison checked by the kernel bounds the power at a
planning point (`power_of_check`), and another shows that a candidate falls short
(`power_lt_of_fails`); a search proves this for every smaller candidate.

A cross-sectional study, or a cohort of one population, fixes only the total: the number
exposed is binomial and, given it, the two groups are as above (`Association.mixture`).
Power is the average of the groups' power over the number exposed (`total_real_ratPoint`);
each number exposed is checked in its own theorem (`PartValid`). Power at one point says
nothing about other points, or about cause.
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

/-! ### Designs that fix only the total -/

/-- With `k` of `n` exposed, Fisher's region for the groups `(n - k, k)` from validated
thresholds, and the numerator of its rejection probability at the planning point. -/
def PartValid (n k levelNum levelDen a d b e : ℕ) (cuts nexts : List ℕ) (numerator : ℕ) : Prop :=
  HintsValid (n - k) k levelNum levelDen cuts nexts ∧
    rejectionNumerator (n - k) k a d b e (hintReject (n - k) k cuts) = numerator

instance (n k levelNum levelDen a d b e : ℕ) (cuts nexts : List ℕ) (numerator : ℕ) :
    Decidable (PartValid n k levelNum levelDen a d b e cuts nexts numerator) := by
  unfold PartValid
  infer_instance

/-- Numerator of the rejection probability averaged over the number exposed, when each
participant is exposed with probability `aq/dq`; the denominator is
`dq ^ n * (d ^ n * e ^ n)`. -/
def totalNumerator (n aq dq d e : ℕ) (numerators : List ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), binomialWeight n aq dq k * numerators.getD k 0 * (d ^ k * e ^ (n - k))

theorem total_real_ratPoint (n aq dq a d b e levelNum levelDen : ℕ) (hq : aq ≤ dq)
    (hdq : 0 < dq) (ha : a ≤ d) (hd : 0 < d) (hb : b ≤ e) (he : 0 < e)
    (levelDen_pos : 0 < levelDen) (alpha : ℚ) (level_eq : alpha = (levelNum : ℚ) / levelDen)
    (cuts nexts : List (List ℕ)) (numerators : List ℕ)
    (parts : ∀ k, k < n + 1 → PartValid n k levelNum levelDen a d b e (cuts.getD k [])
      (nexts.getD k []) (numerators.getD k 0)) :
    (Association.mixture n (ratPoint aq dq hq hdq)
        (fun k => productBinomial (n - k) k (ratPoint a d ha hd) (ratPoint b e hb he))).real
        (Association.mixtureRejection n alpha) =
      (totalNumerator n aq dq d e numerators : ℝ) / ((dq ^ n * (d ^ n * e ^ n) : ℕ) : ℝ) := by
  unfold Association.mixtureRejection
  rw [BinomialPower.mixture_real_apply, totalNumerator, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k k_mem
  have k_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp k_mem)
  obtain ⟨valid, numerator_eq⟩ := parts k (by omega)
  rw [binomialMass_ratPoint n aq dq k hq hdq k_le,
    rejection_probability (n - k) k levelNum levelDen levelDen_pos alpha level_eq a d b e ha hd
      hb he, rejectionNumerator_hint _ _ _ _ _ _ _ _ _ _ valid, numerator_eq,
    rejectionDenominator_cast]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hq' : (dq : ℝ) ≠ 0 := by exact_mod_cast hdq.ne'
  have splitd : (d : ℝ) ^ n = (d : ℝ) ^ (n - k) * (d : ℝ) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel k_le]
  have splite : (e : ℝ) ^ n = (e : ℝ) ^ k * (e : ℝ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' k_le]
  push_cast
  rw [splitd, splite]
  field_simp

/-- Power with only the total fixed, at a rational planning point, from one check. -/
theorem total_power_of_check (n aq dq a d b e levelNum levelDen : ℕ) (hq : aq ≤ dq)
    (hdq : 0 < dq) (ha : a ≤ d) (hd : 0 < d) (hb : b ≤ e) (he : 0 < e)
    (levelDen_pos : 0 < levelDen) (alpha : ℚ) (level_eq : alpha = (levelNum : ℚ) / levelDen)
    (cuts nexts : List (List ℕ)) (numerators : List ℕ)
    (parts : ∀ k, k < n + 1 → PartValid n k levelNum levelDen a d b e (cuts.getD k [])
      (nexts.getD k []) (numerators.getD k 0))
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * (dq ^ n * (d ^ n * e ^ n)) ≤
      totalNumerator n aq dq d e numerators * boundDen) :
    (boundNum : ℝ) / boundDen ≤
      (Association.mixture n (ratPoint aq dq hq hdq)
        (fun k => productBinomial (n - k) k (ratPoint a d ha hd) (ratPoint b e hb he))).real
        (Association.mixtureRejection n alpha) := by
  rw [total_real_ratPoint n aq dq a d b e levelNum levelDen hq hdq ha hd hb he levelDen_pos alpha
    level_eq cuts nexts numerators parts]
  exact le_ratio_of_check _ _ _ _
    (Nat.mul_pos (Nat.pow_pos hdq) (Nat.mul_pos (Nat.pow_pos hd) (Nat.pow_pos he)))
    boundDen_pos check

end StatClaim.Modules.AssociationPower
