module

public import StatProof.Modules.Fisher
public import StatProof.Computation
public import StatProof.Core.Policy
public import StatProof.ProductBinomial

/-!
Exact power of the fixed-sample Fisher analysis at one declared pair of
rational success probabilities. The rejection region is recomputed in the
kernel from the formal p-value, so no table of decisions is trusted.

Power at a planning point is not a guarantee at other alternatives, and it
does not assert that the planning point describes a real study.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.FisherPower

open MeasureTheory TwoArmBinomial

/-- Rejection by natural-number cross multiplication: p-value ≤ levelNum/levelDen. -/
def checkedReject (nControl nTreatment levelNum levelDen control treatment : ℕ) : Bool :=
  decide (checkedExtremeWeight nControl nTreatment (control + treatment) control * levelDen ≤
    levelNum * Nat.fast_choose (nControl + nTreatment) (control + treatment))

theorem checkedReject_iff (nControl nTreatment levelNum levelDen control treatment : ℕ)
    (levelDen_pos : 0 < levelDen) (control_le : control ≤ nControl)
    (treatment_le : treatment ≤ nTreatment) :
    checkedReject nControl nTreatment levelNum levelDen control treatment = true ↔
      hypergeometricPValue nControl nTreatment (control + treatment) control ≤
        (levelNum : ℚ) / levelDen := by
  have feasible : control + treatment ≤ nControl + nTreatment := by omega
  have normalizer_pos : (0 : ℚ) < Nat.fast_choose (nControl + nTreatment) (control + treatment) := by
    rw [← Nat.choose_eq_fast_choose]
    exact hypergeometric_denominator_pos _ _ _ feasible
  rw [hypergeometricPValue_eq_checked_ratio _ _ _ _ feasible,
    div_le_div_iff₀ normalizer_pos (by exact_mod_cast levelDen_pos)]
  simp only [checkedReject, decide_eq_true_eq]
  exact_mod_cast Iff.rfl

/-! ### Checking the rejection region from supplied thresholds

Recomputing every p-value is expensive. At each pooled total the rejected
tables are exactly those whose weight is at most some cut. A proposed cut, and
the next larger weight, are validated by three passes over the support. The
proposals are untrusted: an invalid one fails the check. -/

/-- Sum of table weights not exceeding a threshold, at a fixed pooled total. -/
def lowSum (nControl nTreatment total threshold : ℕ) : ℕ :=
  ∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
    (fun k => checkedWeight nControl nTreatment total k ≤ threshold),
    checkedWeight nControl nTreatment total k

theorem lowSum_mono (nControl nTreatment total : ℕ) {s t : ℕ} (h : s ≤ t) :
    lowSum nControl nTreatment total s ≤ lowSum nControl nTreatment total t := by
  unfold lowSum
  apply Finset.sum_le_sum_of_subset
  intro k member
  simp only [Finset.mem_filter] at member ⊢
  exact ⟨member.1, member.2.trans h⟩

/-- `cut` is the largest rejected weight at this total and `next` the smallest
weight above it; zero stands for "none". -/
def HintValid (nControl nTreatment levelNum levelDen total cut next : ℕ) : Prop :=
  lowSum nControl nTreatment total cut * levelDen ≤
      levelNum * Nat.fast_choose (nControl + nTreatment) total ∧
    (next = 0 ∨ levelNum * Nat.fast_choose (nControl + nTreatment) total <
      lowSum nControl nTreatment total next * levelDen) ∧
    ∀ k ∈ hypergeometricSupport nControl nTreatment total,
      checkedWeight nControl nTreatment total k ≤ cut ∨
        (next ≠ 0 ∧ next ≤ checkedWeight nControl nTreatment total k)

instance (nControl nTreatment levelNum levelDen total cut next : ℕ) :
    Decidable (HintValid nControl nTreatment levelNum levelDen total cut next) := by
  unfold HintValid
  infer_instance

theorem checkedReject_eq_of_hint (nControl nTreatment levelNum levelDen total cut next : ℕ)
    (valid : HintValid nControl nTreatment levelNum levelDen total cut next) (k : ℕ)
    (member : k ∈ hypergeometricSupport nControl nTreatment total) :
    checkedReject nControl nTreatment levelNum levelDen k (total - k) =
      decide (checkedWeight nControl nTreatment total k ≤ cut) := by
  have bounds := member
  simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range] at bounds
  have pooled : k + (total - k) = total := by omega
  obtain ⟨low, high, cover⟩ := valid
  unfold checkedReject
  rw [pooled]
  change decide (lowSum nControl nTreatment total (checkedWeight nControl nTreatment total k) *
    levelDen ≤ _) = _
  by_cases small : checkedWeight nControl nTreatment total k ≤ cut
  · rw [decide_eq_true small]
    exact decide_eq_true
      ((Nat.mul_le_mul_right levelDen (lowSum_mono nControl nTreatment total small)).trans low)
  · rcases cover k member with le | ⟨nonzero, ge⟩
    · exact absurd le small
    · rcases high with zero | strict
      · exact absurd zero nonzero
      · rw [decide_eq_false small]
        exact decide_eq_false (Nat.not_le.mpr (strict.trans_le
          (Nat.mul_le_mul_right levelDen (lowSum_mono nControl nTreatment total ge))))

/-- Rejection decided from the supplied cut for the table's pooled total. -/
def hintReject (nControl nTreatment : ℕ) (cuts : List ℕ) (control treatment : ℕ) : Bool :=
  decide (checkedWeight nControl nTreatment (control + treatment) control ≤
    cuts.getD (control + treatment) 0)

def HintsValid (nControl nTreatment levelNum levelDen : ℕ) (cuts nexts : List ℕ) : Prop :=
  ∀ total, total < nControl + nTreatment + 1 →
    HintValid nControl nTreatment levelNum levelDen total (cuts.getD total 0) (nexts.getD total 0)

instance (nControl nTreatment levelNum levelDen : ℕ) (cuts nexts : List ℕ) :
    Decidable (HintsValid nControl nTreatment levelNum levelDen cuts nexts) := by
  unfold HintsValid
  infer_instance

/-- With validated thresholds, the cheap rule gives the same rejection probability. -/
theorem rejectionNumerator_hint (nControl nTreatment a d b e levelNum levelDen : ℕ)
    (cuts nexts : List ℕ) (valid : HintsValid nControl nTreatment levelNum levelDen cuts nexts) :
    rejectionNumerator nControl nTreatment a d b e
        (checkedReject nControl nTreatment levelNum levelDen) =
      rejectionNumerator nControl nTreatment a d b e (hintReject nControl nTreatment cuts) := by
  unfold rejectionNumerator
  apply Finset.sum_congr rfl
  intro x x_mem
  apply Finset.sum_congr rfl
  intro y y_mem
  have x_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp x_mem)
  have y_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp y_mem)
  have member : x ∈ hypergeometricSupport nControl nTreatment (x + y) := by
    simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range]
    omega
  have key := checkedReject_eq_of_hint nControl nTreatment levelNum levelDen (x + y) _ _
    (valid (x + y) (by omega)) x member
  rw [show x + y - x = y by omega] at key
  rw [key]
  rfl

/-- The fixed Fisher analysis viewed as a policy analysis. -/
noncomputable def analysis (sizes : FixedSampleDesign) (level : SignificanceLevel) :
    Core.PolicyAnalysis (Core.Policy.fixed (model sizes)) :=
  Core.PolicyAnalysis.ofFixed
    (Fisher.analysis sizes (Core.StudyDesign.fixed (model sizes)) level)

/-- A planning point: one rational success probability for each arm. -/
noncomputable def ratePoint (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e)
    (positive₂ : 0 < e) : Parameters :=
  (ratPoint a d le₁ positive₁, ratPoint b e le₂ positive₂)

/-- Exact rejection probability at a rational planning point. -/
theorem rejection_probability (sizes : FixedSampleDesign) (level : SignificanceLevel)
    (levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (level_eq : level.value = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e) :
    ((Core.Policy.fixed (model sizes)).law (ratePoint a d b e le₁ positive₁ le₂ positive₂)).real
        (analysis sizes level).rejection =
      (rejectionNumerator sizes.nControl sizes.nTreatment a d b e
        (checkedReject sizes.nControl sizes.nTreatment levelNum levelDen) : ℝ) /
        (rejectionDenominator sizes.nControl sizes.nTreatment d e : ℝ) := by
  rw [Core.Policy.fixed_law, rejectionDenominator_cast]
  refine productBinomial_real_ratPoint _ _ a d b e le₁ positive₁ le₂ positive₂ _ _ ?_
  intro control control_le treatment treatment_le
  rw [checkedReject_iff _ _ _ _ _ _ levelDen_pos control_le treatment_le, ← level_eq]
  change ((control, treatment) ∈ Set.Iic sizes.nControl ×ˢ Set.Iic sizes.nTreatment ∧ _) ↔ _
  simp [control_le, treatment_le]
  rfl

/-- Power at the planning point, from one natural-number check. -/
theorem power_of_check (sizes : FixedSampleDesign) (level : SignificanceLevel)
    (levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (level_eq : level.value = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * rejectionDenominator sizes.nControl sizes.nTreatment d e ≤
      rejectionNumerator sizes.nControl sizes.nTreatment a d b e
        (checkedReject sizes.nControl sizes.nTreatment levelNum levelDen) * boundDen) :
    ((analysis sizes level).powerClaim
      (fun parameter => parameter = ratePoint a d b e le₁ positive₁ le₂ positive₂)
      ((boundNum : ℝ) / boundDen)).statement := by
  intro parameter alternative
  rw [show parameter = ratePoint a d b e le₁ positive₁ le₂ positive₂ from alternative,
    rejection_probability sizes level levelNum levelDen levelDen_pos level_eq]
  exact le_ratio_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos check

/-- Every candidate with `n` controls and `ratio * n` treated participants, for
`n` from `low` up to but excluding `high`, has power below the bound at the
planning point. A decidable natural-number statement. -/
def SmallerFail (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ) : Prop :=
  ∀ n, n < high → low ≤ n →
    rejectionNumerator n (ratio * n) a d b e (checkedReject n (ratio * n) levelNum levelDen) *
        boundDen < boundNum * rejectionDenominator n (ratio * n) d e

instance (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ) :
    Decidable (SmallerFail ratio low high levelNum levelDen a d b e boundNum boundDen) := by
  unfold SmallerFail
  infer_instance

/-- `SmallerFail` checked with supplied thresholds for each candidate size. -/
def SmallerFailHinted (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ)
    (cuts nexts : List (List ℕ)) : Prop :=
  ∀ n, n < high → low ≤ n →
    HintsValid n (ratio * n) levelNum levelDen (cuts.getD (n - low) [])
        (nexts.getD (n - low) []) ∧
      rejectionNumerator n (ratio * n) a d b e
          (hintReject n (ratio * n) (cuts.getD (n - low) [])) * boundDen <
        boundNum * rejectionDenominator n (ratio * n) d e

instance (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ)
    (cuts nexts : List (List ℕ)) :
    Decidable (SmallerFailHinted ratio low high levelNum levelDen a d b e boundNum boundDen
      cuts nexts) := by
  unfold SmallerFailHinted
  infer_instance

theorem smallerFail_of_hinted (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ)
    (cuts nexts : List (List ℕ))
    (check : SmallerFailHinted ratio low high levelNum levelDen a d b e boundNum boundDen
      cuts nexts) :
    SmallerFail ratio low high levelNum levelDen a d b e boundNum boundDen := by
  intro n upper lower
  obtain ⟨valid, strict⟩ := check n upper lower
  rw [rejectionNumerator_hint _ _ _ _ _ _ _ _ _ _ valid]
  exact strict

/-- No smaller candidate with the same allocation ratio reaches the power bound. -/
theorem power_lt_of_smallerFail (level : SignificanceLevel)
    (levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (level_eq : level.value = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen) (ratio : ℕ) (ratio_pos : 0 < ratio)
    (low high : ℕ)
    (check : SmallerFail ratio low high levelNum levelDen a d b e boundNum boundDen)
    (n : ℕ) (positive : 0 < n) (lower : low ≤ n) (upper : n < high) :
    ((Core.Policy.fixed (model ⟨n, ratio * n, positive, Nat.mul_pos ratio_pos positive⟩)).law
        (ratePoint a d b e le₁ positive₁ le₂ positive₂)).real
        (analysis ⟨n, ratio * n, positive, Nat.mul_pos ratio_pos positive⟩ level).rejection <
      (boundNum : ℝ) / boundDen := by
  rw [rejection_probability ⟨n, ratio * n, positive, Nat.mul_pos ratio_pos positive⟩ level
    levelNum levelDen levelDen_pos level_eq]
  exact ratio_lt_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos (check n upper lower)

/-- The uniform Type I bound of the same analysis, as a policy claim. -/
theorem typeI_statement (sizes : FixedSampleDesign) (level : SignificanceLevel) :
    ((analysis sizes level).typeIClaim (level.value : ℝ)).statement :=
  (Fisher.fixedGuarantee sizes level).toPolicy

end StatProof.Modules.FisherPower
