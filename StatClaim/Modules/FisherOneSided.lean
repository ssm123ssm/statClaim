module

public import StatClaim.Modules.FisherPower
public import StatClaim.BinomialMonotone

/-!
The one-sided Fisher exact test for two arms: reject when the control arm has
few enough successes, given the pooled total, that the treatment looks better.
The null is "the treatment's success rate is at most the control's".

At equal rates the bound is the general conditional argument. For a smaller
treatment rate it follows because adding a treatment success never turns a
rejection into a non-rejection; that property is checked for the declared
design from validated thresholds.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.FisherOneSided

open MeasureTheory TwoArmBinomial

/-- One-sided conditional p-value: the chance of this few control successes. -/
def lowerPValue (nControl nTreatment total observed : ℕ) : ℚ :=
  lowerTailPValue (hypergeometricSupport nControl nTreatment total)
    (hypergeometricMass nControl nTreatment total) observed

/-- Tables rejected at the given level. -/
def region (nControl nTreatment : ℕ) (alpha : ℚ) : Finset (ℕ × ℕ) :=
  (binomialCountSupport nControl nTreatment).filter (fun counts =>
    lowerPValue nControl nTreatment (counts.1 + counts.2) counts.1 ≤ alpha)

/-- With equal success rates, the test rejects with probability at most alpha. -/
theorem boundary_le (nControl nTreatment : ℕ) (p : unitInterval) (alpha : ℚ)
    (alpha_nonnegative : 0 ≤ alpha) :
    (fisherNullLaw nControl nTreatment p).real (region nControl nTreatment alpha) ≤
      (alpha : ℝ) := by
  rw [← sum_measureReal_singleton]
  simp only [fisherNullLaw_real_singleton, region, Finset.sum_filter]
  exact conditionalTest_rejection_le nControl nTreatment p p.property.1 p.property.2 alpha
    (fun total k => lowerPValue nControl nTreatment total k ≤ alpha)
    (fun total => lowerTail_rejection_mass_le _ _
      (fun k _ => hypergeometricMass_nonnegative nControl nTreatment total k)
      alpha alpha_nonnegative)

/-- One more treatment success never turns a rejection into a non-rejection. -/
def SectionsUpper (nControl nTreatment : ℕ) (alpha : ℚ) : Prop :=
  ∀ x y, y < nTreatment → (x, y) ∈ region nControl nTreatment alpha →
    (x, y + 1) ∈ region nControl nTreatment alpha

/-- The analysis as a policy analysis. Null: treatment rate at most control rate. -/
noncomputable def analysis (sizes : FixedSampleDesign) (level : SignificanceLevel) :
    Core.PolicyAnalysis (Core.Policy.fixed (model sizes)) where
  hypothesis := proportionDifferenceAtMost 0
  rejection := ↑(region sizes.nControl sizes.nTreatment level.value)
  rejection_measurable := Finset.measurableSet _

/-- Type I error over the whole null, given the section property. -/
theorem typeI_of_sections (sizes : FixedSampleDesign) (level : SignificanceLevel)
    (sections : SectionsUpper sizes.nControl sizes.nTreatment level.value) :
    ((analysis sizes level).typeIClaim (level.value : ℝ)).statement := by
  intro parameter null
  rw [Core.Policy.fixed_law]
  have ordered : parameter.2 ≤ parameter.1 := by
    have real : (parameter.2 : ℝ) - (parameter.1 : ℝ) ≤ ((0 : ℚ) : ℝ) := null
    apply Subtype.coe_le_coe.mp
    simpa using real
  refine le_trans (productBinomial_real_mono_right sizes.nControl sizes.nTreatment
    parameter.1 parameter.2 parameter.1 ordered _ ?_)
    (boundary_le sizes.nControl sizes.nTreatment parameter.1 level.value level.nonnegative)
  intro x y bound member
  exact Finset.mem_coe.mpr (sections x y bound (Finset.mem_coe.mp member))

/-! ### Kernel computation -/

/-- Integer numerator of the one-sided p-value. -/
def lowerWeight (nControl nTreatment total observed : ℕ) : ℕ :=
  ∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter (fun k => k ≤ observed),
    checkedWeight nControl nTreatment total k

theorem lowerPValue_eq_ratio (nControl nTreatment total observed : ℕ)
    (_feasible : total ≤ nControl + nTreatment) :
    lowerPValue nControl nTreatment total observed =
      (lowerWeight nControl nTreatment total observed : ℚ) /
        (Nat.fast_choose (nControl + nTreatment) total : ℚ) := by
  unfold lowerPValue lowerTailPValue lowerWeight
  simp only [hypergeometricMass, checkedWeight_eq, ← Nat.choose_eq_fast_choose, Nat.cast_sum,
    Finset.sum_div]

/-- A proposed p-value is confirmed by one cross-multiplication. -/
theorem lowerPValue_eq_of_cross_product
    (nControl nTreatment total observed numerator denominator : ℕ)
    (feasible : total ≤ nControl + nTreatment) (denominator_positive : 0 < denominator)
    (cross_product : lowerWeight nControl nTreatment total observed * denominator =
      numerator * Nat.fast_choose (nControl + nTreatment) total) :
    lowerPValue nControl nTreatment total observed = (numerator : ℚ) / (denominator : ℚ) := by
  rw [lowerPValue_eq_ratio _ _ _ _ feasible]
  have normalizer_ne : (Nat.fast_choose (nControl + nTreatment) total : ℚ) ≠ 0 := by
    rw [← Nat.choose_eq_fast_choose]
    exact ne_of_gt (hypergeometric_denominator_pos _ _ _ feasible)
  have denominator_ne : (denominator : ℚ) ≠ 0 := by exact_mod_cast denominator_positive.ne'
  apply (div_eq_div_iff normalizer_ne denominator_ne).mpr
  exact_mod_cast cross_product

/-- Rejection by natural-number cross multiplication. -/
def checkedReject (nControl nTreatment levelNum levelDen control treatment : ℕ) : Bool :=
  decide (lowerWeight nControl nTreatment (control + treatment) control * levelDen ≤
    levelNum * Nat.fast_choose (nControl + nTreatment) (control + treatment))

theorem checkedReject_iff (nControl nTreatment levelNum levelDen control treatment : ℕ)
    (levelDen_pos : 0 < levelDen) (control_le : control ≤ nControl)
    (treatment_le : treatment ≤ nTreatment) :
    checkedReject nControl nTreatment levelNum levelDen control treatment = true ↔
      lowerPValue nControl nTreatment (control + treatment) control ≤
        (levelNum : ℚ) / levelDen := by
  have feasible : control + treatment ≤ nControl + nTreatment := by omega
  have normalizer_pos :
      (0 : ℚ) < Nat.fast_choose (nControl + nTreatment) (control + treatment) := by
    rw [← Nat.choose_eq_fast_choose]
    exact hypergeometric_denominator_pos _ _ _ feasible
  rw [lowerPValue_eq_ratio _ _ _ _ feasible,
    div_le_div_iff₀ normalizer_pos (by exact_mod_cast levelDen_pos)]
  simp only [checkedReject, decide_eq_true_eq]
  exact_mod_cast Iff.rfl

theorem lowerWeight_mono (nControl nTreatment total : ℕ) {a b : ℕ} (h : a ≤ b) :
    lowerWeight nControl nTreatment total a ≤ lowerWeight nControl nTreatment total b := by
  unfold lowerWeight
  apply Finset.sum_le_sum_of_subset
  intro k member
  simp only [Finset.mem_filter] at member ⊢
  exact ⟨member.1, member.2.trans h⟩

/-- Weight strictly below a bound. -/
def belowWeight (nControl nTreatment total bound : ℕ) : ℕ :=
  ∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter (fun k => k < bound),
    checkedWeight nControl nTreatment total k

/-- At this total, control counts below `bound` are rejected and no others. -/
def HintValid (nControl nTreatment levelNum levelDen total bound : ℕ) : Prop :=
  belowWeight nControl nTreatment total bound * levelDen ≤
      levelNum * Nat.fast_choose (nControl + nTreatment) total ∧
    (min nControl total < bound ∨
      levelNum * Nat.fast_choose (nControl + nTreatment) total <
        lowerWeight nControl nTreatment total bound * levelDen)

instance (nControl nTreatment levelNum levelDen total bound : ℕ) :
    Decidable (HintValid nControl nTreatment levelNum levelDen total bound) := by
  unfold HintValid
  infer_instance

theorem checkedReject_eq_of_hint (nControl nTreatment levelNum levelDen total bound : ℕ)
    (valid : HintValid nControl nTreatment levelNum levelDen total bound) (k : ℕ)
    (member : k ∈ hypergeometricSupport nControl nTreatment total) :
    checkedReject nControl nTreatment levelNum levelDen k (total - k) = decide (k < bound) := by
  have bounds := (mem_hypergeometricSupport_iff nControl nTreatment total k).mp member
  have inside := member
  simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range] at inside
  have pooled : k + (total - k) = total := by omega
  obtain ⟨low, high⟩ := valid
  unfold checkedReject
  rw [pooled]
  by_cases small : k < bound
  · rw [decide_eq_true small]
    have subset : lowerWeight nControl nTreatment total k ≤
        belowWeight nControl nTreatment total bound := by
      unfold lowerWeight belowWeight
      apply Finset.sum_le_sum_of_subset
      intro j j_mem
      simp only [Finset.mem_filter] at j_mem ⊢
      exact ⟨j_mem.1, lt_of_le_of_lt j_mem.2 small⟩
    exact decide_eq_true ((Nat.mul_le_mul_right levelDen subset).trans low)
  · rw [decide_eq_false small]
    rcases high with beyond | strict
    · exact absurd (lt_of_le_of_lt bounds.2 beyond) small
    · exact decide_eq_false (Nat.not_le.mpr (strict.trans_le
        (Nat.mul_le_mul_right levelDen
          (lowerWeight_mono nControl nTreatment total (Nat.le_of_not_lt small)))))

/-- Rejection decided from the supplied bound for the table's pooled total. -/
def hintReject (bounds : List ℕ) (control treatment : ℕ) : Bool :=
  decide (control < bounds.getD (control + treatment) 0)

def HintsValid (nControl nTreatment levelNum levelDen : ℕ) (bounds : List ℕ) : Prop :=
  ∀ total, total < nControl + nTreatment + 1 →
    HintValid nControl nTreatment levelNum levelDen total (bounds.getD total 0)

instance (nControl nTreatment levelNum levelDen : ℕ) (bounds : List ℕ) :
    Decidable (HintsValid nControl nTreatment levelNum levelDen bounds) := by
  unfold HintsValid
  infer_instance

theorem checkedReject_eq_hint (nControl nTreatment levelNum levelDen : ℕ) (bounds : List ℕ)
    (valid : HintsValid nControl nTreatment levelNum levelDen bounds) (x y : ℕ)
    (x_le : x ≤ nControl) (y_le : y ≤ nTreatment) :
    checkedReject nControl nTreatment levelNum levelDen x y = hintReject bounds x y := by
  have member : x ∈ hypergeometricSupport nControl nTreatment (x + y) := by
    simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range]
    omega
  have key := checkedReject_eq_of_hint nControl nTreatment levelNum levelDen (x + y) _
    (valid (x + y) (by omega)) x member
  rw [show x + y - x = y by omega] at key
  exact key

theorem rejectionNumerator_hint (nControl nTreatment a d b e levelNum levelDen : ℕ)
    (bounds : List ℕ) (valid : HintsValid nControl nTreatment levelNum levelDen bounds) :
    rejectionNumerator nControl nTreatment a d b e
        (checkedReject nControl nTreatment levelNum levelDen) =
      rejectionNumerator nControl nTreatment a d b e (hintReject bounds) := by
  unfold rejectionNumerator
  apply Finset.sum_congr rfl
  intro x x_mem
  apply Finset.sum_congr rfl
  intro y y_mem
  rw [checkedReject_eq_hint nControl nTreatment levelNum levelDen bounds valid x y
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp x_mem))
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp y_mem))]

theorem mem_region_iff (nControl nTreatment levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (x y : ℕ) :
    (x, y) ∈ region nControl nTreatment ((levelNum : ℚ) / levelDen) ↔
      x ≤ nControl ∧ y ≤ nTreatment ∧
        checkedReject nControl nTreatment levelNum levelDen x y = true := by
  simp only [region, binomialCountSupport, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨x_le, y_le⟩, small⟩
    exact ⟨x_le, y_le, (checkedReject_iff _ _ _ _ _ _ levelDen_pos x_le y_le).mpr small⟩
  · rintro ⟨x_le, y_le, rejected⟩
    exact ⟨⟨x_le, y_le⟩, (checkedReject_iff _ _ _ _ _ _ levelDen_pos x_le y_le).mp rejected⟩

/-- The section property stated on the supplied bounds. -/
def HintSections (nControl nTreatment : ℕ) (bounds : List ℕ) : Prop :=
  ∀ x, x < nControl + 1 → ∀ y, y < nTreatment →
    hintReject bounds x y = true → hintReject bounds x (y + 1) = true

instance (nControl nTreatment : ℕ) (bounds : List ℕ) :
    Decidable (HintSections nControl nTreatment bounds) := by
  unfold HintSections
  infer_instance

theorem sectionsUpper_of_hints (nControl nTreatment levelNum levelDen : ℕ)
    (levelDen_pos : 0 < levelDen) (bounds : List ℕ)
    (valid : HintsValid nControl nTreatment levelNum levelDen bounds)
    (sections : HintSections nControl nTreatment bounds) :
    SectionsUpper nControl nTreatment ((levelNum : ℚ) / levelDen) := by
  intro x y y_lt member
  obtain ⟨x_le, y_le, rejected⟩ :=
    (mem_region_iff nControl nTreatment levelNum levelDen levelDen_pos x y).mp member
  refine (mem_region_iff nControl nTreatment levelNum levelDen levelDen_pos x (y + 1)).mpr
    ⟨x_le, y_lt, ?_⟩
  rw [checkedReject_eq_hint _ _ _ _ bounds valid x y x_le y_le] at rejected
  rw [checkedReject_eq_hint _ _ _ _ bounds valid x (y + 1) x_le y_lt]
  exact sections x (Nat.lt_succ_of_le x_le) y y_lt rejected

/-- Type I error over the whole null from validated bounds. -/
theorem typeI_of_hints (sizes : FixedSampleDesign) (level : SignificanceLevel)
    (levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (level_eq : level.value = (levelNum : ℚ) / levelDen) (bounds : List ℕ)
    (valid : HintsValid sizes.nControl sizes.nTreatment levelNum levelDen bounds)
    (sections : HintSections sizes.nControl sizes.nTreatment bounds) :
    ((analysis sizes level).typeIClaim (level.value : ℝ)).statement := by
  apply typeI_of_sections
  rw [level_eq]
  exact sectionsUpper_of_hints _ _ _ _ levelDen_pos bounds valid sections

/-- Exact rejection probability at a rational planning point. -/
theorem rejection_probability (sizes : FixedSampleDesign) (level : SignificanceLevel)
    (levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (level_eq : level.value = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e) :
    ((Core.Policy.fixed (model sizes)).law
        (FisherPower.ratePoint a d b e le₁ positive₁ le₂ positive₂)).real
        (analysis sizes level).rejection =
      (rejectionNumerator sizes.nControl sizes.nTreatment a d b e
        (checkedReject sizes.nControl sizes.nTreatment levelNum levelDen) : ℝ) /
        (rejectionDenominator sizes.nControl sizes.nTreatment d e : ℝ) := by
  rw [Core.Policy.fixed_law, rejectionDenominator_cast]
  refine productBinomial_real_ratPoint _ _ a d b e le₁ positive₁ le₂ positive₂ _ _ ?_
  intro control control_le treatment treatment_le
  change (control, treatment) ∈ (↑(region sizes.nControl sizes.nTreatment level.value) :
    Set (ℕ × ℕ)) ↔ _
  rw [Finset.mem_coe, level_eq, mem_region_iff _ _ _ _ levelDen_pos]
  simp [control_le, treatment_le]

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
      (fun parameter => parameter = FisherPower.ratePoint a d b e le₁ positive₁ le₂ positive₂)
      ((boundNum : ℝ) / boundDen)).statement := by
  intro parameter alternative
  rw [show parameter = FisherPower.ratePoint a d b e le₁ positive₁ le₂ positive₂ from
    alternative, rejection_probability sizes level levelNum levelDen levelDen_pos level_eq]
  exact le_ratio_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos check

/-- Every smaller candidate with the same allocation ratio has power below the bound. -/
def SmallerFailHinted (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ)
    (bounds : List (List ℕ)) : Prop :=
  ∀ n, n < high → low ≤ n →
    HintsValid n (ratio * n) levelNum levelDen (bounds.getD (n - low) []) ∧
      rejectionNumerator n (ratio * n) a d b e (hintReject (bounds.getD (n - low) [])) *
          boundDen < boundNum * rejectionDenominator n (ratio * n) d e

instance (ratio low high levelNum levelDen a d b e boundNum boundDen : ℕ)
    (bounds : List (List ℕ)) :
    Decidable (SmallerFailHinted ratio low high levelNum levelDen a d b e boundNum boundDen
      bounds) := by
  unfold SmallerFailHinted
  infer_instance

theorem power_lt_of_smallerFail (level : SignificanceLevel)
    (levelNum levelDen : ℕ) (levelDen_pos : 0 < levelDen)
    (level_eq : level.value = (levelNum : ℚ) / levelDen)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen) (ratio : ℕ) (ratio_pos : 0 < ratio)
    (low high : ℕ) (bounds : List (List ℕ))
    (check : SmallerFailHinted ratio low high levelNum levelDen a d b e boundNum boundDen bounds)
    (n : ℕ) (positive : 0 < n) (lower : low ≤ n) (upper : n < high) :
    ((Core.Policy.fixed (model ⟨n, ratio * n, positive, Nat.mul_pos ratio_pos positive⟩)).law
        (FisherPower.ratePoint a d b e le₁ positive₁ le₂ positive₂)).real
        (analysis ⟨n, ratio * n, positive, Nat.mul_pos ratio_pos positive⟩ level).rejection <
      (boundNum : ℝ) / boundDen := by
  obtain ⟨valid, strict⟩ := check n upper lower
  rw [rejection_probability ⟨n, ratio * n, positive, Nat.mul_pos ratio_pos positive⟩ level
    levelNum levelDen levelDen_pos level_eq, rejectionNumerator_hint _ _ _ _ _ _ _ _ _ valid]
  exact ratio_lt_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos strict

end StatClaim.Modules.FisherOneSided
