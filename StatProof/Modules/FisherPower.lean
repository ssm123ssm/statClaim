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

/-- The uniform Type I bound of the same analysis, as a policy claim. -/
theorem typeI_statement (sizes : FixedSampleDesign) (level : SignificanceLevel) :
    ((analysis sizes level).typeIClaim (level.value : ℝ)).statement :=
  (Fisher.fixedGuarantee sizes level).toPolicy

end StatProof.Modules.FisherPower
