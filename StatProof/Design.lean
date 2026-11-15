module

public import Mathlib.Tactic.NormNum

/-!
Foundational declarations only. These definitions do not yet specify binomial
sampling, a rejection rule, or a Type I error guarantee.
-/

@[expose] public section

namespace StatProof

/-- Sample sizes for the initial fixed-sample module. Sampling assumptions will
be explicit hypotheses of the future statistical theorem. -/
structure FixedSampleDesign where
  nControl : Nat
  nTreatment : Nat
  controlPositive : 0 < nControl
  treatmentPositive : 0 < nTreatment

/-- An exact significance level, including the boundary levels zero and one. -/
structure SignificanceLevel where
  value : ℚ
  nonnegative : 0 ≤ value
  le_one : value ≤ 1

/-- Backward-compatible default; analyses may choose another level explicitly. -/
def targetAlpha : ℚ := 1 / 20

def defaultLevel : SignificanceLevel := ⟨targetAlpha, by norm_num [targetAlpha],
  by norm_num [targetAlpha]⟩

/-- An arithmetic sanity check, not a statistical guarantee. -/
theorem targetAlpha_pos : 0 < targetAlpha := by
  norm_num [targetAlpha]

theorem targetAlpha_lt_one : targetAlpha < 1 := by
  norm_num [targetAlpha]

end StatProof
