module

public import StatProof.Fisher

/-!
Per-result checking bridge. Integer arithmetic is evaluated by Lean's kernel
using factorial-based binomial coefficients. Python may propose a fraction;
the checked cross-product equality proves that fraction equals the formal
p-value. No correctness assumption about the Python implementation is required.
-/

@[expose] public section

namespace StatProof

/-- An efficient integer weight whose equality to the specification is proved. -/
def checkedWeight (nControl nTreatment total k : ℕ) : ℕ :=
  Nat.fast_choose nControl k * Nat.fast_choose nTreatment (total - k)

theorem checkedWeight_eq (nControl nTreatment total k : ℕ) :
    checkedWeight nControl nTreatment total k =
      hypergeometricWeight nControl nTreatment total k := by
  simp only [checkedWeight, hypergeometricWeight, Nat.choose_eq_fast_choose]

/-- The numerator of the exact probability-ordered p-value, computed with the
proved factorial-based formula, independently of Python's recurrence. -/
def checkedExtremeWeight (nControl nTreatment total observed : ℕ) : ℕ :=
  ∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
    (fun k => checkedWeight nControl nTreatment total k ≤
      checkedWeight nControl nTreatment total observed),
    checkedWeight nControl nTreatment total k

theorem hypergeometricPValue_eq_checked_ratio (nControl nTreatment total observed : ℕ)
    (feasible : total ≤ nControl + nTreatment) :
    hypergeometricPValue nControl nTreatment total observed =
      (checkedExtremeWeight nControl nTreatment total observed : ℚ) /
        (Nat.fast_choose (nControl + nTreatment) total : ℚ) := by
  rw [hypergeometricPValue_eq_weight_ratio _ _ _ _ feasible]
  simp only [checkedExtremeWeight, checkedWeight_eq, ← Nat.choose_eq_fast_choose]

/-- A proposed rational value is certified by checking one natural-number
cross-product equality in the kernel. The proposed denominator must be positive. -/
theorem hypergeometricPValue_eq_of_cross_product
    (nControl nTreatment total observed numerator denominator : ℕ)
    (feasible : total ≤ nControl + nTreatment) (denominator_positive : 0 < denominator)
    (cross_product : checkedExtremeWeight nControl nTreatment total observed * denominator =
      numerator * Nat.fast_choose (nControl + nTreatment) total) :
    hypergeometricPValue nControl nTreatment total observed =
      (numerator : ℚ) / (denominator : ℚ) := by
  rw [hypergeometricPValue_eq_checked_ratio _ _ _ _ feasible]
  have normalizer_ne : (Nat.fast_choose (nControl + nTreatment) total : ℚ) ≠ 0 := by
    rw [← Nat.choose_eq_fast_choose]
    exact ne_of_gt (hypergeometric_denominator_pos _ _ _ feasible)
  have denominator_ne : (denominator : ℚ) ≠ 0 := by exact_mod_cast denominator_positive.ne'
  apply (div_eq_div_iff normalizer_ne denominator_ne).mpr
  exact_mod_cast cross_product

/-- The observed table probability can be checked by the same integer method. -/
theorem hypergeometricMass_eq_of_cross_product
    (nControl nTreatment total observed numerator denominator : ℕ)
    (feasible : total ≤ nControl + nTreatment) (denominator_positive : 0 < denominator)
    (cross_product : checkedWeight nControl nTreatment total observed * denominator =
      numerator * Nat.fast_choose (nControl + nTreatment) total) :
    hypergeometricMass nControl nTreatment total observed =
      (numerator : ℚ) / (denominator : ℚ) := by
  unfold hypergeometricMass
  rw [← checkedWeight_eq, Nat.choose_eq_fast_choose]
  have normalizer_ne : (Nat.fast_choose (nControl + nTreatment) total : ℚ) ≠ 0 := by
    rw [← Nat.choose_eq_fast_choose]
    exact ne_of_gt (hypergeometric_denominator_pos _ _ _ feasible)
  have denominator_ne : (denominator : ℚ) ≠ 0 := by exact_mod_cast denominator_positive.ne'
  apply (div_eq_div_iff normalizer_ne denominator_ne).mpr
  exact_mod_cast cross_product

end StatProof
