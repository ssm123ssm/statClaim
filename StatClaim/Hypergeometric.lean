module

public import StatClaim.Design
public import StatClaim.FinitePValue
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Nat.Choose.Vandermonde

/-!
The finite hypergeometric law for two fixed arm sizes and a pooled success count.
All masses and p-values are rational. Normalization follows from Vandermonde's
identity, and the conditional rejection bound follows from the generic finite
p-value theorem. The derivation of this law from independent binomial samples
and the connection with the Python recurrence are separate obligations.
-/

@[expose] public section

namespace StatClaim

/-- Feasible control success counts at a fixed pooled success count. -/
def hypergeometricSupport (nControl nTreatment total : ℕ) : Finset ℕ :=
  (Finset.range (total + 1)).filter (fun k => k ≤ nControl ∧ total - k ≤ nTreatment)

/-- The integer numerator of a conditional table probability. -/
def hypergeometricWeight (nControl nTreatment total k : ℕ) : ℕ :=
  nControl.choose k * nTreatment.choose (total - k)

/-- Conditional mass, for a feasible total and an outcome in the support. -/
def hypergeometricMass (nControl nTreatment total k : ℕ) : ℚ :=
  (hypergeometricWeight nControl nTreatment total k : ℚ) /
    ((nControl + nTreatment).choose total : ℚ)

/-- The support agrees with the inclusive bounds used by the executable test. -/
theorem mem_hypergeometricSupport_iff (nControl nTreatment total k : ℕ) :
    k ∈ hypergeometricSupport nControl nTreatment total ↔
      total - nTreatment ≤ k ∧ k ≤ min nControl total := by
  simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range, le_min_iff]
  omega

theorem hypergeometric_denominator_pos (nControl nTreatment total : ℕ)
    (feasible : total ≤ nControl + nTreatment) :
    (0 : ℚ) < (nControl + nTreatment).choose total := by
  exact_mod_cast Nat.choose_pos feasible

theorem hypergeometricMass_nonnegative (nControl nTreatment total k : ℕ) :
    0 ≤ hypergeometricMass nControl nTreatment total k := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Sum the unnormalized weights on the feasible support. -/
theorem hypergeometricWeight_sum (nControl nTreatment total : ℕ) :
    (∑ k ∈ hypergeometricSupport nControl nTreatment total,
      hypergeometricWeight nControl nTreatment total k) =
      (nControl + nTreatment).choose total := by
  have vandermonde : (∑ k ∈ Finset.range (total + 1),
      hypergeometricWeight nControl nTreatment total k) =
      (nControl + nTreatment).choose total := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rfl
  calc
    (∑ k ∈ hypergeometricSupport nControl nTreatment total,
        hypergeometricWeight nControl nTreatment total k) =
        ∑ k ∈ Finset.range (total + 1), hypergeometricWeight nControl nTreatment total k := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k in_range outside_support
      by_cases control_le : k ≤ nControl
      · have treatment_lt : nTreatment < total - k := by
          by_contra! treatment_le
          exact outside_support (Finset.mem_filter.mpr ⟨in_range, control_le, treatment_le⟩)
        simp [hypergeometricWeight, Nat.choose_eq_zero_of_lt treatment_lt]
      · simp [hypergeometricWeight, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge control_le)]
    _ = (nControl + nTreatment).choose total := vandermonde

/-- For every feasible pooled count, the conditional masses sum to one. -/
theorem hypergeometricMass_sum_one (nControl nTreatment total : ℕ)
    (feasible : total ≤ nControl + nTreatment) :
    (∑ k ∈ hypergeometricSupport nControl nTreatment total,
      hypergeometricMass nControl nTreatment total k) = 1 := by
  have weights : (∑ k ∈ hypergeometricSupport nControl nTreatment total,
      (hypergeometricWeight nControl nTreatment total k : ℚ)) =
      ((nControl + nTreatment).choose total : ℚ) := by
    exact_mod_cast hypergeometricWeight_sum nControl nTreatment total
  simp only [hypergeometricMass, ← Finset.sum_div]
  rw [weights, div_self (ne_of_gt (hypergeometric_denominator_pos _ _ _ feasible))]

/-- Rational probability ordering is exactly integer weight ordering. -/
theorem hypergeometricMass_le_iff (nControl nTreatment total k observed : ℕ)
    (feasible : total ≤ nControl + nTreatment) :
    hypergeometricMass nControl nTreatment total k ≤
        hypergeometricMass nControl nTreatment total observed ↔
      hypergeometricWeight nControl nTreatment total k ≤
        hypergeometricWeight nControl nTreatment total observed := by
  simp only [hypergeometricMass,
    div_le_div_iff_of_pos_right (hypergeometric_denominator_pos _ _ _ feasible), Nat.cast_le]

/-- Probability-ordered, two-sided conditional p-value, with all ties included. -/
def hypergeometricPValue (nControl nTreatment total observed : ℕ) : ℚ :=
  probabilityOrderedPValue (hypergeometricSupport nControl nTreatment total)
    (hypergeometricMass nControl nTreatment total) observed

/-- Explicit integer formula used as the reference specification for the executable. -/
theorem hypergeometricPValue_eq_weight_ratio (nControl nTreatment total observed : ℕ)
    (feasible : total ≤ nControl + nTreatment) :
    hypergeometricPValue nControl nTreatment total observed =
      ((∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
        (fun k => hypergeometricWeight nControl nTreatment total k ≤
          hypergeometricWeight nControl nTreatment total observed),
        hypergeometricWeight nControl nTreatment total k : ℕ) : ℚ) /
        ((nControl + nTreatment).choose total : ℚ) := by
  unfold hypergeometricPValue probabilityOrderedPValue
  simp_rw [hypergeometricMass_le_iff nControl nTreatment total _ observed feasible]
  simp [hypergeometricMass, Nat.cast_sum, Finset.sum_div]

/-- The exact conditional rejection probability is at most the chosen threshold.
Use `hypergeometricMass_sum_one` to interpret this mass bound as a probability. -/
theorem hypergeometric_rejection_mass_le (nControl nTreatment total : ℕ)
    (alpha : ℚ) (alpha_nonnegative : 0 ≤ alpha) :
    (∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
      (fun k => hypergeometricPValue nControl nTreatment total k ≤ alpha),
      hypergeometricMass nControl nTreatment total k) ≤ alpha := by
  exact probabilityOrdered_rejection_mass_le _ _
    (fun k _ => hypergeometricMass_nonnegative nControl nTreatment total k)
    alpha alpha_nonnegative

/-- The conditional bound at the project's exact significance threshold. -/
theorem hypergeometric_rejection_mass_le_targetAlpha (nControl nTreatment total : ℕ) :
    (∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
      (fun k => hypergeometricPValue nControl nTreatment total k ≤ targetAlpha),
      hypergeometricMass nControl nTreatment total k) ≤ targetAlpha := by
  exact hypergeometric_rejection_mass_le _ _ _ targetAlpha targetAlpha_pos.le

end StatClaim
