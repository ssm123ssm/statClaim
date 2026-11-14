import StatProof

open StatProof

-- Unequal arm sizes: the support bounds agree with the executable convention.
example : hypergeometricSupport 4 9 12 = {3, 4} := by decide

-- All mass functions are normalized for feasible totals, not just these examples.
example : (∑ k ∈ hypergeometricSupport 4 4 4, hypergeometricMass 4 4 4 k) = 1 :=
  hypergeometricMass_sum_one 4 4 4 (by norm_num)

-- Equal-probability opposite tails both contribute to the two-sided value.
example : hypergeometricMass 4 4 4 0 = 1 / 70 := by
  norm_num [hypergeometricMass, hypergeometricWeight,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]
example : hypergeometricPValue 4 4 4 0 = 1 / 35 := by
  have support : hypergeometricSupport 4 4 4 = {0, 1, 2, 3, 4} := by decide
  rw [hypergeometricPValue_eq_weight_ratio 4 4 4 0 (by norm_num)]
  rw [support]
  norm_num [hypergeometricWeight, Finset.filter_insert, Finset.filter_singleton,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

-- Rejection includes equality at the exact significance threshold.
private theorem boundary_value : hypergeometricPValue 1 19 19 0 = targetAlpha := by
  have support : hypergeometricSupport 1 19 19 = {0, 1} := by decide
  rw [hypergeometricPValue_eq_weight_ratio 1 19 19 0 (by norm_num)]
  rw [support]
  norm_num [hypergeometricWeight, Finset.filter_insert, Finset.filter_singleton, targetAlpha,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

example : (0, 19) ∈ fisherRejectionRegion 1 19 := by
  simp only [fisherRejectionRegion, Finset.mem_filter]
  exact ⟨by decide, le_of_eq boundary_value⟩

-- Degenerate pooled totals yield a p-value of one.
example : hypergeometricPValue 10 15 0 0 = 1 := by
  have support : hypergeometricSupport 10 15 0 = {0} := by decide
  rw [hypergeometricPValue_eq_weight_ratio 10 15 0 0 (by norm_num)]
  rw [support]
  norm_num [hypergeometricWeight, Finset.filter_insert, Finset.filter_singleton]
example : hypergeometricPValue 4 4 8 4 = 1 := by
  have support : hypergeometricSupport 4 4 8 = {4} := by decide
  rw [hypergeometricPValue_eq_weight_ratio 4 4 8 4 (by norm_num)]
  rw [support]
  norm_num [hypergeometricWeight, Finset.filter_insert, Finset.filter_singleton,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

-- These are instantiations of the general result, not numerical enumeration.
example (p : unitInterval) :
    (fisherNullLaw 100 100 p).real (fisherRejectionRegion 100 100) ≤ (1 / 20 : ℝ) :=
  fisher_typeI_error_le 100 100 p

example : (fisherNullLaw 10 20 ⟨0, by norm_num⟩).real (fisherRejectionRegion 10 20) ≤
    (1 / 20 : ℝ) :=
  fisher_typeI_error_le 10 20 ⟨0, by norm_num⟩

example : (fisherNullLaw 10 20 ⟨1, by norm_num⟩).real (fisherRejectionRegion 10 20) ≤
    (1 / 20 : ℝ) :=
  fisher_typeI_error_le 10 20 ⟨1, by norm_num⟩
