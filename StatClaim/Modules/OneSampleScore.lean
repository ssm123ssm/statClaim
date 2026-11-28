module

public import StatClaim.BinomialMonotone

/-! Two-sided score and Wald statistics for a fixed reference rate in a binomial sample. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.OneSampleScore

open MeasureTheory ProbabilityTheory

/-- Use the null variance for the score rule and the estimated variance for
the Wald rule. The comparison is defined directly even at zero variance. -/
def rejects (n : ℕ) (reference cutoff : ℚ) (count : ℕ) (estimated : Bool := false) : Prop :=
  let observed := (count : ℚ) / n
  let rate := if estimated then observed else reference
  cutoff * rate * (1 - rate) / n < (observed - reference) ^ 2

instance (n : ℕ) (reference cutoff : ℚ) (count : ℕ) (estimated : Bool) :
    Decidable (rejects n reference cutoff count estimated) := by
  unfold rejects
  infer_instance

def rejection (n : ℕ) (reference cutoff : ℚ) (estimated : Bool := false) : Set ℕ :=
  {count | rejects n reference cutoff count estimated}

theorem rejection_iff_real (n : ℕ) (reference cutoff : ℚ) (count : ℕ) :
    count ∈ rejection n reference cutoff ↔
      (cutoff : ℝ) * (reference : ℝ) * (1 - (reference : ℝ)) / n <
        ((count : ℝ) / n - (reference : ℝ)) ^ 2 := by
  change rejects n reference cutoff count ↔ _
  simp only [rejects, Bool.false_eq_true, ite_false]
  have h := Rat.cast_lt (K := ℝ) (p := cutoff * reference * (1 - reference) / n)
    (q := ((count : ℚ) / n - reference) ^ 2)
  push_cast at h
  exact h.symm

theorem wald_rejection_iff_real (n : ℕ) (reference cutoff : ℚ) (count : ℕ) :
    count ∈ rejection n reference cutoff true ↔
      let observed := (count : ℝ) / n
      (cutoff : ℝ) * observed * (1 - observed) / n < (observed - (reference : ℝ)) ^ 2 := by
  change rejects n reference cutoff count true ↔ _
  simp only [rejects, ite_true]
  have h := Rat.cast_lt (K := ℝ)
    (p := cutoff * ((count : ℚ) / n) * (1 - (count : ℚ) / n) / n)
    (q := ((count : ℚ) / n - reference) ^ 2)
  push_cast at h
  exact h.symm

def numerator (n a d : ℕ) (cutoff : ℚ) (estimated : Bool := false) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    if rejects n ((a : ℚ) / d) cutoff k estimated then binomialWeight n a d k else 0

/-- All feasible count probabilities have denominator `d ^ n`. -/
theorem probability (n a d : ℕ) (cutoff : ℚ) (ha : a ≤ d) (hd : 0 < d)
    (estimated : Bool := false) :
    (binomial n (ratPoint a d ha hd)).real (rejection n ((a : ℚ) / d) cutoff estimated) =
      (numerator n a d cutoff estimated : ℝ) / (d ^ n : ℕ) := by
  classical
  rw [binomial_real_eq_expectation]
  simp only [binomialExpectation, numerator, Nat.cast_sum, Finset.sum_div, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialMass_ratPoint n a d k ha hd (by simpa using hk)]
  by_cases h : rejects n ((a : ℚ) / d) cutoff k estimated <;> simp [rejection, h]

end StatClaim.Modules.OneSampleScore
