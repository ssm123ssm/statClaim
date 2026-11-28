module

public import StatClaim.BinomialMonotone

/-! The two-sided score statistic for a fixed reference rate in a binomial sample. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.OneSampleScore

open MeasureTheory ProbabilityTheory

/-- Compare the squared difference to the cutoff times the null variance.
The score test uses the reference rate in its variance. -/
def rejects (n : ℕ) (reference cutoff : ℚ) (count : ℕ) : Prop :=
  cutoff * reference * (1 - reference) / n < ((count : ℚ) / n - reference) ^ 2

instance (n : ℕ) (reference cutoff : ℚ) (count : ℕ) :
    Decidable (rejects n reference cutoff count) := by
  unfold rejects
  infer_instance

def rejection (n : ℕ) (reference cutoff : ℚ) : Set ℕ :=
  {count | rejects n reference cutoff count}

theorem rejection_iff_real (n : ℕ) (reference cutoff : ℚ) (count : ℕ) :
    count ∈ rejection n reference cutoff ↔
      (cutoff : ℝ) * (reference : ℝ) * (1 - (reference : ℝ)) / n <
        ((count : ℝ) / n - (reference : ℝ)) ^ 2 := by
  change rejects n reference cutoff count ↔ _
  unfold rejects
  have h := Rat.cast_lt (K := ℝ) (p := cutoff * reference * (1 - reference) / n)
    (q := ((count : ℚ) / n - reference) ^ 2)
  push_cast at h
  exact h.symm

def numerator (n a d : ℕ) (cutoff : ℚ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    if rejects n ((a : ℚ) / d) cutoff k then binomialWeight n a d k else 0

/-- All feasible count probabilities have denominator `d ^ n`. -/
theorem probability (n a d : ℕ) (cutoff : ℚ) (ha : a ≤ d) (hd : 0 < d) :
    (binomial n (ratPoint a d ha hd)).real (rejection n ((a : ℚ) / d) cutoff) =
      (numerator n a d cutoff : ℝ) / (d ^ n : ℕ) := by
  classical
  rw [binomial_real_eq_expectation]
  simp only [binomialExpectation, numerator, Nat.cast_sum, Finset.sum_div, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [binomialMass_ratPoint n a d k ha hd (by simpa using hk)]
  by_cases h : rejects n ((a : ℚ) / d) cutoff k <;> simp [rejection, h]

end StatClaim.Modules.OneSampleScore
