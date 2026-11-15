module

public import StatProof.Core.Policy
public import StatProof.BinomialMonotone

/-!
The one-sided exact binomial test for a single arm: reject when the number of
responses reaches a critical value. The null is every response rate at or
below a reference rate. The Type I bound is checked at the reference rate and
extended to all smaller rates by monotonicity.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.OneSampleBinomial

open MeasureTheory

/-- Sample size and the smallest response count that rejects. -/
structure Design where
  n : ℕ
  critical : ℕ

noncomputable def policy (design : Design) : Core.Policy unitInterval ℕ ℕ where
  potentialLaw := fun rate => ProbabilityTheory.binomial design.n rate
  probability := fun _ => inferInstance
  record := id
  record_measurable := measurable_id

/-- Null: the response rate is at most the reference rate. -/
noncomputable def analysis (design : Design) (nullRate : unitInterval) :
    Core.PolicyAnalysis (policy design) where
  hypothesis := fun rate => rate ≤ nullRate
  rejection := {count | design.critical ≤ count}
  rejection_measurable := .of_discrete

/-- Integer numerator of the upper tail at rate a/d; the denominator is d ^ n. -/
def tailNumerator (n a d critical : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if critical ≤ k then binomialWeight n a d k else 0

theorem law_eq (design : Design) (rate : unitInterval) :
    ((policy design).law rate).real {count | design.critical ≤ count} =
      (ProbabilityTheory.binomial design.n rate).real {count | design.critical ≤ count} := by
  rw [Core.Policy.law_real_apply _ _ .of_discrete]
  rfl

theorem rejection_probability (design : Design) (a d : ℕ) (le : a ≤ d) (positive : 0 < d) :
    ((policy design).law (ratPoint a d le positive)).real {count | design.critical ≤ count} =
      (tailNumerator design.n a d design.critical : ℝ) / ((d ^ design.n : ℕ) : ℝ) := by
  classical
  rw [law_eq, binomial_real_eq_expectation]
  simp only [binomialExpectation, tailNumerator, Nat.cast_sum, Finset.sum_div, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro k k_mem
  rw [binomialMass_ratPoint design.n a d k le positive
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp k_mem))]
  by_cases reject : design.critical ≤ k
  · simp [reject]
  · simp [reject]

/-- Type I error for every rate at or below the reference, from one check. -/
theorem typeI_of_check (design : Design) (a d : ℕ) (le : a ≤ d) (positive : 0 < d)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : tailNumerator design.n a d design.critical * boundDen ≤
      boundNum * d ^ design.n) :
    ((analysis design (ratPoint a d le positive)).typeIClaim
      ((boundNum : ℝ) / boundDen)).statement := by
  intro rate null
  change ((policy design).law rate).real {count | design.critical ≤ count} ≤ _
  refine le_trans ?_ (le_trans (rejection_probability design a d le positive).le
    (ratio_le_of_check _ _ _ _ (Nat.pow_pos positive) boundDen_pos check))
  rw [law_eq, law_eq]
  exact binomial_real_mono design.n rate _ null _ (fun _ _ ab member => le_trans member ab)

/-- Power at one declared rate, from one check. -/
theorem power_of_check (design : Design) (nullRate : unitInterval) (a d : ℕ) (le : a ≤ d)
    (positive : 0 < d) (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * d ^ design.n ≤
      tailNumerator design.n a d design.critical * boundDen) :
    ((analysis design nullRate).powerClaim (fun rate => rate = ratPoint a d le positive)
      ((boundNum : ℝ) / boundDen)).statement := by
  intro rate alternative
  rw [show rate = ratPoint a d le positive from alternative]
  change _ ≤ ((policy design).law _).real {count | design.critical ≤ count}
  rw [rejection_probability]
  exact le_ratio_of_check _ _ _ _ (Nat.pow_pos positive) boundDen_pos check

end StatProof.Modules.OneSampleBinomial
