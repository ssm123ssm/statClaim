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

/-- The exact one-sided p-value of an observed count is the upper tail at the
null rate. A proposed fraction is confirmed by one cross-multiplication. -/
theorem pValue_eq_of_cross_product (n observed a d : ℕ) (le : a ≤ d) (positive : 0 < d)
    (numerator denominator : ℕ) (denominator_pos : 0 < denominator)
    (cross : tailNumerator n a d observed * denominator = numerator * d ^ n) :
    ((policy ⟨n, observed⟩).law (ratPoint a d le positive)).real {count | observed ≤ count} =
      (numerator : ℝ) / denominator := by
  refine (rejection_probability ⟨n, observed⟩ a d le positive).trans ?_
  dsimp only
  rw [div_eq_div_iff (by exact_mod_cast (Nat.pow_pos positive).ne')
    (by exact_mod_cast denominator_pos.ne')]
  exact_mod_cast cross

/-- The smallest response count whose upper tail at rate a/d is at most
`levelNum/levelDen`; `n + 1` (never reject) if there is none. -/
def criticalValue (n a d levelNum levelDen : ℕ) : ℕ :=
  ((List.range (n + 1)).find? (fun critical =>
    decide (tailNumerator n a d critical * levelDen ≤ levelNum * d ^ n))).getD (n + 1)

/-- The test at level `levelNum/levelDen` with the given sample size. -/
def levelDesign (n a d levelNum levelDen : ℕ) : Design :=
  ⟨n, criticalValue n a d levelNum levelDen⟩

/-- Every sample size from `low` up to, but excluding, `high` either exceeds the
error bound at the null rate or falls short of the power bound. -/
def SmallerFail (low high a d levelNum levelDen maxNum maxDen b e boundNum boundDen : ℕ) : Prop :=
  ∀ n, n < high → low ≤ n →
    maxNum * d ^ n < tailNumerator n a d (criticalValue n a d levelNum levelDen) * maxDen ∨
      tailNumerator n b e (criticalValue n a d levelNum levelDen) * boundDen < boundNum * e ^ n

instance (low high a d levelNum levelDen maxNum maxDen b e boundNum boundDen : ℕ) :
    Decidable (SmallerFail low high a d levelNum levelDen maxNum maxDen b e boundNum boundDen) := by
  unfold SmallerFail
  infer_instance

/-- No smaller candidate meets both targets. -/
theorem fails_of_smallerFail (a d : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (levelNum levelDen : ℕ)
    (maxNum maxDen : ℕ) (maxDen_pos : 0 < maxDen) (b e : ℕ) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen) (low high : ℕ)
    (check : SmallerFail low high a d levelNum levelDen maxNum maxDen b e boundNum boundDen)
    (n : ℕ) (lower : low ≤ n) (upper : n < high) :
    (maxNum : ℝ) / maxDen <
        ((policy (levelDesign n a d levelNum levelDen)).law (ratPoint a d le₁ positive₁)).real
          {count | (levelDesign n a d levelNum levelDen).critical ≤ count} ∨
      ((policy (levelDesign n a d levelNum levelDen)).law (ratPoint b e le₂ positive₂)).real
          {count | (levelDesign n a d levelNum levelDen).critical ≤ count} <
        (boundNum : ℝ) / boundDen := by
  rw [rejection_probability, rejection_probability]
  rcases check n upper lower with error | power
  · left
    rw [div_lt_div_iff₀ (by exact_mod_cast maxDen_pos)
      (by exact_mod_cast Nat.pow_pos positive₁)]
    exact_mod_cast error
  · right
    exact ratio_lt_of_check _ _ _ _ (Nat.pow_pos positive₂) boundDen_pos power

end StatProof.Modules.OneSampleBinomial
