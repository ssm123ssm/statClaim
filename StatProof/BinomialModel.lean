module

public import StatProof.Hypergeometric
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
Finite independent-binomial null model. The two success counts have the product
of their binomial masses, with a common real success probability in [0, 1].
Partitioning this finite sample space by the pooled success count connects it
to the normalized rational hypergeometric law, without conditioning on an event
of probability zero. Consequently the algebra also covers p = 0 and p = 1.
-/

@[expose] public section

namespace StatProof

/-- Binomial point mass as a real number. -/
def binomialMass (n : ℕ) (p : ℝ) (successes : ℕ) : ℝ :=
  (n.choose successes : ℝ) * p ^ successes * (1 - p) ^ (n - successes)

theorem binomialMass_nonnegative (n : ℕ) (p : ℝ) (successes : ℕ)
    (p_nonnegative : 0 ≤ p) (p_le_one : p ≤ 1) :
    0 ≤ binomialMass n p successes := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg p_nonnegative _))
    (pow_nonneg (sub_nonneg.mpr p_le_one) _)

/-- Normalization is exactly the binomial theorem, including both endpoints. -/
theorem binomialMass_sum_one (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (n + 1), binomialMass n p k) = 1 := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      unfold binomialMass
      ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by simp

/-- All pairs of success counts admitted by the two arm sizes. -/
def binomialCountSupport (nControl nTreatment : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (nControl + 1) ×ˢ Finset.range (nTreatment + 1)

/-- Product point mass: this is where independence and the equal-proportions
null enter the finite model. -/
def independentBinomialMass (nControl nTreatment : ℕ) (p : ℝ) (counts : ℕ × ℕ) : ℝ :=
  binomialMass nControl p counts.1 * binomialMass nTreatment p counts.2

theorem independentBinomialMass_nonnegative (nControl nTreatment : ℕ) (p : ℝ)
    (counts : ℕ × ℕ) (p_nonnegative : 0 ≤ p) (p_le_one : p ≤ 1) :
    0 ≤ independentBinomialMass nControl nTreatment p counts := by
  exact mul_nonneg (binomialMass_nonnegative _ p _ p_nonnegative p_le_one)
    (binomialMass_nonnegative _ p _ p_nonnegative p_le_one)

/-- The independent joint masses define a normalized finite distribution. -/
theorem independentBinomialMass_sum_one (nControl nTreatment : ℕ) (p : ℝ) :
    (∑ counts ∈ binomialCountSupport nControl nTreatment,
      independentBinomialMass nControl nTreatment p counts) = 1 := by
  simp only [binomialCountSupport, Finset.sum_product, independentBinomialMass]
  simp_rw [← Finset.mul_sum, binomialMass_sum_one, mul_one]
  exact binomialMass_sum_one nControl p

/-- Every legal pair occurs exactly once in the partition by pooled successes. -/
theorem sum_binomialCountSupport_by_total (nControl nTreatment : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ counts ∈ binomialCountSupport nControl nTreatment, f counts) =
      ∑ total ∈ Finset.range (nControl + nTreatment + 1),
        ∑ k ∈ hypergeometricSupport nControl nTreatment total, f (k, total - k) := by
  classical
  have maps : ∀ counts ∈ binomialCountSupport nControl nTreatment,
      counts.1 + counts.2 ∈ Finset.range (nControl + nTreatment + 1) := by
    intro counts counts_mem
    simp only [binomialCountSupport, Finset.mem_product, Finset.mem_range] at counts_mem
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to maps f]
  apply Finset.sum_congr rfl
  intro total _
  symm
  refine Finset.sum_bij (fun k _ => (k, total - k)) ?_ ?_ ?_ ?_
  · intro k k_mem
    simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range] at k_mem
    simp only [binomialCountSupport, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · intro k _ l _ pair_eq
    exact congrArg Prod.fst pair_eq
  · intro counts counts_mem
    simp only [binomialCountSupport, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at counts_mem
    refine ⟨counts.1, ?_, ?_⟩
    · simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range]
      omega
    · apply Prod.ext
      · rfl
      · dsimp
        omega
  · intro k _
    rfl

/-- Factor the joint point mass into a pooled binomial mass and a conditional
hypergeometric mass. No division by p, 1-p, or pooled event probability occurs. -/
theorem independentBinomialMass_factorization (nControl nTreatment total k : ℕ) (p : ℝ)
    (feasible : total ≤ nControl + nTreatment)
    (in_support : k ∈ hypergeometricSupport nControl nTreatment total) :
    independentBinomialMass nControl nTreatment p (k, total - k) =
      binomialMass (nControl + nTreatment) p total *
        (hypergeometricMass nControl nTreatment total k : ℝ) := by
  have bounds := in_support
  simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range] at bounds
  have successes : k + (total - k) = total := by omega
  have failures : nControl - k + (nTreatment - (total - k)) =
      nControl + nTreatment - total := by omega
  have denominator_ne : ((nControl + nTreatment).choose total : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos feasible))
  calc
    _ = (hypergeometricWeight nControl nTreatment total k : ℝ) *
        (p ^ k * p ^ (total - k)) *
        ((1 - p) ^ (nControl - k) * (1 - p) ^ (nTreatment - (total - k))) := by
      simp only [independentBinomialMass, binomialMass, hypergeometricWeight, Nat.cast_mul]
      ring
    _ = (hypergeometricWeight nControl nTreatment total k : ℝ) *
        p ^ total * (1 - p) ^ (nControl + nTreatment - total) := by
      rw [← pow_add, ← pow_add, successes, failures]
    _ = _ := by
      simp only [binomialMass, hypergeometricMass, Rat.cast_div, Rat.cast_natCast]
      field_simp [denominator_ne]

/-- The pooled success count has the binomial mass for the combined sample. -/
theorem independentBinomialMass_pooled_sum (nControl nTreatment total : ℕ) (p : ℝ)
    (feasible : total ≤ nControl + nTreatment) :
    (∑ k ∈ hypergeometricSupport nControl nTreatment total,
      independentBinomialMass nControl nTreatment p (k, total - k)) =
      binomialMass (nControl + nTreatment) p total := by
  have normalized : (∑ k ∈ hypergeometricSupport nControl nTreatment total,
      (hypergeometricMass nControl nTreatment total k : ℝ)) = 1 := by
    exact_mod_cast hypergeometricMass_sum_one nControl nTreatment total feasible
  calc
    _ = ∑ k ∈ hypergeometricSupport nControl nTreatment total,
        binomialMass (nControl + nTreatment) p total *
          (hypergeometricMass nControl nTreatment total k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact independentBinomialMass_factorization _ _ _ _ p feasible hk
    _ = _ := by rw [← Finset.mul_sum, normalized, mul_one]

/-- At a positive-probability pooled total, the usual finite conditional
point probability is exactly the rational hypergeometric mass. -/
theorem independentBinomialMass_conditional (nControl nTreatment total k : ℕ) (p : ℝ)
    (feasible : total ≤ nControl + nTreatment)
    (in_support : k ∈ hypergeometricSupport nControl nTreatment total)
    (pooled_positive : 0 < binomialMass (nControl + nTreatment) p total) :
    independentBinomialMass nControl nTreatment p (k, total - k) /
      (∑ j ∈ hypergeometricSupport nControl nTreatment total,
        independentBinomialMass nControl nTreatment p (j, total - j)) =
      (hypergeometricMass nControl nTreatment total k : ℝ) := by
  rw [independentBinomialMass_pooled_sum _ _ _ p feasible,
    independentBinomialMass_factorization _ _ _ _ p feasible in_support,
    mul_div_cancel_left₀ _ (ne_of_gt pooled_positive)]

/-- Exact null rejection probability in the finite independent-binomial model. -/
def fisherNullRejectionProbability (nControl nTreatment : ℕ) (p : ℝ) : ℝ :=
  ∑ counts ∈ binomialCountSupport nControl nTreatment,
    if hypergeometricPValue nControl nTreatment (counts.1 + counts.2) counts.1 ≤ targetAlpha
    then independentBinomialMass nControl nTreatment p counts else 0

/-- Uniform Type I error bound for the specified finite independent-binomial
null model. The closed interval includes p = 0 and p = 1. -/
theorem fisherNullRejectionProbability_le_alpha (nControl nTreatment : ℕ) (p : ℝ)
    (p_nonnegative : 0 ≤ p) (p_le_one : p ≤ 1)
    (alpha : ℚ) (alpha_nonnegative : 0 ≤ alpha) :
    (∑ counts ∈ binomialCountSupport nControl nTreatment,
      if hypergeometricPValue nControl nTreatment (counts.1 + counts.2) counts.1 ≤ alpha
      then independentBinomialMass nControl nTreatment p counts else 0) ≤ (alpha : ℝ) := by
  classical
  rw [sum_binomialCountSupport_by_total]
  calc
    _ ≤ ∑ total ∈ Finset.range (nControl + nTreatment + 1),
        binomialMass (nControl + nTreatment) p total * (alpha : ℝ) := by
      apply Finset.sum_le_sum
      intro total total_mem
      have feasible : total ≤ nControl + nTreatment := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using total_mem
      have conditional_bound :
          (∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
            (fun k => hypergeometricPValue nControl nTreatment total k ≤ alpha),
            (hypergeometricMass nControl nTreatment total k : ℝ)) ≤ (alpha : ℝ) := by
        exact_mod_cast hypergeometric_rejection_mass_le nControl nTreatment total alpha alpha_nonnegative
      calc
        _ = binomialMass (nControl + nTreatment) p total *
            ∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter
              (fun k => hypergeometricPValue nControl nTreatment total k ≤ alpha),
              (hypergeometricMass nControl nTreatment total k : ℝ) := by
          rw [Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k k_mem
          have bounds := k_mem
          simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range] at bounds
          have pooled : k + (total - k) = total := by omega
          simp only [pooled, mul_ite, mul_zero]
          split_ifs with reject
          · exact independentBinomialMass_factorization _ _ _ _ p feasible k_mem
          · rfl
        _ ≤ _ := mul_le_mul_of_nonneg_left conditional_bound
          (binomialMass_nonnegative _ p total p_nonnegative p_le_one)
    _ = (alpha : ℝ) := by
      rw [← Finset.sum_mul, binomialMass_sum_one, one_mul]

/-- Compatibility specialization at the default significance level. -/
theorem fisherNullRejectionProbability_le_targetAlpha (nControl nTreatment : ℕ) (p : ℝ)
    (p_nonnegative : 0 ≤ p) (p_le_one : p ≤ 1) :
    fisherNullRejectionProbability nControl nTreatment p ≤ (targetAlpha : ℝ) :=
  fisherNullRejectionProbability_le_alpha nControl nTreatment p p_nonnegative p_le_one
    targetAlpha targetAlpha_pos.le


/-- Any test that rejects with conditional probability at most `alpha` at every
pooled success count rejects with probability at most `alpha` when the two arms
share one success probability. -/
theorem conditionalTest_rejection_le (nControl nTreatment : ℕ) (p : ℝ)
    (p_nonnegative : 0 ≤ p) (p_le_one : p ≤ 1) (alpha : ℚ)
    (reject : ℕ → ℕ → Prop) [∀ total k, Decidable (reject total k)]
    (conditional : ∀ total,
      (∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter (reject total),
        hypergeometricMass nControl nTreatment total k) ≤ alpha) :
    (∑ counts ∈ binomialCountSupport nControl nTreatment,
      if reject (counts.1 + counts.2) counts.1
      then independentBinomialMass nControl nTreatment p counts else 0) ≤ (alpha : ℝ) := by
  rw [sum_binomialCountSupport_by_total]
  calc
    _ ≤ ∑ total ∈ Finset.range (nControl + nTreatment + 1),
        binomialMass (nControl + nTreatment) p total * (alpha : ℝ) := by
      apply Finset.sum_le_sum
      intro total total_mem
      have feasible : total ≤ nControl + nTreatment := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using total_mem
      have conditional_bound :
          (∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter (reject total),
            (hypergeometricMass nControl nTreatment total k : ℝ)) ≤ (alpha : ℝ) := by
        exact_mod_cast conditional total
      calc
        _ = binomialMass (nControl + nTreatment) p total *
            ∑ k ∈ (hypergeometricSupport nControl nTreatment total).filter (reject total),
              (hypergeometricMass nControl nTreatment total k : ℝ) := by
          rw [Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k k_mem
          have bounds := k_mem
          simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range] at bounds
          have pooled : k + (total - k) = total := by omega
          simp only [pooled, mul_ite, mul_zero]
          split_ifs with rejected
          · exact independentBinomialMass_factorization _ _ _ _ p feasible k_mem
          · rfl
        _ ≤ _ := mul_le_mul_of_nonneg_left conditional_bound
          (binomialMass_nonnegative _ p total p_nonnegative p_le_one)
    _ = (alpha : ℝ) := by
      rw [← Finset.sum_mul, binomialMass_sum_one, one_mul]

end StatProof
