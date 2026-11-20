module

public import StatClaim.Fisher

/-!
Fisher's exact test of no association in an observational 2×2 study.

A cohort study fixes how many exposed and unexposed participants are followed; a
case-control study fixes how many cases and controls are sampled. Either way the
table holds two independent binomial counts, and no association makes their
success probabilities equal. That is the model of `StatClaim.Fisher`, with the
two groups in place of arms, so `groups_typeI_le_alpha` is Fisher's theorem.

A cross-sectional study, or a cohort that does not fix how many are exposed, fixes
only the total. Under independent sampling the number exposed is binomial, and
under no association the outcome counts given that number are two independent
binomials with a common probability. Fisher's test uses the number exposed as
observed. Given it, the test rejects with probability at most alpha, so the
average over the number exposed is at most alpha too: `mixture_typeI_le_alpha`.

No theorem here concerns cause: exposure was not assigned.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Association

open MeasureTheory

/-- Fixed groups: Fisher's bound, for every common probability in [0, 1]. -/
theorem groups_typeI_le_alpha (first second : ℕ) (p : unitInterval) (alpha : ℚ)
    (alpha_nonnegative : 0 ≤ alpha) :
    (fisherNullLaw first second p).real (fisherRejectionRegionAt first second alpha) ≤
      (alpha : ℝ) :=
  fisher_typeI_error_le_alpha first second p alpha alpha_nonnegative

/-- A table of a sample whose number exposed is random: the number exposed, then the
outcome counts among the unexposed and among the exposed. -/
abbrev Table := ℕ × (ℕ × ℕ)

/-- Its law under no association: `n` participants, each exposed with probability `q`;
given `k` exposed, the outcome counts are independent binomials with common probability
`p`, among `n - k` unexposed and `k` exposed. -/
noncomputable def mixtureLaw (n : ℕ) (q p : unitInterval) : Measure Table :=
  ∑ k ∈ Finset.range (n + 1),
    ENNReal.ofReal (binomialMass n (q : ℝ) k) •
      (Measure.dirac k).prod (fisherNullLaw (n - k) k p)

/-- Fisher's test applied to the observed table, with the observed group sizes. -/
def mixtureRejection (n : ℕ) (alpha : ℚ) : Set Table :=
  {table | table.1 ≤ n ∧ table.2 ∈ fisherRejectionRegionAt (n - table.1) table.1 alpha}

/-- One term of the mixture: the group sizes are fixed at `k`. -/
theorem term_apply (n k : ℕ) (k_le : k ≤ n) (p : unitInterval) (alpha : ℚ) :
    (Measure.dirac k).prod (fisherNullLaw (n - k) k p) (mixtureRejection n alpha) =
      fisherNullLaw (n - k) k p (fisherRejectionRegionAt (n - k) k alpha) := by
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (.of_discrete)]
  congr 1
  ext counts
  simp [mixtureRejection, k_le]

/-- Given the number exposed, the test rejects with probability at most alpha. -/
theorem term_le (n k : ℕ) (p : unitInterval) (alpha : ℚ) (alpha_nonnegative : 0 ≤ alpha) :
    fisherNullLaw (n - k) k p (fisherRejectionRegionAt (n - k) k alpha) ≤
      ENNReal.ofReal (alpha : ℝ) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (groups_typeI_le_alpha (n - k) k p alpha alpha_nonnegative)

theorem weights_sum (n : ℕ) (q : unitInterval) :
    ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (binomialMass n (q : ℝ) k) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun k _ => binomialMass_nonnegative n (q : ℝ) k q.property.1 q.property.2),
    binomialMass_sum_one, ENNReal.ofReal_one]

/-- The mixture is a probability law. -/
theorem mixtureLaw_univ (n : ℕ) (q p : unitInterval) : mixtureLaw n q p Set.univ = 1 := by
  simp only [mixtureLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  exact weights_sum n q

instance mixtureLaw_isProbabilityMeasure (n : ℕ) (q p : unitInterval) :
    IsProbabilityMeasure (mixtureLaw n q p) :=
  ⟨mixtureLaw_univ n q p⟩

/-- With the number exposed random, Fisher's test of no association has Type I error at
most alpha, for every exposure probability and every common outcome probability. -/
theorem mixture_typeI_le_alpha (n : ℕ) (q p : unitInterval) (alpha : ℚ)
    (alpha_nonnegative : 0 ≤ alpha) :
    (mixtureLaw n q p).real (mixtureRejection n alpha) ≤ (alpha : ℝ) := by
  have bound : mixtureLaw n q p (mixtureRejection n alpha) ≤ ENNReal.ofReal (alpha : ℝ) := by
    simp only [mixtureLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul]
    calc
      _ = ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (binomialMass n (q : ℝ) k) *
            fisherNullLaw (n - k) k p (fisherRejectionRegionAt (n - k) k alpha) := by
        apply Finset.sum_congr rfl
        intro k member
        rw [term_apply n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp member))]
      _ ≤ ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (binomialMass n (q : ℝ) k) *
            ENNReal.ofReal (alpha : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        gcongr
        exact term_le n k p alpha alpha_nonnegative
      _ = ENNReal.ofReal (alpha : ℝ) := by
        rw [← Finset.sum_mul, weights_sum, one_mul]
  exact ENNReal.toReal_le_of_le_ofReal (by exact_mod_cast alpha_nonnegative) bound

end StatClaim.Modules.Association
