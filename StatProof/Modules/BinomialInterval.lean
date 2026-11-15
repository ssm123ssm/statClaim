module

public import StatProof.Modules.OneSampleBinomial

/-!
Exact (Clopper–Pearson) confidence sets for a binomial proportion.

`coverage` is a general theorem: for every true rate, the confidence set
contains it with probability at least `1 - 2a`, where `a` is the tail level per
side. `interval_contains` shows that, for one observed count, the confidence
set lies inside a reported interval with rational endpoints; this needs two
kernel checks. A reported interval is therefore at least as wide as the exact
one, which preserves coverage.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.BinomialInterval

open MeasureTheory ProbabilityTheory

/-- An upper-tail p-value is valid: small values are correspondingly unlikely. -/
theorem upper_tail_valid (μ : Measure ℕ) [IsProbabilityMeasure μ] (a : ℝ) (nonnegative : 0 ≤ a) :
    μ.real {x | μ.real (Set.Ici x) ≤ a} ≤ a := by
  classical
  by_cases some : ∃ x, μ.real (Set.Ici x) ≤ a
  · refine le_trans (measureReal_mono ?_) (Nat.find_spec some)
    intro x member
    exact Nat.find_min' some member
  · have empty : {x | μ.real (Set.Ici x) ≤ a} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x member => some ⟨x, member⟩)
    rw [empty, measureReal_empty]
    exact nonnegative

/-- The same for a lower-tail p-value, when all mass lies at or below `bound`. -/
theorem lower_tail_valid (μ : Measure ℕ) [IsProbabilityMeasure μ] (bound : ℕ)
    (full : μ.real (Set.Iic bound) = 1) (a : ℝ) (nonnegative : 0 ≤ a) :
    μ.real {x | μ.real (Set.Iic x) ≤ a} ≤ a := by
  classical
  by_cases large : 1 ≤ a
  · refine le_trans (measureReal_mono (Set.subset_univ _)) ?_
    rw [probReal_univ]
    exact large
  · by_cases some : ∃ x, μ.real (Set.Iic x) ≤ a
    · obtain ⟨witness, witness_small⟩ := some
      have below : ∀ x, μ.real (Set.Iic x) ≤ a → x ≤ bound := by
        intro x small
        by_contra beyond
        have mono : μ.real (Set.Iic bound) ≤ μ.real (Set.Iic x) :=
          measureReal_mono (Set.Iic_subset_Iic.mpr (by omega))
        rw [full] at mono
        exact large (mono.trans small)
      have greatest : μ.real (Set.Iic
          (Nat.findGreatest (fun x => μ.real (Set.Iic x) ≤ a) bound)) ≤ a :=
        Nat.findGreatest_spec (P := fun x => μ.real (Set.Iic x) ≤ a)
          (below witness witness_small) witness_small
      refine le_trans (measureReal_mono ?_) greatest
      intro x member
      exact Nat.le_findGreatest (below x member) member
    · have empty : {x | μ.real (Set.Iic x) ≤ a} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun x member => some ⟨x, member⟩)
      rw [empty, measureReal_empty]
      exact nonnegative

theorem binomial_full (n : ℕ) (p : unitInterval) : (binomial n p).real (Set.Iic n) = 1 := by
  have range_eq : (↑(Finset.range (n + 1)) : Set ℕ) = Set.Iic n := by
    ext k
    simp only [Finset.mem_coe, Finset.mem_range, Set.mem_Iic, Nat.lt_succ_iff]
  rw [← range_eq, ← sum_measureReal_singleton]
  simp only [← binomialMass_eq_mathlib]
  exact binomialMass_sum_one n (p : ℝ)

/-- The exact confidence set at tail level `a` per side: rates not rejected by
either one-sided exact test. -/
def confidenceSet (n : ℕ) (a : ℝ) (x : ℕ) : Set unitInterval :=
  {p | a < (binomial n p).real (Set.Ici x) ∧ a < (binomial n p).real (Set.Iic x)}

/-- Coverage: whatever the true rate, the confidence set contains it with
probability at least `1 - 2a`. -/
theorem coverage (n : ℕ) (a : ℝ) (nonnegative : 0 ≤ a) (p : unitInterval) :
    1 - 2 * a ≤ (binomial n p).real {x | p ∈ confidenceSet n a x} := by
  have miss : (binomial n p).real {x | p ∈ confidenceSet n a x}ᶜ ≤ a + a := by
    have subset : {x | p ∈ confidenceSet n a x}ᶜ ⊆
        {x | (binomial n p).real (Set.Ici x) ≤ a} ∪
          {x | (binomial n p).real (Set.Iic x) ≤ a} := by
      intro x outside
      by_contra neither
      rw [Set.mem_union, not_or] at neither
      have upper : ¬ (binomial n p).real (Set.Ici x) ≤ a := neither.1
      have lower : ¬ (binomial n p).real (Set.Iic x) ≤ a := neither.2
      exact outside ⟨not_le.mp upper, not_le.mp lower⟩
    exact (measureReal_mono subset).trans ((measureReal_union_le _ _).trans
      (add_le_add (upper_tail_valid _ a nonnegative)
        (lower_tail_valid _ n (binomial_full n p) a nonnegative)))
  have total := measureReal_compl (μ := binomial n p)
    (s := {x | p ∈ confidenceSet n a x}) .of_discrete
  rw [probReal_univ] at total
  linarith

/-- Lower tails become less likely as the rate increases. -/
theorem binomial_real_Iic_antitone (n : ℕ) (p q : unitInterval) (h : p ≤ q) (x : ℕ) :
    (binomial n q).real (Set.Iic x) ≤ (binomial n p).real (Set.Iic x) := by
  have complement : ∀ r : unitInterval,
      (binomial n r).real (Set.Iic x) = 1 - (binomial n r).real (Set.Ici (x + 1)) := by
    intro r
    have total := measureReal_compl (μ := binomial n r) (s := Set.Ici (x + 1)) .of_discrete
    rw [probReal_univ] at total
    rw [← total]
    congr 1
    ext y
    simp only [Set.mem_Iic, Set.mem_compl_iff, Set.mem_Ici]
    omega
  rw [complement p, complement q]
  have upper := binomial_real_mono n p q h (Set.Ici (x + 1))
    (fun _ _ ab member => Set.mem_Ici.mpr (le_trans (Set.mem_Ici.mp member) ab))
  linarith

/-- Integer numerator of the lower tail at rate a/d; the denominator is d ^ n. -/
def lowerNumerator (n a d x : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if k ≤ x then binomialWeight n a d k else 0

theorem upper_tail_ratPoint (n x a d : ℕ) (le : a ≤ d) (positive : 0 < d) :
    (binomial n (ratPoint a d le positive)).real (Set.Ici x) =
      (OneSampleBinomial.tailNumerator n a d x : ℝ) / ((d ^ n : ℕ) : ℝ) := by
  have key := OneSampleBinomial.rejection_probability ⟨n, x⟩ a d le positive
  rw [OneSampleBinomial.law_eq] at key
  exact key

theorem lower_tail_ratPoint (n x a d : ℕ) (le : a ≤ d) (positive : 0 < d) :
    (binomial n (ratPoint a d le positive)).real (Set.Iic x) =
      (lowerNumerator n a d x : ℝ) / ((d ^ n : ℕ) : ℝ) := by
  classical
  rw [binomial_real_eq_expectation]
  simp only [binomialExpectation, lowerNumerator, Nat.cast_sum, Finset.sum_div, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro k k_mem
  rw [binomialMass_ratPoint n a d k le positive
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp k_mem))]
  by_cases small : k ≤ x
  · simp [small]
  · simp [small]

/-- For one observed count, the confidence set lies inside the interval with
the given rational endpoints. Each side is either trivial (0 or 1) or
established by one natural-number comparison. -/
theorem interval_contains (n x aNum aDen : ℕ) (aDen_pos : 0 < aDen)
    (lNum lDen : ℕ) (lower_le : lNum ≤ lDen) (lower_pos : 0 < lDen)
    (uNum uDen : ℕ) (upper_le : uNum ≤ uDen) (upper_pos : 0 < uDen)
    (lowerCheck : lNum = 0 ∨
      OneSampleBinomial.tailNumerator n lNum lDen x * aDen ≤ aNum * lDen ^ n)
    (upperCheck : uNum = uDen ∨ lowerNumerator n uNum uDen x * aDen ≤ aNum * uDen ^ n)
    (p : unitInterval) (member : p ∈ confidenceSet n ((aNum : ℝ) / aDen) x) :
    ratPoint lNum lDen lower_le lower_pos ≤ p ∧ p ≤ ratPoint uNum uDen upper_le upper_pos := by
  constructor
  · rcases lowerCheck with zero | check
    · apply Subtype.coe_le_coe.mp
      simp only [ratPoint, zero, Nat.cast_zero, zero_div]
      exact p.property.1
    · by_contra above
      have below : p ≤ ratPoint lNum lDen lower_le lower_pos := le_of_lt (not_le.mp above)
      have tail := binomial_real_mono n p _ below (Set.Ici x)
        (fun _ _ ab inside => Set.mem_Ici.mpr (le_trans (Set.mem_Ici.mp inside) ab))
      rw [upper_tail_ratPoint] at tail
      exact absurd member.1 (not_lt.mpr (tail.trans
        (ratio_le_of_check _ _ _ _ (Nat.pow_pos lower_pos) aDen_pos check)))
  · rcases upperCheck with one | check
    · apply Subtype.coe_le_coe.mp
      have positive : (uDen : ℝ) ≠ 0 := by exact_mod_cast upper_pos.ne'
      simp only [ratPoint, one, div_self positive]
      exact p.property.2
    · by_contra below
      have above : ratPoint uNum uDen upper_le upper_pos ≤ p := le_of_lt (not_le.mp below)
      have tail := binomial_real_Iic_antitone n _ p above x
      rw [lower_tail_ratPoint] at tail
      exact absurd member.2 (not_lt.mpr (tail.trans
        (ratio_le_of_check _ _ _ _ (Nat.pow_pos upper_pos) aDen_pos check)))

end StatProof.Modules.BinomialInterval
