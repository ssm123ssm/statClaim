module

public import StatProof.Fisher

/-!
Two independent binomial counts with separately chosen success probabilities.
Probabilities of arbitrary events reduce to finite sums of point masses. At
rational success probabilities those sums are ratios of natural numbers, so a
specific design's rejection probability can be bounded by kernel arithmetic.
Nothing here asserts that real observations follow this law.
-/

@[expose] public section

namespace StatProof

open MeasureTheory

/-- Independent binomial counts; the two success probabilities may differ. -/
noncomputable def productBinomial (n m : ℕ) (p q : unitInterval) : Measure (ℕ × ℕ) :=
  (ProbabilityTheory.binomial n p).prod (ProbabilityTheory.binomial m q)

instance productBinomial_isProbabilityMeasure (n m : ℕ) (p q : unitInterval) :
    IsProbabilityMeasure (productBinomial n m p q) := by
  unfold productBinomial
  infer_instance

theorem productBinomial_real_singleton (n m : ℕ) (p q : unitInterval) (counts : ℕ × ℕ) :
    (productBinomial n m p q).real {counts} =
      binomialMass n (p : ℝ) counts.1 * binomialMass m (q : ℝ) counts.2 := by
  rcases counts with ⟨first, second⟩
  rw [show ({(first, second)} : Set (ℕ × ℕ)) = {first} ×ˢ {second} from
    Set.singleton_prod_singleton.symm]
  simp only [productBinomial, measureReal_prod_prod, ← binomialMass_eq_mathlib]

theorem productBinomial_real_support (n m : ℕ) (p q : unitInterval) :
    (productBinomial n m p q).real (binomialCountSupport n m) = 1 := by
  rw [← sum_measureReal_singleton]
  simp only [productBinomial_real_singleton, binomialCountSupport, Finset.sum_product]
  simp_rw [← Finset.mul_sum, binomialMass_sum_one, mul_one]
  exact binomialMass_sum_one n (p : ℝ)

/-- Any event's probability is the finite sum of its feasible point masses. -/
theorem productBinomial_real_eq_sum (n m : ℕ) (p q : unitInterval) (event : Set (ℕ × ℕ))
    [DecidablePred (· ∈ event)] :
    (productBinomial n m p q).real event =
      ∑ counts ∈ binomialCountSupport n m,
        if counts ∈ event then binomialMass n (p : ℝ) counts.1 * binomialMass m (q : ℝ) counts.2
        else 0 := by
  set μ := productBinomial n m p q
  set support : Set (ℕ × ℕ) := ↑(binomialCountSupport n m)
  have outside : μ.real supportᶜ = 0 := by
    rw [measureReal_compl (Finset.measurableSet _), probReal_univ,
      productBinomial_real_support, sub_self]
  have rest : μ.real (event \ support) = 0 :=
    measureReal_mono_null (fun _ member => member.2) outside
  have split := measureReal_inter_add_sdiff (μ := μ) (s := event)
    (Finset.measurableSet (binomialCountSupport n m))
  rw [rest, add_zero] at split
  rw [← split]
  have finite : event ∩ support =
      ↑((binomialCountSupport n m).filter (· ∈ event)) := by
    ext counts
    simp [support, and_comm]
  rw [finite, ← sum_measureReal_singleton, Finset.sum_filter]
  simp only [μ, productBinomial_real_singleton]

/-- A rational point of the unit interval, from natural numbers. -/
noncomputable def ratPoint (a d : ℕ) (le : a ≤ d) (positive : 0 < d) : unitInterval :=
  ⟨(a : ℝ) / d, div_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg d),
    (div_le_one (by exact_mod_cast positive)).mpr (by exact_mod_cast le)⟩

/-- Integer numerator of a binomial point mass at success probability a/d. -/
def binomialWeight (n a d k : ℕ) : ℕ :=
  Nat.fast_choose n k * a ^ k * (d - a) ^ (n - k)

theorem binomialMass_ratPoint (n a d k : ℕ) (le : a ≤ d) (positive : 0 < d) (bound : k ≤ n) :
    binomialMass n (ratPoint a d le positive : ℝ) k =
      (binomialWeight n a d k : ℝ) / (d : ℝ) ^ n := by
  have d_ne : (d : ℝ) ≠ 0 := by exact_mod_cast positive.ne'
  have complement : 1 - (a : ℝ) / d = ((d - a : ℕ) : ℝ) / d := by
    rw [Nat.cast_sub le]
    field_simp
  have split : (d : ℝ) ^ n = (d : ℝ) ^ k * (d : ℝ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' bound]
  simp only [binomialMass, ratPoint, binomialWeight, complement, div_pow, Nat.cast_mul,
    Nat.cast_pow, ← Nat.choose_eq_fast_choose, split]
  field_simp

/-- Integer numerator of an event's probability at rational success probabilities. -/
def rejectionNumerator (n m a d b e : ℕ) (reject : ℕ → ℕ → Bool) : ℕ :=
  ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (m + 1),
    if reject x y then binomialWeight n a d x * binomialWeight m b e y else 0

/-- The probability of an event that a Boolean rule decides on feasible counts
is an explicit ratio of natural numbers. -/
theorem productBinomial_real_ratPoint (n m a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d)
    (le₂ : b ≤ e) (positive₂ : 0 < e) (event : Set (ℕ × ℕ)) (reject : ℕ → ℕ → Bool)
    (decides : ∀ x ≤ n, ∀ y ≤ m, ((x, y) ∈ event ↔ reject x y = true)) :
    (productBinomial n m (ratPoint a d le₁ positive₁) (ratPoint b e le₂ positive₂)).real event =
      (rejectionNumerator n m a d b e reject : ℝ) / ((d : ℝ) ^ n * (e : ℝ) ^ m) := by
  classical
  rw [productBinomial_real_eq_sum, binomialCountSupport, Finset.sum_product]
  simp only [rejectionNumerator, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x x_mem
  apply Finset.sum_congr rfl
  intro y y_mem
  have x_le : x ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp x_mem)
  have y_le : y ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp y_mem)
  rw [binomialMass_ratPoint n a d x le₁ positive₁ x_le,
    binomialMass_ratPoint m b e y le₂ positive₂ y_le]
  by_cases rejected : reject x y = true
  · have member := (decides x x_le y y_le).mpr rejected
    simp only [member, rejected, ite_true, Nat.cast_mul, div_mul_div_comm]
  · have outside : (x, y) ∉ event := fun member => rejected ((decides x x_le y y_le).mp member)
    simp [outside, rejected]

/-- Denominator matching `rejectionNumerator`. -/
def rejectionDenominator (n m d e : ℕ) : ℕ := d ^ n * e ^ m

theorem rejectionDenominator_cast (n m d e : ℕ) :
    ((rejectionDenominator n m d e : ℕ) : ℝ) = (d : ℝ) ^ n * (e : ℝ) ^ m := by
  simp [rejectionDenominator]

theorem rejectionDenominator_pos (n m d e : ℕ) (positive₁ : 0 < d) (positive₂ : 0 < e) :
    0 < rejectionDenominator n m d e :=
  Nat.mul_pos (Nat.pow_pos positive₁) (Nat.pow_pos positive₂)

/-- An upper bound on a ratio, from one natural-number comparison. -/
theorem ratio_le_of_check (numerator denominator boundNum boundDen : ℕ)
    (denominator_pos : 0 < denominator) (boundDen_pos : 0 < boundDen)
    (check : numerator * boundDen ≤ boundNum * denominator) :
    (numerator : ℝ) / denominator ≤ (boundNum : ℝ) / boundDen := by
  rw [div_le_div_iff₀ (by exact_mod_cast denominator_pos) (by exact_mod_cast boundDen_pos)]
  exact_mod_cast check

/-- A lower bound on a ratio, from one natural-number comparison. -/
theorem le_ratio_of_check (numerator denominator boundNum boundDen : ℕ)
    (denominator_pos : 0 < denominator) (boundDen_pos : 0 < boundDen)
    (check : boundNum * denominator ≤ numerator * boundDen) :
    (boundNum : ℝ) / boundDen ≤ (numerator : ℝ) / denominator := by
  rw [div_le_div_iff₀ (by exact_mod_cast boundDen_pos) (by exact_mod_cast denominator_pos)]
  exact_mod_cast check

/-- A strict upper bound on a ratio, from one natural-number comparison. -/
theorem ratio_lt_of_check (numerator denominator boundNum boundDen : ℕ)
    (denominator_pos : 0 < denominator) (boundDen_pos : 0 < boundDen)
    (check : numerator * boundDen < boundNum * denominator) :
    (numerator : ℝ) / denominator < (boundNum : ℝ) / boundDen := by
  rw [div_lt_div_iff₀ (by exact_mod_cast denominator_pos) (by exact_mod_cast boundDen_pos)]
  exact_mod_cast check

end StatProof
