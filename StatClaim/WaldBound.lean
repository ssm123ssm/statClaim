module

public import StatClaim.BinomialModel
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Linarith

/-!
Finite-sample size of the two-sided unpooled Wald test with equally sized
independent binomial arms. Condition on the pooled successes, bound each
hypergeometric tail by a geometric series, and mix using the binomial law.
-/

@[expose] public section

namespace StatClaim

/-- `a / b` is the squared critical value. At zero estimated variance, the
strict cross-multiplied rule rejects exactly when the estimates differ. -/
def balancedWaldReject (n a b total k : ℕ) : Prop :=
  a * total * (2 * n - total) <
    (b * (2 * n) + a) * ((2 * k - total) + (total - 2 * k)) ^ 2

instance (n a b total k : ℕ) : Decidable (balancedWaldReject n a b total k) :=
  inferInstanceAs (Decidable (_ < _))

/-- The first success count on the upper side of the rejection region. -/
def balancedWaldUpperCutoff (n a b total : ℕ) : ℕ :=
  (total + Nat.sqrt (a * total * (2 * n - total) / (b * (2 * n) + a))) / 2 + 1

private theorem upperCutoff_above_center (n a b total : ℕ) :
    total < 2 * balancedWaldUpperCutoff n a b total := by
  unfold balancedWaldUpperCutoff
  omega

private theorem wald_reject_upper_iff (n a b total k : ℕ)
    (den_pos : 0 < b * (2 * n) + a) (above_center : total ≤ 2 * k) :
    balancedWaldReject n a b total k ↔ balancedWaldUpperCutoff n a b total ≤ k := by
  unfold balancedWaldReject balancedWaldUpperCutoff
  rw [Nat.sub_eq_zero_of_le above_center, Nat.add_zero]
  rw [mul_comm (b * (2 * n) + a), ← Nat.div_lt_iff_lt_mul den_pos, pow_two, ← Nat.sqrt_lt]
  omega

private theorem wald_reject_reflect (n a b total k : ℕ) (hk : k ≤ total) :
    balancedWaldReject n a b total (total - k) ↔ balancedWaldReject n a b total k := by
  unfold balancedWaldReject
  have : (2 * (total - k) - total) + (total - 2 * (total - k)) =
      (2 * k - total) + (total - 2 * k) := by omega
  rw [this]

/-- Squared unpooled standard error of the difference in arm proportions. -/
noncomputable def balancedWaldSquaredSE (n x y : ℕ) : ℝ :=
  ((x : ℝ) / n) * (1 - (x : ℝ) / n) / n +
  ((y : ℝ) / n) * (1 - (y : ℝ) / n) / n

/-- At positive arm size this polynomial rule is the usual unpooled squared
Wald comparison, written without dividing by the estimated variance. -/
theorem balancedWaldReject_iff (n a b x y : ℕ) (hn : 0 < n) (hb : 0 < b)
    (hx : x ≤ n) (hy : y ≤ n) :
    balancedWaldReject n a b (x + y) x ↔
      ((a : ℝ) / b) * balancedWaldSquaredSE n x y <
      ((x : ℝ) / n - (y : ℝ) / n) ^ 2 := by
  unfold balancedWaldSquaredSE
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have total_le : x + y ≤ 2 * n := by omega
  unfold balancedWaldReject
  have cast_comparison :
      (a * (x + y) * (2 * n - (x + y)) <
        (b * (2 * n) + a) * ((2 * x - (x + y)) + ((x + y) - 2 * x)) ^ 2) ↔
      (a : ℝ) * (x + y) * (2 * n - (x + y)) <
        (b * (2 * n) + a) * ((x : ℝ) - y) ^ 2 := by
    rw [← Nat.cast_lt (α := ℝ)]
    push_cast [Nat.cast_sub total_le]
    have abs_sq : (((2 * x - (x + y)) + ((x + y) - 2 * x) : ℕ) : ℝ) ^ 2 =
        ((x : ℝ) - y) ^ 2 := by
      rcases le_total x y with h | h
      · have eq : (2 * x - (x + y)) + ((x + y) - 2 * x) = y - x := by omega
        rw [eq, Nat.cast_sub h]
        ring
      · have eq : (2 * x - (x + y)) + ((x + y) - 2 * x) = x - y := by omega
        rw [eq, Nat.cast_sub h]
    rw [Nat.cast_add] at abs_sq
    rw [abs_sq]
  rw [cast_comparison]
  have factor_pos : (0 : ℝ) < 2 * b * n ^ 3 := by positivity
  rw [← mul_lt_mul_iff_of_pos_left (c := (((x : ℝ) / n - (y : ℝ) / n) ^ 2)) factor_pos]
  have lhs :
      2 * (b : ℝ) * n ^ 3 *
        ((a / b) * (((x : ℝ) / n) * (1 - (x : ℝ) / n) / n +
         ((y : ℝ) / n) * (1 - (y : ℝ) / n) / n)) =
      (a : ℝ) * (x + y) * (2 * n - (x + y)) - (a : ℝ) * ((x : ℝ) - y) ^ 2 := by
    field_simp
    ring
  have rhs : 2 * (b : ℝ) * n ^ 3 * ((x : ℝ) / n - (y : ℝ) / n) ^ 2 =
      (b : ℝ) * (2 * n) * ((x : ℝ) - y) ^ 2 := by
    field_simp
  rw [lhs, rhs, sub_lt_iff_lt_add, ← add_mul]

/-- Ratio of consecutive upper hypergeometric weights in the feasible tail. -/
def waldTailRatio (n total k : ℕ) : ℚ :=
  ((n - k) * (total - k) : ℕ) / (((k + 1) * (n - (total - k) + 1) : ℕ) : ℚ)

private theorem waldTailRatio_nonneg (n total k : ℕ) : 0 ≤ waldTailRatio n total k := by
  unfold waldTailRatio
  positivity

private theorem waldTailRatio_lt_one (n total k : ℕ) (center : total - k ≤ k) :
    waldTailRatio n total k < 1 := by
  unfold waldTailRatio
  rw [div_lt_iff₀ (by positivity), one_mul]
  exact_mod_cast calc
    (n - k) * (total - k) ≤ (n - (total - k) + 1) * k :=
      Nat.mul_le_mul (Nat.le_succ_of_le (Nat.sub_le_sub_left center n)) center
    _ < (k + 1) * (n - (total - k) + 1) := by
      rw [Nat.mul_comm (k + 1)]
      exact Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self k) (Nat.succ_pos _)

private theorem waldTailRatio_antitone (n total : ℕ) :
    Antitone (waldTailRatio n total) := by
  intro k j h
  unfold waldTailRatio
  apply div_le_div₀ (by positivity) ?_ (by positivity) ?_
  · exact_mod_cast Nat.mul_le_mul (Nat.sub_le_sub_left h n) (Nat.sub_le_sub_left h total)
  · exact_mod_cast Nat.mul_le_mul (Nat.succ_le_succ h)
      (Nat.succ_le_succ (Nat.sub_le_sub_left (Nat.sub_le_sub_left h total) n))

private theorem waldWeight_succ (n total k : ℕ) (hk : k < total)
    (htk : total - k ≤ n) :
    (hypergeometricWeight n n total (k + 1) : ℚ) =
      waldTailRatio n total k * (hypergeometricWeight n n total k : ℚ) := by
  let j := total - (k + 1)
  have h₁ : total - k = j + 1 := by dsimp [j]; omega
  have h₂ : n - (total - k) + 1 = n - j := by omega
  have hc := Nat.choose_succ_right_eq n k
  have ht := Nat.choose_succ_right_eq n j
  unfold waldTailRatio hypergeometricWeight
  rw [h₂, h₁]
  change ((n.choose (k + 1) * n.choose j : ℕ) : ℚ) =
    ((n - k) * (j + 1) : ℕ) / ((((k + 1) * (n - j)) : ℕ) : ℚ) *
      ((n.choose k * n.choose (j + 1) : ℕ) : ℚ)
  have hj : 0 < n - j := by omega
  have hden : (((k + 1) * (n - j) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos k) hj)
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  exact_mod_cast calc
    n.choose (k + 1) * n.choose j * ((k + 1) * (n - j)) =
        (n.choose (k + 1) * (k + 1)) * (n.choose j * (n - j)) := by ring
    _ = (n - k) * (j + 1) * (n.choose k * n.choose (j + 1)) := by rw [hc, ← ht]; ring

def waldFastWeight (n total k : ℕ) : ℕ :=
  n.fast_choose k * n.fast_choose (total - k)

theorem waldFastWeight_eq (n total k : ℕ) :
    waldFastWeight n total k = hypergeometricWeight n n total k := by
  simp only [waldFastWeight, hypergeometricWeight, ← Nat.choose_eq_fast_choose]

/-- Bound the unnormalized upper hypergeometric tail. Sum at most `terms`
leading weights exactly and bound the rest by a geometric series. -/
def waldTailWeightBound (n total : ℕ) (k : ℕ) : ℕ → ℚ
  | 0 => if k ≤ min n total then
      (waldFastWeight n total k : ℚ) / (1 - waldTailRatio n total k) else 0
  | terms + 1 => if k ≤ min n total then
      (waldFastWeight n total k : ℚ) + waldTailWeightBound n total (k + 1) terms else 0

private theorem sum_range_le_geometric (f : ℕ → ℚ) (r : ℚ) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (len : ℕ) (nonneg : ∀ i, 0 ≤ f i)
    (decay : ∀ i, i + 1 < len → f (i + 1) ≤ r * f i) :
    (∑ i ∈ Finset.range len, f i) ≤ f 0 / (1 - r) := by
  induction len generalizing f with
  | zero => simpa using div_nonneg (nonneg 0) (by linarith : 0 ≤ 1 - r)
  | succ len ih =>
    rw [Finset.sum_range_succ']
    by_cases h : len = 0
    · subst len
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      rw [le_div_iff₀ (by linarith : 0 < 1 - r)]
      nlinarith [mul_nonneg hr₀ (nonneg 0)]
    · have hd : f 1 ≤ r * f 0 := decay 0 (by omega)
      calc
        _ ≤ f 1 / (1 - r) + f 0 := by
          gcongr
          exact ih (fun i => f (i + 1)) (fun i => nonneg (i + 1))
            (fun i hi => decay (i + 1) (by omega))
        _ ≤ f 0 / (1 - r) := by
          have hr : 0 < 1 - r := by linarith
          rw [← mul_le_mul_iff_of_pos_right hr, add_mul,
            div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne']
          linarith

private theorem tail_sum_le_waldTailWeightBound (n total k terms : ℕ)
    (center : total - k ≤ k) (support : total - k ≤ n) :
    (∑ j ∈ Finset.range (min n total + 1 - k),
      (hypergeometricWeight n n total (k + j) : ℚ)) ≤ waldTailWeightBound n total k terms := by
  induction terms generalizing k with
  | zero =>
    by_cases hk : k ≤ min n total
    · rw [waldTailWeightBound, ite_eq_left hk, waldFastWeight_eq]
      apply sum_range_le_geometric _ _ (waldTailRatio_nonneg n total k)
        (waldTailRatio_lt_one n total k center)
      · intro j
        positivity
      · intro j hj
        have h' : k + j < min n total := by omega
        rw [← Nat.add_assoc, waldWeight_succ _ _ _
          (lt_of_lt_of_le h' (min_le_right _ _)) (by omega)]
        exact mul_le_mul_of_nonneg_right
          (waldTailRatio_antitone n total (Nat.le_add_right k j)) (by positivity)
    · have hlen : min n total + 1 - k = 0 := by omega
      simp [waldTailWeightBound, hk, hlen]
  | succ terms ih =>
    by_cases hk : k ≤ min n total
    · have hlen : min n total + 1 - k = (min n total + 1 - (k + 1)) + 1 := by omega
      rw [waldTailWeightBound, ite_eq_left hk, waldFastWeight_eq, hlen,
        Finset.sum_range_succ', add_comm]
      simp only [Nat.add_zero]
      apply add_le_add_right
      simpa only [Nat.add_assoc, Nat.add_comm 1] using
        ih (k + 1) (by omega) (by omega)
    · have hlen : min n total + 1 - k = 0 := by omega
      simp [waldTailWeightBound, hk, hlen]

private theorem waldRejectionWeight_eq (n a b total : ℕ)
    (den_pos : 0 < b * (2 * n) + a) (ht : total ≤ 2 * n) :
    (∑ k ∈ hypergeometricSupport n n total,
      if balancedWaldReject n a b total k then (hypergeometricWeight n n total k : ℚ) else 0) =
      2 * ∑ j ∈ Finset.range (min n total + 1 - balancedWaldUpperCutoff n a b total),
        (hypergeometricWeight n n total (balancedWaldUpperCutoff n a b total + j) : ℚ) := by
  let start := balancedWaldUpperCutoff n a b total
  have center := upperCutoff_above_center n a b total
  change total < 2 * start at center
  let support := hypergeometricSupport n n total
  let weight (k : ℕ) : ℚ := hypergeometricWeight n n total k
  have mem_support (k : ℕ) : k ∈ support ↔ total - n ≤ k ∧ k ≤ min n total :=
    mem_hypergeometricSupport_iff _ _ _ _
  have decomposition : ∀ k ∈ support,
      (if balancedWaldReject n a b total k then weight k else 0) =
      (if start ≤ k then weight k else 0) + (if start ≤ total - k then weight k else 0) := by
    intro k hk
    have hbnds := (mem_support k).mp hk
    have hk_total : k ≤ total := le_trans hbnds.2 (min_le_right _ _)
    by_cases hc : total ≤ 2 * k
    · have hlow : ¬ start ≤ total - k := by omega
      simp [wald_reject_upper_iff n a b total k den_pos hc, hlow, start]
    · have hhigh : ¬ start ≤ k := by omega
      have hr := (wald_reject_reflect n a b total k hk_total).symm.trans
        (wald_reject_upper_iff n a b total (total - k) den_pos (by omega))
      simp [hr, hhigh, start]
  have mirror :
      (∑ k ∈ support.filter (fun k => start ≤ total - k), weight k) =
      ∑ k ∈ support.filter (fun k => start ≤ k), weight k := by
    have swap_mem (k : ℕ) (hk : k ∈ support) : total - k ∈ support := by
      rw [mem_support] at hk ⊢
      omega
    refine Finset.sum_bij (fun k _ => total - k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨swap_mem k hk.1, hk.2⟩
    · intro k hk l hl heq
      have hk' := (mem_support k).mp (Finset.mem_filter.mp hk).1
      have hl' := (mem_support l).mp (Finset.mem_filter.mp hl).1
      omega
    · intro k hk
      rw [Finset.mem_filter] at hk
      have hk' := (mem_support k).mp hk.1
      have eq : total - (total - k) = k := by omega
      exact ⟨total - k, Finset.mem_filter.mpr ⟨swap_mem k hk.1, by rw [eq]; exact hk.2⟩, eq⟩
    · intro k hk
      have hk' := (mem_support k).mp (Finset.mem_filter.mp hk).1
      have eq : total - (total - k) = k := by omega
      simp only [weight, hypergeometricWeight, eq]
      rw [Nat.mul_comm]
  have reindex :
      (∑ j ∈ Finset.range (min n total + 1 - start), weight (start + j)) =
      ∑ k ∈ support.filter (fun k => start ≤ k), weight k := by
    refine Finset.sum_bij (fun j _ => start + j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_range] at hj
      rw [Finset.mem_filter, mem_support]
      omega
    · intro j _ l _ eq
      omega
    · intro k hk
      rw [Finset.mem_filter, mem_support] at hk
      refine ⟨k - start, Finset.mem_range.mpr ?_, by omega⟩
      omega
    · intro j _
      rfl
  change (∑ k ∈ support, if balancedWaldReject n a b total k then weight k else 0) =
    2 * ∑ j ∈ Finset.range (min n total + 1 - start), weight (start + j)
  rw [Finset.sum_congr rfl decomposition, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, mirror, reindex, two_mul]

/-- Exact null rejection probability of the specified balanced Wald rule. -/
noncomputable def balancedWaldNullRejectionProbability (n a b : ℕ) (p : ℝ) : ℝ :=
  ∑ counts ∈ binomialCountSupport n n,
    if balancedWaldReject n a b (counts.1 + counts.2) counts.1
    then independentBinomialMass n n p counts else 0

/-- Group the exact rejection mass by pooled successes and reflect the two tails. -/
theorem balancedWaldNullRejectionProbability_eq_pooledSum (n a b : ℕ) (p : ℝ)
    (den_pos : 0 < b * (2 * n) + a) :
    balancedWaldNullRejectionProbability n a b p =
      ∑ total ∈ Finset.range (2 * n + 1), (2 : ℝ) *
        (∑ j ∈ Finset.range (min n total + 1 - balancedWaldUpperCutoff n a b total),
          (hypergeometricWeight n n total (balancedWaldUpperCutoff n a b total + j) : ℝ)) *
        (p ^ total * (1 - p) ^ (2 * n - total)) := by
  unfold balancedWaldNullRejectionProbability
  rw [sum_binomialCountSupport_by_total, ← two_mul n]
  apply Finset.sum_congr rfl
  intro total ht
  have ht' : total ≤ 2 * n := by simpa using ht
  have eq : (∑ k ∈ hypergeometricSupport n n total,
      if balancedWaldReject n a b total k then (hypergeometricWeight n n total k : ℝ) else 0) =
      (2 : ℝ) *
        ∑ j ∈ Finset.range (min n total + 1 - balancedWaldUpperCutoff n a b total),
          (hypergeometricWeight n n total (balancedWaldUpperCutoff n a b total + j) : ℝ) := by
    exact_mod_cast waldRejectionWeight_eq n a b total den_pos ht'
  rw [← eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have bounds := (mem_hypergeometricSupport_iff n n total k).mp hk
  have pooled : k + (total - k) = total := by omega
  rw [pooled]
  split_ifs with h
  · simp only [independentBinomialMass, binomialMass, hypergeometricWeight, Nat.cast_mul]
    have fails : n - k + (n - (total - k)) = 2 * n - total := by omega
    rw [← fails, ← pooled, pow_add, pow_add]
    rw [pooled]
    ring
  · simp

/-- A rational upper bound for every common null proportion in `[lo, hi]`.
Per pooled count the computation uses a square root and at most `terms + 1`
hypergeometric weights. It does not visit the tables in the residual tail. -/
def balancedWaldIntervalBound (n a b terms : ℕ) (lo hi : ℚ) : ℚ :=
  ∑ total ∈ Finset.range (2 * n + 1),
    2 * waldTailWeightBound n total (balancedWaldUpperCutoff n a b total) terms *
      (hi ^ total * (1 - lo) ^ (2 * n - total))

/-- The interval bound covers all real null rates in the interval, including
both endpoints whenever they lie in the interval. -/
theorem balancedWaldNullRejectionProbability_le_intervalBound
    (n a b terms : ℕ) (p : ℝ) (lo hi : ℚ)
    (den_pos : 0 < b * (2 * n) + a)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hlo : (lo : ℝ) ≤ p) (hhi : p ≤ (hi : ℝ)) :
    balancedWaldNullRejectionProbability n a b p ≤
      (balancedWaldIntervalBound n a b terms lo hi : ℝ) := by
  rw [balancedWaldNullRejectionProbability_eq_pooledSum n a b p den_pos]
  push_cast [balancedWaldIntervalBound]
  apply Finset.sum_le_sum
  intro total ht
  have ht' : total ≤ 2 * n := by simpa using ht
  have ctr := upperCutoff_above_center n a b total
  have hTail := tail_sum_le_waldTailWeightBound n total
    (balancedWaldUpperCutoff n a b total) terms (by omega) (by omega)
  have hTail' : (∑ j ∈ Finset.range (min n total + 1 - balancedWaldUpperCutoff n a b total),
      (hypergeometricWeight n n total (balancedWaldUpperCutoff n a b total + j) : ℝ)) ≤
      (waldTailWeightBound n total (balancedWaldUpperCutoff n a b total) terms : ℝ) := by
    exact_mod_cast hTail
  have hNonneg : (0 : ℝ) ≤ ∑ j ∈ Finset.range
      (min n total + 1 - balancedWaldUpperCutoff n a b total),
      (hypergeometricWeight n n total (balancedWaldUpperCutoff n a b total + j) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hi₀ : (0 : ℝ) ≤ (hi : ℝ) := hp₀.trans hhi
  have hlo₁ : (lo : ℝ) ≤ 1 := hlo.trans hp₁
  have cap_nonneg := hNonneg.trans hTail'
  gcongr

/-- Take the largest of the bounds over `splits + 1` equal closed
subintervals of the full null parameter space `[0, 1]`. -/
def balancedWaldUniformBound (n a b terms splits : ℕ) : ℚ :=
  (Finset.range (splits + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ fun i =>
    balancedWaldIntervalBound n a b terms
      ((i : ℚ) / (splits + 1)) (((i : ℚ) + 1) / (splits + 1))

/-- The bound holds uniformly over all real common null probabilities. -/
theorem balancedWaldNullRejectionProbability_le_uniformBound
    (n a b terms splits : ℕ) (p : ℝ) (den_pos : 0 < b * (2 * n) + a)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    balancedWaldNullRejectionProbability n a b p ≤
      (balancedWaldUniformBound n a b terms splits : ℝ) := by
  let m : ℝ := (splits : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hpm : 0 ≤ p * m := mul_nonneg hp₀ hm.le
  let i := min ⌊p * m⌋₊ splits
  have hi : i ∈ Finset.range (splits + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
  have hlow : (i : ℝ) ≤ p * m :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hpm)
  have hhigh : p * m ≤ (i : ℝ) + 1 := by
    by_cases h : splits ≤ ⌊p * m⌋₊
    · rw [show i = splits from min_eq_right h]
      simpa [m] using mul_le_mul_of_nonneg_right hp₁ hm.le
    · rw [show i = ⌊p * m⌋₊ from min_eq_left (Nat.le_of_not_ge h)]
      exact (Nat.lt_floor_add_one (p * m)).le
  refine (balancedWaldNullRejectionProbability_le_intervalBound n a b terms p
    ((i : ℚ) / (splits + 1)) (((i : ℚ) + 1) / (splits + 1))
    den_pos hp₀ hp₁ ?_ ?_).trans ?_
  · push_cast
    exact (div_le_iff₀ hm).mpr hlow
  · push_cast
    exact (le_div_iff₀ hm).mpr hhigh
  · apply Rat.cast_le.mpr
    unfold balancedWaldUniformBound
    exact Finset.le_sup' (fun j : ℕ => balancedWaldIntervalBound n a b terms
      ((j : ℚ) / (splits + 1)) (((j : ℚ) + 1) / (splits + 1))) hi

/-- Null rejection probability at an arbitrary real squared critical value. -/
noncomputable def balancedWaldNullRejectionProbabilityAt (n : ℕ) (cutoff p : ℝ) : ℝ := by
  classical
  exact ∑ counts ∈ binomialCountSupport n n,
    if cutoff * balancedWaldSquaredSE n counts.1 counts.2 <
        ((counts.1 : ℝ) / n - (counts.2 : ℝ) / n) ^ 2
    then independentBinomialMass n n p counts else 0

theorem balancedWaldNullRejectionProbabilityAt_eq (n a b : ℕ) (p : ℝ)
    (hn : 0 < n) (hb : 0 < b) :
    balancedWaldNullRejectionProbabilityAt n ((a : ℝ) / b) p =
      balancedWaldNullRejectionProbability n a b p := by
  classical
  unfold balancedWaldNullRejectionProbabilityAt balancedWaldNullRejectionProbability
  apply Finset.sum_congr rfl
  intro counts hk
  simp only [binomialCountSupport, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [balancedWaldReject_iff n a b _ _ hn hb hk.1 hk.2]

theorem balancedWaldNullRejectionProbabilityAt_antitone (n : ℕ) (p : ℝ)
    (hn : 0 < n) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    Antitone (fun cutoff => balancedWaldNullRejectionProbabilityAt n cutoff p) := by
  classical
  intro c₁ c₂ hCutoff
  unfold balancedWaldNullRejectionProbabilityAt
  apply Finset.sum_le_sum
  intro counts hm
  simp only [binomialCountSupport, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hX : (counts.1 : ℝ) / n ≤ 1 := (div_le_one hn').mpr (Nat.cast_le.mpr hm.1)
  have hY : (counts.2 : ℝ) / n ≤ 1 := (div_le_one hn').mpr (Nat.cast_le.mpr hm.2)
  have hSE : 0 ≤ balancedWaldSquaredSE n counts.1 counts.2 := by
    unfold balancedWaldSquaredSE
    positivity
  split_ifs with h₂ h₁ h₁
  · exact le_rfl
  · exact (h₁ (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCutoff hSE) h₂)).elim
  · exact independentBinomialMass_nonnegative n n p counts hp₀ hp₁
  · exact le_rfl

/-- A rational squared cutoff at or below the real cutoff certifies an upper
bound for the real-cutoff procedure. -/
theorem balancedWaldNullRejectionProbabilityAt_le_uniformBound
    (n a b terms splits : ℕ) (cutoff p : ℝ) (hn : 0 < n) (hb : 0 < b)
    (hle : (a : ℝ) / b ≤ cutoff) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    balancedWaldNullRejectionProbabilityAt n cutoff p ≤
      (balancedWaldUniformBound n a b terms splits : ℝ) := by
  have h := balancedWaldNullRejectionProbabilityAt_antitone n p hn hp₀ hp₁ hle
  change balancedWaldNullRejectionProbabilityAt n cutoff p ≤
    balancedWaldNullRejectionProbabilityAt n ((a : ℝ) / b) p at h
  rw [balancedWaldNullRejectionProbabilityAt_eq n a b p hn hb] at h
  exact h.trans (balancedWaldNullRejectionProbability_le_uniformBound n a b terms splits p
    (by positivity) hp₀ hp₁)

end StatClaim
