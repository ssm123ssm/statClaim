module

public import StatClaim.Modules.Wald

/-! Uniform and pointwise checks for nonnegative homogeneous probability polynomials. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.PolynomialBound

open DifferenceTest (cellsOk lastOf cell_exists)

def weights (n : ℕ) (coefficient : ℕ → ℕ) : List ℕ :=
  (List.range (n + 1)).map coefficient

def numerator (coefficients : List ℕ) (high complement : ℕ) : ℕ :=
  (Wald.evaluate high complement coefficients).1

def denominator (n scale grid : ℕ) : ℕ := scale * grid ^ n

noncomputable def value (n scale : ℕ) (coefficient : ℕ → ℕ) (p : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (n + 1),
    (coefficient d : ℝ) * p ^ d * (1 - p) ^ (n - d) / scale

private theorem numerator_eq (n : ℕ) (coefficient : ℕ → ℕ) (high complement : ℕ) :
    numerator (weights n coefficient) high complement =
      ∑ d ∈ Finset.range (n + 1), coefficient d * high ^ d * complement ^ (n - d) := by
  simp only [numerator, Wald.evaluate_eq, weights, List.length_map, List.length_range,
    Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro d hd
  simp [Finset.mem_range.mp hd]

private theorem fraction_eq (n scale : ℕ) (coefficient : ℕ → ℕ) (y z g : ℕ) :
    (numerator (weights n coefficient) y z : ℝ) / (denominator n scale g : ℕ) =
      ∑ d ∈ Finset.range (n + 1),
        (coefficient d : ℝ) * ((y : ℝ) / g) ^ d * ((z : ℝ) / g) ^ (n - d) / scale := by
  rw [numerator_eq, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ≤ n := by simpa using hd
  have split : (g : ℝ) ^ n = (g : ℝ) ^ d * (g : ℝ) ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_of_le hdn]
  push_cast [denominator]
  rw [div_pow, div_pow, split]
  simp only [div_eq_mul_inv, mul_inv]
  ring

def check (n scale : ℕ) (coefficients : List ℕ) (boundNum boundDen : ℕ) (cells : List ℕ) : Bool :=
  decide (cells ≠ [] ∧ lastOf 0 cells = Wald.grid) &&
  cellsOk (fun lo hi => decide (lo ≤ hi ∧ hi ≤ Wald.grid ∧
    numerator coefficients hi (Wald.grid - lo) * boundDen ≤
      boundNum * denominator n scale Wald.grid)) 0 cells

/-- Each factor is bounded on its checked cell. The cells cover the full unit interval. -/
theorem le_of_check (n scale : ℕ) (coefficient : ℕ → ℕ) (boundNum boundDen : ℕ) (cells : List ℕ)
    (hs : 0 < scale) (hden : 0 < boundDen)
    (certificate : check n scale (weights n coefficient) boundNum boundDen cells = true)
    (q : unitInterval) : value n scale coefficient q ≤ (boundNum : ℝ) / boundDen := by
  obtain ⟨shape, checked⟩ := Bool.and_eq_true_iff.mp certificate
  obtain ⟨nonempty, complete⟩ := of_decide_eq_true shape
  have grid_pos : (0 : ℝ) < Wald.grid := by norm_num [Wald.grid]
  obtain ⟨lo, hi, ok, left, right⟩ :=
    cell_exists _ ((q : ℝ) * Wald.grid) cells 0 nonempty checked
      (by simpa using mul_nonneg q.property.1 grid_pos.le)
      (by rw [complete]; exact mul_le_of_le_one_left grid_pos.le q.property.2)
  obtain ⟨ordered, inside, cross⟩ := of_decide_eq_true ok
  have hlo := ordered.trans inside
  have high := (le_div_iff₀ grid_pos).mpr right
  have low := (div_le_iff₀ grid_pos).mpr left
  have complement : 1 - (q : ℝ) ≤ ((Wald.grid - lo : ℕ) : ℝ) / Wald.grid := by
    rw [Nat.cast_sub hlo, sub_div, div_self grid_pos.ne']
    linarith
  calc
    _ ≤ (numerator (weights n coefficient) hi (Wald.grid - lo) : ℝ) /
          (denominator n scale Wald.grid : ℕ) := by
      rw [value, fraction_eq]
      apply Finset.sum_le_sum
      intro d _
      have hq := q.property.1
      have hq1 := sub_nonneg.mpr q.property.2
      gcongr
    _ ≤ _ := ratio_le_of_check _ _ _ _ (by unfold denominator; simp [Wald.grid, hs]) hden cross

theorem at_point (n scale : ℕ) (coefficient : ℕ → ℕ)
    (a d : ℕ) (ha : a ≤ d) (hd : 0 < d) :
    value n scale coefficient (ratPoint a d ha hd) =
      (numerator (weights n coefficient) a (d - a) : ℝ) / (denominator n scale d : ℕ) := by
  have complement : (((d - a : ℕ) : ℝ) / d) = 1 - (a : ℝ) / d := by
    rw [Nat.cast_sub ha, sub_div, div_self (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  rw [value, fraction_eq, complement]
  rfl

def pointProbability (n scale : ℕ) (coefficients : List ℕ) (rate : ℚ) : ℚ :=
  (numerator coefficients rate.num.toNat (rate.den - rate.num.toNat) : ℚ) /
    denominator n scale rate.den

theorem pointProbability_eq (n scale : ℕ) (coefficient : ℕ → ℕ) (rate : ℚ)
    (h0 : 0 ≤ rate) (h1 : rate ≤ 1) :
    ∃ p : unitInterval, (p : ℝ) = (rate : ℝ) ∧
      value n scale coefficient p = (pointProbability n scale (weights n coefficient) rate : ℝ) := by
  have rate_eq : (rate.num.toNat : ℚ) / rate.den = rate := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr h0), Rat.num_div_den]
  have bound : rate.num.toNat ≤ rate.den := by
    have h : (rate.num.toNat : ℚ) / rate.den ≤ 1 := rate_eq.trans_le h1
    rw [div_le_one (by exact_mod_cast rate.den_pos : (0 : ℚ) < rate.den)] at h
    exact_mod_cast h
  refine ⟨ratPoint rate.num.toNat rate.den bound rate.den_pos, ?_, ?_⟩
  · simpa only [ratPoint, Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) rate_eq
  · rw [at_point]
    simp [pointProbability]


end StatClaim.Modules.PolynomialBound
