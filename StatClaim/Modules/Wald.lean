module

public import Mathlib.Data.Rat.Floor
public import StatClaim.Modules.DifferenceTest
public import StatClaim.WaldBound

/-!
Computable certificates for the two-sided unpooled Wald test. The hint supplies
rounded-up pooled rejection weights and a partition of the common null rate.
Lean checks the weights against the geometric tail bound, then bounds each
cell by integer arithmetic. The partition must cover the full unit interval.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Wald

open MeasureTheory TwoArmBinomial
open DifferenceTest (cellsOk lastOf cell_exists list_sum_range)

def weightScale : ℕ := 1024
def terms : ℕ := 12
def grid : ℕ := 16384

structure Certificate where
  weights : List ℕ
  cells : List ℕ

def scaledWeight (n a b total : ℕ) : ℕ :=
  ⌈(weightScale : ℚ) * (2 * waldTailWeightBound n total
    (balancedWaldUpperCutoff n a b total) terms)⌉₊

def weights (n a b : ℕ) : List ℕ :=
  (List.range (2 * n + 1)).map (scaledWeight n a b)

/-- Evaluate the homogeneous polynomial and return the complement power for the next step. -/
def evaluate (high complement : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 1)
  | weight :: rest =>
      let (value, power) := evaluate high complement rest
      (weight * power + high * value, complement * power)

private theorem evaluate_eq (high complement : ℕ) (ws : List ℕ) :
    evaluate high complement ws =
      (∑ t ∈ Finset.range ws.length,
        (ws[t]?.getD 0) * high ^ t * complement ^ (ws.length - 1 - t),
        complement ^ ws.length) := by
  induction ws with
  | nil => simp [evaluate]
  | cons weight rest ih =>
    rw [evaluate, ih]
    simp only [List.length_cons, Finset.sum_range_succ', List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.getD_some, pow_zero, mul_one,
      Nat.sub_zero, Nat.sub_succ, pow_succ, Finset.mul_sum, Prod.mk.injEq]
    constructor
    · rw [add_comm (weight * complement ^ rest.length)]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      have hsub : ((rest.length + 1).pred - t).pred = rest.length.pred - t := by
        simp only [Nat.pred_eq_sub_one]
        omega
      rw [hsub]
      ring
    · exact Nat.mul_comm _ _

def cellNumerator (weights : List ℕ) (low high : ℕ) : ℕ :=
  (evaluate high (grid - low) weights).1

private theorem cellNumerator_eq (n a b low high : ℕ) :
    cellNumerator (weights n a b) low high =
      ∑ total ∈ Finset.range (2 * n + 1),
        scaledWeight n a b total * high ^ total * (grid - low) ^ (2 * n - total) := by
  simp only [cellNumerator, evaluate_eq, weights, List.length_map, List.length_range,
    Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro total ht
  simp [Finset.mem_range.mp ht]

def cellDenominator (n : ℕ) : ℕ := weightScale * grid ^ (2 * n)

def cellCheck (n : ℕ) (weights : List ℕ) (boundNum boundDen low high : ℕ) : Bool :=
  decide (low ≤ high ∧ high ≤ grid) &&
    decide (cellNumerator weights low high * boundDen ≤ boundNum * cellDenominator n)

def check (n a b boundNum boundDen : ℕ) (hint : Certificate) : Bool :=
  decide (hint.weights = weights n a b ∧ hint.cells ≠ [] ∧ lastOf 0 hint.cells = grid) &&
    cellsOk (cellCheck n hint.weights boundNum boundDen) 0 hint.cells

private theorem intervalBound_le_cellFraction (n a b low high : ℕ) (hlo : low ≤ grid) :
    balancedWaldIntervalBound n a b terms ((low : ℚ) / grid) ((high : ℚ) / grid) ≤
      (cellNumerator (weights n a b) low high : ℚ) / cellDenominator n := by
  have grid_pos : (0 : ℚ) < grid := by norm_num [grid]
  have scale_pos : (0 : ℚ) < weightScale := by norm_num [weightScale]
  have complement : (1 : ℚ) - (low : ℚ) / grid = ((grid - low : ℕ) : ℚ) / grid := by
    rw [Nat.cast_sub hlo]
    field_simp
  rw [balancedWaldIntervalBound, cellNumerator_eq, complement, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro total ht
  have ht' : total ≤ 2 * n := by simpa using ht
  have weight_le : 2 * waldTailWeightBound n total (balancedWaldUpperCutoff n a b total) terms ≤
      (scaledWeight n a b total : ℚ) / weightScale := by
    apply (le_div_iff₀ scale_pos).mpr
    rw [mul_comm]
    exact Nat.le_ceil _
  calc
    _ ≤ ((scaledWeight n a b total : ℚ) / weightScale) *
        (((high : ℚ) / grid) ^ total * (((grid - low : ℕ) : ℚ) / grid) ^ (2 * n - total)) :=
      mul_le_mul_of_nonneg_right weight_le (by positivity)
    _ = _ := by
      push_cast [cellDenominator]
      rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.add_sub_of_le ht',
        div_mul_div_comm]
      ring

/-- Every success probability lies in one of the checked cells. -/
theorem typeI_of_check (n a b boundNum boundDen : ℕ) (hint : Certificate)
    (hn : 0 < n) (hb : 0 < b) (hden : 0 < boundDen)
    (checked : check n a b boundNum boundDen hint = true)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    balancedWaldNullRejectionProbability n a b p ≤ (boundNum : ℝ) / boundDen := by
  obtain ⟨structural, cells⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨caps, nonempty, complete⟩ := of_decide_eq_true structural
  have grid_pos : (0 : ℝ) < grid := by norm_num [grid]
  obtain ⟨low, high, ok, left, right⟩ := cell_exists _ (p * grid) hint.cells 0 nonempty cells
    (by simpa using mul_nonneg hp₀ grid_pos.le)
    (by rw [complete]; exact mul_le_of_le_one_left grid_pos.le hp₁)
  simp only [cellCheck, Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨ordered, inside⟩, bound⟩ := ok
  have hnum : (cellNumerator (weights n a b) low high : ℚ) * boundDen ≤
      (boundNum : ℚ) * cellDenominator n := by
    rw [caps] at bound
    exact_mod_cast bound
  have cell_le : (cellNumerator (weights n a b) low high : ℚ) / cellDenominator n ≤
      (boundNum : ℚ) / boundDen := by
    rw [div_le_div_iff₀ (by norm_num [cellDenominator, weightScale, grid])
      (by exact_mod_cast hden)]
    exact hnum
  have rational_bound := (intervalBound_le_cellFraction n a b low high (ordered.trans inside)).trans
    cell_le
  have real_bound : (balancedWaldIntervalBound n a b terms
      ((low : ℚ) / grid) ((high : ℚ) / grid) : ℝ) ≤ (boundNum : ℝ) / boundDen := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using (Rat.cast_le (K := ℝ)).mpr rational_bound
  apply le_trans _ real_bound
  apply balancedWaldNullRejectionProbability_le_intervalBound n a b terms p _ _
    (by positivity) hp₀ hp₁
  · push_cast
    exact (div_le_iff₀ grid_pos).mpr left
  · push_cast
    exact (le_div_iff₀ grid_pos).mpr right

def region (n a b : ℕ) : Set Counts :=
  {counts | balancedWaldReject n a b (counts.1 + counts.2) counts.1}

theorem region_iff (n x y : ℕ) (cutoff : ℚ) (hcutoff : 0 ≤ cutoff)
    (hn : 0 < n) (hx : x ≤ n) (hy : y ≤ n) :
    (x, y) ∈ region n cutoff.num.toNat cutoff.den ↔
      (cutoff : ℝ) * balancedWaldSquaredSE n x y < ((x : ℝ) / n - (y : ℝ) / n) ^ 2 := by
  change balancedWaldReject n cutoff.num.toNat cutoff.den (x + y) x ↔ _
  rw [balancedWaldReject_iff _ _ _ x y hn cutoff.den_pos hx hy]
  have cutoff_eq : ((cutoff.num.toNat : ℕ) : ℝ) / cutoff.den = (cutoff : ℝ) := by
    have eq : ((cutoff.num.toNat : ℕ) : ℚ) / cutoff.den = cutoff := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hcutoff)]
      exact Rat.num_div_den cutoff
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) eq
  rw [cutoff_eq]

/-- Connect the finite-sum Wald bound to the shared independent-binomial law. -/
theorem level (sizes : FixedSampleDesign) (balanced : sizes.nTreatment = sizes.nControl)
    (a b boundNum boundDen : ℕ) (hb : 0 < b) (hden : 0 < boundDen)
    (hint : Certificate) (ok : check sizes.nControl a b boundNum boundDen hint = true)
    (θ : Parameters) (null : equalProportions θ) :
    ((model sizes).law θ).real (region sizes.nControl a b) ≤ (boundNum : ℝ) / boundDen := by
  rw [law_under_null sizes θ null]
  change (productBinomial sizes.nControl sizes.nTreatment θ.1 θ.1).real _ ≤ _
  rw [balanced]
  let n := sizes.nControl
  change (productBinomial n n θ.1 θ.1).real (region n a b) ≤ _
  let (counts : Counts) : Decidable (counts ∈ region n a b) :=
    inferInstanceAs (Decidable (balancedWaldReject n a b (counts.1 + counts.2) counts.1))
  rw [productBinomial_real_eq_sum]
  exact typeI_of_check n a b boundNum boundDen hint sizes.controlPositive hb hden ok θ.1
    θ.1.property.1 θ.1.property.2

def exactWeight (n a b total : ℕ) : ℕ :=
  let start := balancedWaldUpperCutoff n a b total
  2 * ((List.range (min n total + 1 - start)).map
    (fun j => waldFastWeight n total (start + j))).sum

/-- The exact rejection probability at a rational common success rate. -/
def pointProbability (n a b : ℕ) (rate : ℚ) : ℚ :=
  let num := rate.num.toNat
  let den := rate.den
  let ws := (List.range (2 * n + 1)).map (exactWeight n a b)
  ((evaluate num (den - num) ws).1 : ℚ) / (den : ℚ) ^ (2 * n)

theorem pointProbability_eq (n a b : ℕ) (rate : ℚ) (hn : 0 < n) (hb : 0 < b)
    (h₀ : 0 ≤ rate) (h₁ : rate ≤ 1) :
    (pointProbability n a b rate : ℝ) =
      balancedWaldNullRejectionProbability n a b (rate : ℝ) := by
  have den_pos : (0 : ℝ) < rate.den := by exact_mod_cast rate.den_pos
  have rate_eq : ((rate.num.toNat : ℕ) : ℝ) / rate.den = (rate : ℝ) := by
    have eq : ((rate.num.toNat : ℕ) : ℚ) / rate.den = rate := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr h₀)]
      exact Rat.num_div_den rate
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) eq
  have num_le : rate.num.toNat ≤ rate.den := by
    have h : ((rate.num.toNat : ℕ) : ℝ) / rate.den ≤ 1 :=
      rate_eq ▸ (by exact_mod_cast h₁)
    rw [div_le_one den_pos] at h
    exact_mod_cast h
  have complement : (((rate.den - rate.num.toNat : ℕ) : ℝ) / rate.den) = 1 - (rate : ℝ) := by
    rw [Nat.cast_sub num_le, sub_div, div_self den_pos.ne', rate_eq]
  rw [balancedWaldNullRejectionProbability_eq_pooledSum _ _ _ _ (by positivity)]
  simp only [pointProbability, evaluate_eq, List.length_map, List.length_range, Nat.add_sub_cancel,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Nat.cast_sum]
  rw [Rat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro total mem
  have ht : total ≤ 2 * n := by simpa using mem
  simp [Finset.mem_range.mp mem]
  have den_pow : (rate.den : ℝ) ^ (2 * n) =
      (rate.den : ℝ) ^ total * (rate.den : ℝ) ^ (2 * n - total) := by
    rw [← pow_add, Nat.add_sub_of_le ht]
  rw [den_pow, mul_assoc, mul_div_assoc, ← div_mul_div_comm, ← div_pow, ← div_pow,
    rate_eq, complement]
  simp only [exactWeight, list_sum_range]
  push_cast
  simp_rw [waldFastWeight_eq]

def checkCounterexample (n a b : ℕ) (alpha rate reported : ℚ) : Bool :=
  decide (0 ≤ rate ∧ rate ≤ 1 ∧ reported = pointProbability n a b rate ∧ alpha < reported)

theorem exact_at_of_check (sizes : FixedSampleDesign) (balanced : sizes.nTreatment = sizes.nControl)
    (a b : ℕ) (hb : 0 < b) (alpha rate reported : ℚ)
    (ok : checkCounterexample sizes.nControl a b alpha rate reported = true) :
    ∃ θ : Parameters, equalProportions θ ∧
      (θ.1 : ℝ) = (rate : ℝ) ∧
      ((model sizes).law θ).real (region sizes.nControl a b) = (reported : ℝ) ∧
      (alpha : ℝ) < (reported : ℝ) := by
  obtain ⟨h₀, h₁, equal, excess⟩ := of_decide_eq_true ok
  let p : unitInterval := ⟨(rate : ℝ), by exact_mod_cast h₀, by exact_mod_cast h₁⟩
  refine ⟨(p, p), rfl, rfl, ?_, by exact_mod_cast excess⟩
  rw [law_under_null sizes (p, p) rfl]
  change (productBinomial sizes.nControl sizes.nTreatment p p).real _ = _
  rw [balanced]
  let n := sizes.nControl
  let (counts : Counts) : Decidable (counts ∈ region n a b) :=
    inferInstanceAs (Decidable (balancedWaldReject n a b (counts.1 + counts.2) counts.1))
  rw [productBinomial_real_eq_sum, equal, pointProbability_eq n a b rate sizes.controlPositive hb h₀ h₁]
  rfl

end StatClaim.Modules.Wald
