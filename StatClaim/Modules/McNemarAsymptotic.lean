module

public import StatClaim.Modules.BinomialPower
public import StatClaim.Modules.Wald

/-! Finite-sample certificates for the two-sided, uncorrected McNemar chi-square rule. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.McNemarAsymptotic

open MeasureTheory ProbabilityTheory
open DifferenceTest (cellsOk lastOf cell_exists)

def rejects (a b d k : ℕ) : Prop :=
  0 < d ∧ a * d < b * (max (2 * k) d - min (2 * k) d) ^ 2

instance (a b d k : ℕ) : Decidable (rejects a b d k) := by
  unfold rejects
  infer_instance

def rejection (n a b : ℕ) : Set (ℕ × ℕ) :=
  Association.given n (fun d => {k | rejects a b d k})

def conditionalWeight (a b d : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d + 1), if rejects a b d k then d.fast_choose k else 0

def weight (n a b d : ℕ) : ℕ :=
  n.fast_choose d * conditionalWeight a b d * 2 ^ (n - d)

def weights (n a b : ℕ) : List ℕ :=
  (List.range (n + 1)).map (weight n a b)

private theorem conditional_probability (a b d : ℕ) :
    (binomial d Matched.half).real {k | rejects a b d k} =
      (conditionalWeight a b d : ℝ) / 2 ^ d := by
  classical
  rw [binomial_real_eq_expectation]
  simp only [binomialExpectation, conditionalWeight, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := by simpa using hk
  rw [show Matched.half = ratPoint 1 2 (by decide) (by decide) from rfl,
    binomialMass_ratPoint d 1 2 k (by decide) (by decide) hkd]
  by_cases h : rejects a b d k <;>
    norm_num [Set.mem_ofPred_eq, h, binomialWeight]

theorem probability (n a b : ℕ) (q : unitInterval) :
    (Matched.pairsLaw n q Matched.half).real (rejection n a b) =
      ∑ d ∈ Finset.range (n + 1), (weight n a b d : ℝ) *
        (q : ℝ) ^ d * (1 - (q : ℝ)) ^ (n - d) / 2 ^ n := by
  unfold Matched.pairsLaw rejection
  rw [BinomialPower.mixture_real_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ≤ n := by simpa using hd
  rw [conditional_probability]
  have split : (2 : ℝ) ^ n = 2 ^ d * 2 ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_cancel' hdn]
  simp only [binomialMass, weight, Nat.choose_eq_fast_choose, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [split]
  field_simp

def numerator (n a b high complement : ℕ) : ℕ :=
  (Wald.evaluate high complement (weights n a b)).1

private theorem numerator_eq (n a b high complement : ℕ) :
    numerator n a b high complement =
      ∑ d ∈ Finset.range (n + 1), weight n a b d * high ^ d * complement ^ (n - d) := by
  simp only [numerator, Wald.evaluate_eq, weights, List.length_map, List.length_range,
    Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro d hd
  simp [Finset.mem_range.mp hd]

def denominator (n grid : ℕ) : ℕ := 2 ^ n * grid ^ n

private theorem fraction_eq (n a b y z g : ℕ) :
    (numerator n a b y z : ℝ) / (denominator n g : ℕ) =
      ∑ d ∈ Finset.range (n + 1), (weight n a b d : ℝ) *
        ((y : ℝ) / g) ^ d * ((z : ℝ) / g) ^ (n - d) / 2 ^ n := by
  rw [numerator_eq, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ≤ n := by simpa using hd
  push_cast [denominator]
  have split : (g : ℝ) ^ n = (g : ℝ) ^ d * (g : ℝ) ^ (n - d) := by
    rw [← pow_add, Nat.add_sub_of_le hdn]
  rw [div_pow, div_pow, split]
  simp only [div_eq_mul_inv, mul_inv]
  ring

def check (n a b boundNum boundDen : ℕ) (cells : List ℕ) : Bool :=
  decide (cells ≠ [] ∧ lastOf 0 cells = Wald.grid) &&
  cellsOk (fun lo hi => decide (lo ≤ hi ∧ hi ≤ Wald.grid ∧
    numerator n a b hi (Wald.grid - lo) * boundDen ≤ boundNum * denominator n Wald.grid))
    0 cells

/-- The checked partition covers every possible discordance rate. -/
theorem typeI_of_check (n a b boundNum boundDen : ℕ) (cells : List ℕ)
    (hden : 0 < boundDen) (certificate : check n a b boundNum boundDen cells = true)
    (q : unitInterval) :
    (Matched.pairsLaw n q Matched.half).real (rejection n a b) ≤ (boundNum : ℝ) / boundDen := by
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
    _ ≤ (numerator n a b hi (Wald.grid - lo) : ℝ) / (denominator n Wald.grid : ℕ) := by
      rw [probability, fraction_eq]
      apply Finset.sum_le_sum
      intro d _
      have hq := q.property.1
      have hq1 := sub_nonneg.mpr q.property.2
      gcongr
    _ ≤ _ := ratio_le_of_check _ _ _ _ (by simp [denominator, Wald.grid]) hden cross

def checkCounterexample (n a b boundNum boundDen pointNum pointDen : ℕ) : Bool :=
  decide (pointNum ≤ pointDen ∧ 0 < pointDen ∧
    boundNum * denominator n pointDen < numerator n a b pointNum (pointDen - pointNum) * boundDen)

theorem counterexample (n a b boundNum boundDen pointNum pointDen : ℕ)
    (hden : 0 < boundDen)
    (checked : checkCounterexample n a b boundNum boundDen pointNum pointDen = true) :
    ∃ q : unitInterval,
      (boundNum : ℝ) / boundDen < (Matched.pairsLaw n q Matched.half).real (rejection n a b) := by
  obtain ⟨hpoint, hpos, cross⟩ := of_decide_eq_true checked
  let q := ratPoint pointNum pointDen hpoint hpos
  have complement : (((pointDen - pointNum : ℕ) : ℝ) / pointDen) = 1 - (q : ℝ) := by
    have pos : (pointDen : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Nat.cast_sub hpoint, sub_div, div_self pos]
    rfl
  refine ⟨q, ?_⟩
  rw [probability, ← complement]
  simp only [q, ratPoint]
  rw [← fraction_eq]
  rw [div_lt_div_iff₀ (by exact_mod_cast hden)
    (by exact_mod_cast (show 0 < denominator n pointDen by unfold denominator; positivity))]
  exact_mod_cast cross

end StatClaim.Modules.McNemarAsymptotic
