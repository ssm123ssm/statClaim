module

public import StatClaim.Modules.BinomialPower
public import StatClaim.Modules.PolynomialBound

/-! Finite-sample certificates for the two-sided, uncorrected McNemar chi-square rule. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.McNemarAsymptotic

open MeasureTheory ProbabilityTheory

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
  PolynomialBound.weights n (weight n a b)

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
  PolynomialBound.numerator (weights n a b) high complement

def denominator (n grid : ℕ) : ℕ :=
  PolynomialBound.denominator n (2 ^ n) grid

def check (n a b boundNum boundDen : ℕ) (cells : List ℕ) : Bool :=
  PolynomialBound.check n (2 ^ n) (weights n a b) boundNum boundDen cells

/-- The checked partition covers every possible discordance rate. -/
theorem typeI_of_check (n a b boundNum boundDen : ℕ) (cells : List ℕ)
    (hden : 0 < boundDen) (certificate : check n a b boundNum boundDen cells = true)
    (q : unitInterval) :
    (Matched.pairsLaw n q Matched.half).real (rejection n a b) ≤ (boundNum : ℝ) / boundDen := by
  rw [probability]
  simpa only [PolynomialBound.value, Nat.cast_pow, Nat.cast_ofNat] using
    PolynomialBound.le_of_check n (2 ^ n) (weight n a b) boundNum boundDen cells
      (by positivity) hden certificate q

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
  have eq : (Matched.pairsLaw n q Matched.half).real (rejection n a b) =
      (numerator n a b pointNum (pointDen - pointNum) : ℝ) / (denominator n pointDen : ℕ) := by
    rw [probability]
    simpa only [PolynomialBound.value, Nat.cast_pow, Nat.cast_ofNat, q, numerator, weights,
      denominator] using PolynomialBound.at_point n (2 ^ n) (weight n a b) pointNum pointDen hpoint hpos
  refine ⟨q, ?_⟩
  rw [eq, div_lt_div_iff₀ (by exact_mod_cast hden)
    (by exact_mod_cast (show 0 < denominator n pointDen by
      unfold denominator PolynomialBound.denominator
      positivity))]
  exact_mod_cast cross

end StatClaim.Modules.McNemarAsymptotic
