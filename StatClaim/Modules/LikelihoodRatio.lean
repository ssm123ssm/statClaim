module

public import StatClaim.Modules.BinomialPolynomial
public import Mathlib.Analysis.MeanInequalities

/-!
For two binomial samples, twice the log of the maximized likelihood ratio is
the usual deviance. A declared rational cutoff for the likelihood ratio
specifies a deviance cutoff exactly while permitting integer computation.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.LikelihoodRatio

open MeasureTheory

/-- The binomial likelihood with the binomial coefficient omitted. -/
noncomputable def likelihood (n count : ℕ) (p : ℝ) : ℝ :=
  p ^ count * (1 - p) ^ (n - count)

/-- The binomial likelihood at the observed proportion. -/
noncomputable def fitted (n count : ℕ) : ℝ :=
  likelihood n count ((count : ℝ) / n)

theorem likelihood_le_fitted (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (p : unitInterval) :
    likelihood n k p ≤ fitted n k := by
  by_cases hz : k = 0
  · subst k
    simpa [fitted, likelihood] using
      pow_le_one₀ (sub_nonneg.mpr p.property.2) (by linarith [p.property.1]) (n := n)
  by_cases he : k = n
  · subst k
    have ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simpa [fitted, likelihood, ne] using pow_le_one₀ p.property.1 p.property.2 (n := n)
  let u := (k : ℝ) / n
  let v := 1 - u
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have u_pos : 0 < u := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hz) hnr
  have v_pos : 0 < v := sub_pos.mpr ((div_lt_one hnr).mpr (by
    exact_mod_cast (lt_of_le_of_ne hk he)))
  let a := (p : ℝ) / u
  let b := (1 - (p : ℝ)) / v
  have ha : 0 ≤ a := div_nonneg p.property.1 u_pos.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr p.property.2) v_pos.le
  have mean := Real.geom_mean_le_arith_mean2_weighted u_pos.le v_pos.le ha hb (by
    simp [v])
  have average : u * a + v * b = 1 := by
    dsimp [a, b]
    field_simp
    ring
  rw [average] at mean
  have bound := pow_le_pow_left₀ (by positivity) mean n
  rw [one_pow, mul_pow, ← Real.rpow_mul_natCast ha, ← Real.rpow_mul_natCast hb] at bound
  have ku : u * n = (k : ℝ) := div_mul_cancel₀ _ hnr.ne'
  have kv : v * n = ((n - k : ℕ) : ℝ) := by
    rw [show v = 1 - u from rfl, sub_mul, one_mul, ku, Nat.cast_sub hk]
  rw [ku, kv, Real.rpow_natCast, Real.rpow_natCast] at bound
  dsimp [a, b] at bound
  rw [div_pow (p : ℝ) u k, div_pow (1 - (p : ℝ)) v (n - k), div_mul_div_comm] at bound
  exact (div_le_one (mul_pos (pow_pos u_pos _) (pow_pos v_pos _))).mp bound

def fittedNumerator (n count : ℕ) : ℕ :=
  count ^ count * (n - count) ^ (n - count)

theorem fitted_eq (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    fitted n k = (fittedNumerator n k : ℝ) / (n : ℝ) ^ n := by
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have complement : 1 - (k : ℝ) / n = ((n - k : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub hk, sub_div, div_self npos.ne']
  rw [fitted, likelihood, complement, div_pow, div_pow, div_mul_div_comm, ← pow_add, Nat.add_sub_of_le hk]
  push_cast [fittedNumerator]
  rfl

private theorem fittedNumerator_pos (n k : ℕ) : 0 < fittedNumerator n k := by
  have pos (j : ℕ) : 0 < j ^ j := by cases j <;> simp
  exact Nat.mul_pos (pos k) (pos (n - k))

def rejects (nc nt a b x y : ℕ) : Prop :=
  let n := nc + nt
  a * fittedNumerator n (x + y) * (nc ^ nc * nt ^ nt) <
    b * (fittedNumerator nc x * fittedNumerator nt y) * n ^ n

instance (nc nt a b x y : ℕ) : Decidable (rejects nc nt a b x y) := by
  unfold rejects
  infer_instance

def rejection (sizes : FixedSampleDesign) (a b : ℕ) : Set (ℕ × ℕ) :=
  BinomialPolynomial.region (rejects sizes.nControl sizes.nTreatment a b)

noncomputable def ratio (sizes : FixedSampleDesign) (x y : ℕ) : ℝ :=
  fitted sizes.nControl x * fitted sizes.nTreatment y /
    fitted (sizes.nControl + sizes.nTreatment) (x + y)

theorem pooled_likelihood_le_fitted (sizes : FixedSampleDesign) (x y : ℕ)
    (hx : x ≤ sizes.nControl) (hy : y ≤ sizes.nTreatment) (p : unitInterval) :
    likelihood sizes.nControl x p * likelihood sizes.nTreatment y p ≤
      fitted (sizes.nControl + sizes.nTreatment) (x + y) := by
  have complements : sizes.nControl + sizes.nTreatment - (x + y) =
      (sizes.nControl - x) + (sizes.nTreatment - y) := by omega
  calc
    _ = likelihood (sizes.nControl + sizes.nTreatment) (x + y) p := by
      simp only [likelihood, complements, pow_add]
      ring
    _ ≤ _ := likelihood_le_fitted _ _
      (Nat.add_pos_left sizes.controlPositive _) (Nat.add_le_add hx hy) p

theorem separate_likelihood_le_fitted (sizes : FixedSampleDesign) (x y : ℕ)
    (hx : x ≤ sizes.nControl) (hy : y ≤ sizes.nTreatment) (p q : unitInterval) :
    likelihood sizes.nControl x p * likelihood sizes.nTreatment y q ≤
      fitted sizes.nControl x * fitted sizes.nTreatment y := by
  have q0 := q.property.1
  have q1 := sub_nonneg.mpr q.property.2
  have fit_nonnegative : 0 ≤ fitted sizes.nControl x := by
    rw [fitted_eq _ _ sizes.controlPositive hx]
    positivity
  exact mul_le_mul (likelihood_le_fitted _ _ sizes.controlPositive hx p)
    (likelihood_le_fitted _ _ sizes.treatmentPositive hy q)
    (by unfold likelihood; positivity) fit_nonnegative

theorem rejection_iff_ratio (sizes : FixedSampleDesign) (a b x y : ℕ)
    (hb : 0 < b) (hx : x ≤ sizes.nControl) (hy : y ≤ sizes.nTreatment) :
    (x, y) ∈ rejection sizes a b ↔ (a : ℝ) / b < ratio sizes x y := by
  let nc := sizes.nControl
  let nt := sizes.nTreatment
  have pc : (0 : ℝ) < sizes.nControl := by exact_mod_cast sizes.controlPositive
  have pt : (0 : ℝ) < sizes.nTreatment := by exact_mod_cast sizes.treatmentPositive
  have pb : (0 : ℝ) < b := by exact_mod_cast hb
  have npos : 0 < nc + nt := Nat.add_pos_left sizes.controlPositive nt
  have pn : (0 : ℝ) < fittedNumerator (nc + nt) (x + y) := by
    exact_mod_cast fittedNumerator_pos (nc + nt) (x + y)
  unfold ratio
  rw [fitted_eq _ _ sizes.controlPositive hx, fitted_eq _ _ sizes.treatmentPositive hy,
    fitted_eq _ _ npos (Nat.add_le_add hx hy)]
  change rejects nc nt a b x y ↔ _
  unfold rejects
  rw [div_mul_div_comm, div_div_eq_mul_div, div_mul_eq_mul_div, div_div,
    div_lt_div_iff₀ pb (by positivity)]
  norm_cast
  simp only [nc, nt, mul_comm, mul_left_comm, mul_assoc]

/-- At a positive declared likelihood-ratio cutoff the rule is also a strict
comparison of twice the log likelihood ratio. -/
theorem rejection_iff_deviance (sizes : FixedSampleDesign) (a b x y : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hx : x ≤ sizes.nControl) (hy : y ≤ sizes.nTreatment) :
    (x, y) ∈ rejection sizes a b ↔
      2 * Real.log ((a : ℝ) / b) < 2 * Real.log (ratio sizes x y) := by
  rw [rejection_iff_ratio sizes a b x y hb hx hy]
  have positive : ∀ n k : ℕ, 0 < n → k ≤ n → 0 < fitted n k := by
    intro n k hn hk
    rw [fitted_eq n k hn hk]
    exact div_pos (by exact_mod_cast fittedNumerator_pos n k)
      (pow_pos (by exact_mod_cast hn) _)
  have ratio_pos : 0 < ratio sizes x y := by
    unfold ratio
    exact div_pos (mul_pos (positive _ _ sizes.controlPositive hx)
      (positive _ _ sizes.treatmentPositive hy))
      (positive _ _ (Nat.add_pos_left sizes.controlPositive _) (Nat.add_le_add hx hy))
  rw [mul_lt_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2),
    Real.log_lt_log_iff (by positivity) ratio_pos]

def weight (nc nt a b total : ℕ) : ℕ :=
  BinomialPolynomial.weight nc nt (rejects nc nt a b) total

theorem probability (sizes : FixedSampleDesign) (a b : ℕ) (p : unitInterval) :
    (productBinomial sizes.nControl sizes.nTreatment p p).real (rejection sizes a b) =
      PolynomialBound.value (sizes.nControl + sizes.nTreatment) 1
        (weight sizes.nControl sizes.nTreatment a b) p :=
  BinomialPolynomial.probability sizes (rejects sizes.nControl sizes.nTreatment a b) p

end StatClaim.Modules.LikelihoodRatio
