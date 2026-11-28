module

public import StatClaim.Modules.BinomialPolynomial

/-! The two-sided unpooled Wald rule for arbitrary fixed binomial arm sizes. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.UnpooledWald

open MeasureTheory

def rejects (nc nt a b x y : ℕ) : Prop :=
  let u := y * nc
  let v := x * nt
  a * (x * (nc - x) * nt ^ 3 + y * (nt - y) * nc ^ 3) <
    b * (max u v - min u v) ^ 2 * nc * nt

instance (nc nt a b x y : ℕ) : Decidable (rejects nc nt a b x y) := by
  unfold rejects
  infer_instance

def rejection (sizes : FixedSampleDesign) (a b : ℕ) : Set TwoArmBinomial.Counts :=
  BinomialPolynomial.region (rejects sizes.nControl sizes.nTreatment a b)

private theorem cast_gap_square (a b : ℕ) :
    (((max a b - min a b : ℕ) : ℝ)) ^ 2 = ((a : ℝ) - b) ^ 2 := by
  rcases le_total a b with le | ge
  · rw [max_eq_right le, min_eq_left le, Nat.cast_sub le]
    ring
  · rw [max_eq_left ge, min_eq_right ge, Nat.cast_sub ge]

/-- The integer rule compares the squared risk difference with the estimated
unpooled variance times the cutoff, including at zero estimated variance. -/
theorem rejection_iff_real (sizes : FixedSampleDesign) (a b x y : ℕ) (hb : 0 < b)
    (hx : x ≤ sizes.nControl) (hy : y ≤ sizes.nTreatment) :
    (x, y) ∈ rejection sizes a b ↔
      ((a : ℝ) / b) *
        (((x : ℝ) / sizes.nControl) * (1 - (x : ℝ) / sizes.nControl) / sizes.nControl +
          ((y : ℝ) / sizes.nTreatment) * (1 - (y : ℝ) / sizes.nTreatment) / sizes.nTreatment) <
      ((y : ℝ) / sizes.nTreatment - (x : ℝ) / sizes.nControl) ^ 2 := by
  have hnc : (0 : ℝ) < sizes.nControl := by exact_mod_cast sizes.controlPositive
  have hnt : (0 : ℝ) < sizes.nTreatment := by exact_mod_cast sizes.treatmentPositive
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have intCheck := Nat.cast_lt (α := ℝ)
    (m := a * (x * (sizes.nControl - x) * sizes.nTreatment ^ 3 +
      y * (sizes.nTreatment - y) * sizes.nControl ^ 3))
    (n := b * (max (y * sizes.nControl) (x * sizes.nTreatment) -
      min (y * sizes.nControl) (x * sizes.nTreatment)) ^ 2 * sizes.nControl * sizes.nTreatment)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, cast_gap_square, Nat.cast_sub hx,
    Nat.cast_sub hy] at intCheck
  change rejects sizes.nControl sizes.nTreatment a b x y ↔ _
  unfold rejects
  rw [← intCheck]
  conv_rhs => rw [← mul_lt_mul_iff_right₀
    (show (0 : ℝ) < b * (sizes.nControl : ℝ) ^ 3 * (sizes.nTreatment : ℝ) ^ 3 by positivity)]
  generalize (sizes.nControl : ℝ) = nc at *
  generalize (sizes.nTreatment : ℝ) = nt at *
  rw [show (b : ℝ) * nc ^ 3 * nt ^ 3 *
      ((a : ℝ) / b * ((x / nc) * (1 - x / nc) / nc + (y / nt) * (1 - y / nt) / nt)) =
      (a : ℝ) * (x * (nc - x) * nt ^ 3 + y * (nt - y) * nc ^ 3) by field_simp]
  rw [show (b : ℝ) * nc ^ 3 * nt ^ 3 * ((y : ℝ) / nt - (x : ℝ) / nc) ^ 2 =
      (b : ℝ) * ((y : ℝ) * nc - (x : ℝ) * nt) ^ 2 * nc * nt by field_simp]

end StatClaim.Modules.UnpooledWald
