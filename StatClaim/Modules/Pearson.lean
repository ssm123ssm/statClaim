module

public import StatClaim.Modules.PolynomialBound

/-! Pearson's two-by-two rule with fixed binomial arm sizes, optionally with Yates's
continuity correction. Pooling by the total number of successes gives an exact
polynomial in the common success probability. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Pearson

open MeasureTheory

def scaledDifference (nc nt x y : ℕ) (corrected : Bool) : ℕ :=
  let u := y * nc
  let v := x * nt
  2 * (max u v - min u v) - (if corrected then nc + nt else 0)

def rejects (nc nt a b : ℕ) (corrected : Bool) (x y : ℕ) : Prop :=
  let total := x + y
  let n := nc + nt
  4 * a * nc * nt * total * (n - total) < b * n * scaledDifference nc nt x y corrected ^ 2

instance (nc nt a b : ℕ) (corrected : Bool) (x y : ℕ) :
    Decidable (rejects nc nt a b corrected x y) := by
  unfold rejects
  infer_instance

def rejection (sizes : FixedSampleDesign) (a b : ℕ) (corrected : Bool) : Set (ℕ × ℕ) :=
  {xy | rejects sizes.nControl sizes.nTreatment a b corrected xy.1 xy.2}

/-- The count difference on the scale of twice the cross-product difference.
At a two-by-two table, Yates subtracts one half from each absolute residual,
with the result floored at zero. Multiplying a residual by twice the total
sample size gives this difference. -/
theorem scaledDifference_cast (nc nt x y : ℕ) (corrected : Bool) :
    (scaledDifference nc nt x y corrected : ℝ) =
      max 0 (2 * |(y : ℝ) * nc - (x : ℝ) * nt| -
        (if corrected then (nc : ℝ) + nt else 0)) := by
  have abs_eq : ((max (y * nc) (x * nt) - min (y * nc) (x * nt) : ℕ) : ℝ) =
      |(y : ℝ) * nc - (x : ℝ) * nt| := by
    rcases le_total (y * nc) (x * nt) with le | ge
    · rw [max_eq_right le, min_eq_left le, Nat.cast_sub le, abs_of_nonpos]
      · push_cast
        ring
      · exact sub_nonpos.mpr (by exact_mod_cast le)
    · rw [max_eq_left ge, min_eq_right ge, Nat.cast_sub ge,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast ge))]
      push_cast
      rfl
  unfold scaledDifference
  dsimp only
  generalize hk : (if corrected then nc + nt else 0) = shift
  have shift_eq : (shift : ℝ) = if corrected then (nc : ℝ) + nt else 0 := by
    rw [← hk]
    cases corrected <;> simp
  rw [← shift_eq, ← abs_eq]
  generalize max (y * nc) (x * nt) - min (y * nc) (x * nt) = d
  rcases le_total (2 * d) shift with below | above
  · rw [Nat.sub_eq_zero_of_le below, Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast below)
  · rw [Nat.cast_sub above, max_eq_right]
    · push_cast
      rfl
    · exact sub_nonneg.mpr (by exact_mod_cast above)

/-- The natural-number rejection comparison uses Pearson's usual chi-square
statistic. The two constant-outcome tables have zero numerator and never reject. -/
theorem rejection_iff_statistic (sizes : FixedSampleDesign) (a b x y : ℕ)
    (corrected : Bool) (hb : 0 < b) (hx : x ≤ sizes.nControl) (hy : y ≤ sizes.nTreatment) :
    (x, y) ∈ rejection sizes a b corrected ↔
      ((a : ℝ) / b) * (sizes.nControl : ℝ) * sizes.nTreatment * (x + y) *
        ((sizes.nControl : ℝ) + sizes.nTreatment - (x + y)) <
      ((sizes.nControl : ℝ) + sizes.nTreatment) *
        (max 0 (|(y : ℝ) * sizes.nControl - (x : ℝ) * sizes.nTreatment| -
          (if corrected then ((sizes.nControl : ℝ) + sizes.nTreatment) / 2 else 0))) ^ 2 := by
  have bounded := Nat.add_le_add hx hy
  have bpos : (0 : ℝ) < b := by exact_mod_cast hb
  have scaled : (scaledDifference sizes.nControl sizes.nTreatment x y corrected : ℝ) =
      2 * max 0 (|(y : ℝ) * sizes.nControl - (x : ℝ) * sizes.nTreatment| -
        (if corrected then ((sizes.nControl : ℝ) + sizes.nTreatment) / 2 else 0)) := by
    rw [scaledDifference_cast, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    cases corrected <;> simp
    ring_nf
  have step := Nat.cast_lt (α := ℝ)
    (m := 4 * a * sizes.nControl * sizes.nTreatment * (x + y) *
      (sizes.nControl + sizes.nTreatment - (x + y)))
    (n := b * (sizes.nControl + sizes.nTreatment) *
      scaledDifference sizes.nControl sizes.nTreatment x y corrected ^ 2)
  push_cast [Nat.cast_sub bounded] at step
  change rejects sizes.nControl sizes.nTreatment a b corrected x y ↔ _
  unfold rejects
  rw [← step, scaled]
  conv_rhs => rw [← mul_lt_mul_iff_right₀ (show (0 : ℝ) < 4 * b by positivity)]
  generalize (sizes.nControl : ℝ) = nc
  generalize (sizes.nTreatment : ℝ) = nt
  generalize (x : ℝ) = x'
  generalize (y : ℝ) = y'
  generalize max 0 (|y' * nc - x' * nt| -
    (if corrected then (nc + nt) / 2 else 0)) = gap
  rw [show 4 * (b : ℝ) * ((a : ℝ) / b * nc * nt * (x' + y') * (nc + nt - (x' + y'))) =
      4 * a * nc * nt * (x' + y') * (nc + nt - (x' + y')) by field_simp]
  rw [show b * (nc + nt) * (2 * gap) ^ 2 = 4 * b * ((nc + nt) * gap ^ 2) by ring]

def tableWeight (nc nt a b : ℕ) (corrected : Bool) (xy : ℕ × ℕ) : ℕ :=
  if rejects nc nt a b corrected xy.1 xy.2 then
    nc.fast_choose xy.1 * nt.fast_choose xy.2
  else 0

def weight (nc nt a b : ℕ) (corrected : Bool) (total : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (nc + 1) with x ≤ total ∧ total - x ≤ nt,
    tableWeight nc nt a b corrected (x, total - x)

private theorem weight_fiber (nc nt a b : ℕ) (corrected : Bool) (total : ℕ) :
    weight nc nt a b corrected total =
      ∑ xy ∈ binomialCountSupport nc nt with xy.1 + xy.2 = total,
        tableWeight nc nt a b corrected xy := by
  unfold weight
  refine Finset.sum_bij (fun x _ => (x, total - x)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hx
    simp [binomialCountSupport, hx.1, hx.2.2, Nat.add_sub_of_le hx.2.1]
  · intro x _ y _ h
    exact (Prod.mk.inj h).1
  · intro ⟨x, y⟩ hy
    simp only [Finset.mem_filter, binomialCountSupport, Finset.mem_product, Finset.mem_range,
      Nat.lt_succ_iff] at hy
    refine ⟨x, ?_, ?_⟩
    · simp [hy.1.1, ← hy.2]; omega
    · simp [← hy.2]

theorem probability (sizes : FixedSampleDesign) (a b : ℕ) (corrected : Bool) (p : unitInterval) :
    (productBinomial sizes.nControl sizes.nTreatment p p).real (rejection sizes a b corrected) =
      PolynomialBound.value (sizes.nControl + sizes.nTreatment) 1
        (weight sizes.nControl sizes.nTreatment a b corrected) p := by
  classical
  have maps : ∀ xy ∈ binomialCountSupport sizes.nControl sizes.nTreatment,
      xy.1 + xy.2 ∈ Finset.range (sizes.nControl + sizes.nTreatment + 1) := by
    intro xy h
    simp only [binomialCountSupport, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] at h ⊢
    exact Nat.add_le_add h.1 h.2
  rw [productBinomial_real_eq_sum, PolynomialBound.value, ← Finset.sum_fiberwise_of_maps_to maps]
  apply Finset.sum_congr rfl
  intro total _
  rw [weight_fiber, Nat.cast_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro xy h
  simp only [Finset.mem_filter, binomialCountSupport, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff] at h
  have expo : sizes.nControl + sizes.nTreatment - total =
      (sizes.nControl - xy.1) + (sizes.nTreatment - xy.2) := by omega
  by_cases member : xy ∈ rejection sizes a b corrected
  · have reject : rejects sizes.nControl sizes.nTreatment a b corrected xy.1 xy.2 := member
    rw [ite_eq_left member, expo, ← h.2]
    simp only [tableWeight, ite_eq_left reject]
    simp only [binomialMass, ← Nat.choose_eq_fast_choose, Nat.cast_mul, Nat.cast_one,
      div_one, pow_add]
    ring
  · have reject : ¬ rejects sizes.nControl sizes.nTreatment a b corrected xy.1 xy.2 := member
    simp only [ite_eq_right member, tableWeight, ite_eq_right reject, Nat.cast_zero, zero_mul,
      zero_div]

def weights (sizes : FixedSampleDesign) (a b : ℕ) (corrected : Bool) : List ℕ :=
  PolynomialBound.weights (sizes.nControl + sizes.nTreatment)
    (weight sizes.nControl sizes.nTreatment a b corrected)

end StatClaim.Modules.Pearson
