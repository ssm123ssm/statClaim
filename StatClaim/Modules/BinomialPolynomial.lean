module

public import StatClaim.Modules.PolynomialBound

/-! Combine binomial tables with the same total successes into a null probability polynomial. -/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.BinomialPolynomial

open MeasureTheory

def region (rejects : ℕ → ℕ → Prop) : Set (ℕ × ℕ) :=
  {xy | rejects xy.1 xy.2}

def tableWeight (nc nt : ℕ) (rejects : ℕ → ℕ → Prop) [DecidableRel rejects] (xy : ℕ × ℕ) : ℕ :=
  if rejects xy.1 xy.2 then
    nc.fast_choose xy.1 * nt.fast_choose xy.2
  else 0

def weight (nc nt : ℕ) (rejects : ℕ → ℕ → Prop) [DecidableRel rejects] (total : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (nc + 1) with x ≤ total ∧ total - x ≤ nt,
    tableWeight nc nt rejects (x, total - x)

private theorem weight_fiber (nc nt : ℕ) (rejects : ℕ → ℕ → Prop) [DecidableRel rejects]
    (total : ℕ) :
    weight nc nt rejects total =
      ∑ xy ∈ binomialCountSupport nc nt with xy.1 + xy.2 = total,
        tableWeight nc nt rejects xy := by
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

theorem probability (sizes : FixedSampleDesign) (rejects : ℕ → ℕ → Prop)
    [DecidableRel rejects] (p : unitInterval) :
    (productBinomial sizes.nControl sizes.nTreatment p p).real (region rejects) =
      PolynomialBound.value (sizes.nControl + sizes.nTreatment) 1
        (weight sizes.nControl sizes.nTreatment rejects) p := by
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
  by_cases member : xy ∈ region rejects
  · have reject : rejects xy.1 xy.2 := member
    rw [ite_eq_left member, expo, ← h.2]
    simp only [tableWeight, ite_eq_left reject]
    simp only [binomialMass, ← Nat.choose_eq_fast_choose, Nat.cast_mul, Nat.cast_one,
      div_one, pow_add]
    ring
  · have reject : ¬ rejects xy.1 xy.2 := member
    simp only [ite_eq_right member, tableWeight, ite_eq_right reject, Nat.cast_zero, zero_mul,
      zero_div]

end StatClaim.Modules.BinomialPolynomial
