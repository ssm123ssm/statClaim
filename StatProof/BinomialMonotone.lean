module

public import StatProof.ProductBinomial

/-!
Binomial probabilities of upper sets do not decrease as the success probability
increases. This turns a bound checked at one null rate into a bound for every
smaller rate. The proof is an induction on the sample size using Pascal's rule;
no calculus or coupling is needed.
-/

@[expose] public section

namespace StatProof

open MeasureTheory

theorem binomialMass_eq_zero_of_lt {n k : ℕ} (p : ℝ) (h : n < k) : binomialMass n p k = 0 := by
  simp [binomialMass, Nat.choose_eq_zero_of_lt h]

theorem binomialMass_zero_succ (n : ℕ) (p : ℝ) :
    binomialMass (n + 1) p 0 = (1 - p) * binomialMass n p 0 := by
  simp only [binomialMass, Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, pow_succ]
  ring

theorem binomialMass_succ_succ (n k : ℕ) (p : ℝ) :
    binomialMass (n + 1) p (k + 1) =
      p * binomialMass n p k + (1 - p) * binomialMass n p (k + 1) := by
  unfold binomialMass
  rw [Nat.choose_succ_succ]
  have e1 : n + 1 - (k + 1) = n - k := by omega
  by_cases h : k + 1 ≤ n
  · have e2 : n - k = (n - (k + 1)) + 1 := by omega
    rw [e1, e2]
    push_cast
    ring
  · have vanish : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [vanish, e1]
    push_cast
    ring

/-- Expectation of a function of a binomial count, as a finite sum. -/
def binomialExpectation (n : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), binomialMass n p k * f k

theorem binomialExpectation_succ (n : ℕ) (p : ℝ) (f : ℕ → ℝ) :
    binomialExpectation (n + 1) p f =
      p * binomialExpectation n p (fun k => f (k + 1)) + (1 - p) * binomialExpectation n p f := by
  unfold binomialExpectation
  have shift : ∑ k ∈ Finset.range (n + 1), binomialMass n p k * f k =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p (k + 1) * f (k + 1) +
        binomialMass n p 0 * f 0 := by
    rw [Finset.sum_range_succ' _ n, Finset.sum_range_succ _ n,
      binomialMass_eq_zero_of_lt p (Nat.lt_succ_self n)]
    ring
  rw [Finset.sum_range_succ' _ (n + 1), binomialMass_zero_succ, shift]
  simp_rw [binomialMass_succ_succ, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  simp only [mul_assoc, add_assoc]

theorem binomialExpectation_le (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ℕ → ℝ}
    (h : ∀ k, f k ≤ g k) : binomialExpectation n p f ≤ binomialExpectation n p g :=
  Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (h k) (binomialMass_nonnegative n p k hp0 hp1)

/-- A nondecreasing function has a nondecreasing binomial expectation. -/
theorem binomialExpectation_mono (n : ℕ) : ∀ f : ℕ → ℝ, Monotone f → ∀ p q : ℝ,
    0 ≤ p → p ≤ q → q ≤ 1 → binomialExpectation n p f ≤ binomialExpectation n q f := by
  induction n with
  | zero =>
    intro f _ p q _ _ _
    simp [binomialExpectation, binomialMass]
  | succ n ih =>
    intro f mono p q hp hpq hq
    rw [binomialExpectation_succ, binomialExpectation_succ]
    have shifted : Monotone (fun k => f (k + 1)) := fun a b hab => mono (by omega)
    have A := ih _ shifted p q hp hpq hq
    have B := ih f mono p q hp hpq hq
    have AB := binomialExpectation_le n p hp (hpq.trans hq) (f := f)
      (g := fun k => f (k + 1)) (fun k => mono (Nat.le_succ k))
    nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr AB),
      mul_le_mul_of_nonneg_left A (hp.trans hpq),
      mul_le_mul_of_nonneg_left B (sub_nonneg.mpr hq)]

/-- A binomial event's probability as an expectation of its indicator. -/
theorem binomial_real_eq_expectation (n : ℕ) (p : unitInterval) (event : Set ℕ)
    [DecidablePred (· ∈ event)] :
    (ProbabilityTheory.binomial n p).real event =
      binomialExpectation n (p : ℝ) (fun k => if k ∈ event then 1 else 0) := by
  set μ := ProbabilityTheory.binomial n p
  have supported : μ.real (↑(Finset.range (n + 1)) : Set ℕ) = 1 := by
    rw [← sum_measureReal_singleton]
    simp only [μ, ← binomialMass_eq_mathlib]
    exact binomialMass_sum_one n (p : ℝ)
  have outside : μ.real (↑(Finset.range (n + 1)) : Set ℕ)ᶜ = 0 := by
    rw [measureReal_compl (Finset.measurableSet _), probReal_univ, supported, sub_self]
  have rest : μ.real (event \ ↑(Finset.range (n + 1))) = 0 :=
    measureReal_mono_null (fun _ member => member.2) outside
  have split := measureReal_inter_add_sdiff (μ := μ) (s := event)
    (Finset.measurableSet (Finset.range (n + 1)))
  rw [rest, add_zero] at split
  rw [← split]
  have finite : event ∩ ↑(Finset.range (n + 1)) =
      ↑((Finset.range (n + 1)).filter (· ∈ event)) := by
    ext k
    simp [and_comm]
  rw [finite, ← sum_measureReal_singleton, Finset.sum_filter]
  simp only [μ, ← binomialMass_eq_mathlib, binomialExpectation, mul_ite, mul_one, mul_zero]

/-- Upper sets become more likely as the success probability increases. -/
theorem binomial_real_mono (n : ℕ) (p q : unitInterval) (h : p ≤ q) (event : Set ℕ)
    (upper : ∀ a b, a ≤ b → a ∈ event → b ∈ event) :
    (ProbabilityTheory.binomial n p).real event ≤ (ProbabilityTheory.binomial n q).real event := by
  classical
  rw [binomial_real_eq_expectation, binomial_real_eq_expectation]
  refine binomialExpectation_mono n _ ?_ p q p.property.1 h q.property.2
  intro a b hab
  by_cases ha : a ∈ event
  · simp [ha, upper a b hab ha]
  · by_cases hb : b ∈ event <;> simp [ha, hb]

/-- A two-count event's probability as an iterated expectation. -/
theorem productBinomial_real_eq_expectation (n m : ℕ) (p q : unitInterval)
    (event : Set (ℕ × ℕ)) [DecidablePred (· ∈ event)] :
    (productBinomial n m p q).real event =
      binomialExpectation n (p : ℝ) (fun x =>
        binomialExpectation m (q : ℝ) (fun y => if (x, y) ∈ event then 1 else 0)) := by
  rw [productBinomial_real_eq_sum, binomialCountSupport, Finset.sum_product]
  unfold binomialExpectation
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases member : (x, y) ∈ event <;> simp [member]

/-- Upper sets of two counts become more likely as the common rate increases. -/
theorem productBinomial_real_mono (n m : ℕ) (p q : unitInterval) (h : p ≤ q)
    (event : Set (ℕ × ℕ))
    (upper : ∀ a b : ℕ × ℕ, a.1 ≤ b.1 → a.2 ≤ b.2 → a ∈ event → b ∈ event) :
    (productBinomial n m p p).real event ≤ (productBinomial n m q q).real event := by
  classical
  rw [productBinomial_real_eq_expectation, productBinomial_real_eq_expectation]
  have inner : ∀ x, Monotone (fun y : ℕ => if (x, y) ∈ event then (1 : ℝ) else 0) := by
    intro x a b hab
    by_cases ha : (x, a) ∈ event
    · simp [ha, upper (x, a) (x, b) le_rfl hab ha]
    · by_cases hb : (x, b) ∈ event <;> simp [ha, hb]
  refine le_trans (binomialExpectation_le n p p.property.1 p.property.2 (fun x =>
    binomialExpectation_mono m _ (inner x) p q p.property.1 h q.property.2)) ?_
  refine binomialExpectation_mono n _ ?_ p q p.property.1 h q.property.2
  intro a b hab
  refine binomialExpectation_le m q q.property.1 q.property.2 (fun y => ?_)
  by_cases ha : (a, y) ∈ event
  · simp [ha, upper (a, y) (b, y) hab le_rfl ha]
  · by_cases hb : (b, y) ∈ event <;> simp [ha, hb]

end StatProof
