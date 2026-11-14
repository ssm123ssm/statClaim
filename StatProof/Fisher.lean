module

public import StatProof.BinomialModel
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.MeasureTheory.Measure.Prod

/-!
Connect the finite model to Mathlib's probability measures: the null law is the
product of two binomial distributions with a common success probability.
The rejection event is the feasible set of tables whose specified exact
two-sided p-value is at most 1/20.

This is a mathematical guarantee under that model. No theorem here establishes
correspondence with a Python execution or the truth of a study's assumptions.
-/

@[expose] public section

namespace StatProof

/-- The null law of independent binomial counts, with the same success probability. -/
noncomputable def fisherNullLaw (nControl nTreatment : ℕ) (p : unitInterval) :
    MeasureTheory.Measure (ℕ × ℕ) :=
  (ProbabilityTheory.binomial nControl p).prod (ProbabilityTheory.binomial nTreatment p)

instance fisherNullLaw_isProbabilityMeasure (nControl nTreatment : ℕ) (p : unitInterval) :
    MeasureTheory.IsProbabilityMeasure (fisherNullLaw nControl nTreatment p) := by
  unfold fisherNullLaw
  infer_instance

/-- The feasible tables rejected by the exact probability-ordered test. -/
def fisherRejectionRegion (nControl nTreatment : ℕ) : Finset (ℕ × ℕ) :=
  (binomialCountSupport nControl nTreatment).filter (fun counts =>
    hypergeometricPValue nControl nTreatment (counts.1 + counts.2) counts.1 ≤ targetAlpha)

/-- The finite-model binomial formula agrees with Mathlib's binomial measure. -/
theorem binomialMass_eq_mathlib (n k : ℕ) (p : unitInterval) :
    binomialMass n (p : ℝ) k = (ProbabilityTheory.binomial n p).real {k} := by
  exact (ProbabilityTheory.binomial_real_singleton n k p).symm

theorem fisherNullLaw_real_singleton (nControl nTreatment : ℕ) (p : unitInterval)
    (counts : ℕ × ℕ) :
    (fisherNullLaw nControl nTreatment p).real {counts} =
      independentBinomialMass nControl nTreatment (p : ℝ) counts := by
  rcases counts with ⟨control, treatment⟩
  rw [show ({(control, treatment)} : Set (ℕ × ℕ)) = {control} ×ˢ {treatment} from
    Set.singleton_prod_singleton.symm]
  simp only [fisherNullLaw, MeasureTheory.measureReal_prod_prod,
    ← binomialMass_eq_mathlib, independentBinomialMass]

/-- Restricting the rejection event to feasible tables loses no probability. -/
theorem fisherNullLaw_real_support (nControl nTreatment : ℕ) (p : unitInterval) :
    (fisherNullLaw nControl nTreatment p).real (binomialCountSupport nControl nTreatment) = 1 := by
  have singletons := MeasureTheory.sum_measureReal_singleton
    (μ := fisherNullLaw nControl nTreatment p) (binomialCountSupport nControl nTreatment)
  rw [← singletons]
  simp only [fisherNullLaw_real_singleton]
  exact independentBinomialMass_sum_one nControl nTreatment (p : ℝ)

/-- The finite sum being bounded is the actual rejection-event probability
under the product of Mathlib's binomial measures. -/
theorem fisherNullLaw_rejection_probability (nControl nTreatment : ℕ) (p : unitInterval) :
    (fisherNullLaw nControl nTreatment p).real (fisherRejectionRegion nControl nTreatment) =
      fisherNullRejectionProbability nControl nTreatment (p : ℝ) := by
  have singletons := MeasureTheory.sum_measureReal_singleton
    (μ := fisherNullLaw nControl nTreatment p) (fisherRejectionRegion nControl nTreatment)
  rw [← singletons]
  simp only [fisherNullLaw_real_singleton, fisherRejectionRegion, Finset.sum_filter,
    fisherNullRejectionProbability]

/-- Fisher's exact test controls Type I error uniformly over all common success
probabilities in the closed unit interval, including both endpoints. -/
theorem fisher_typeI_error_le (nControl nTreatment : ℕ) (p : unitInterval) :
    (fisherNullLaw nControl nTreatment p).real (fisherRejectionRegion nControl nTreatment) ≤
      (1 / 20 : ℝ) := by
  rw [fisherNullLaw_rejection_probability]
  have bound := fisherNullRejectionProbability_le_targetAlpha nControl nTreatment
    (p : ℝ) p.property.1 p.property.2
  simpa only [targetAlpha, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using bound

end StatProof
