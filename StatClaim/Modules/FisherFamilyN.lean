module

public import StatClaim.Modules.FisherFamily

/-!
Any finite number of Fisher analyses composed with Bonferroni. The joint
sampling law is an input whose binomial marginals must be proved. Dependence
between outcomes is unrestricted.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.FisherFamilyN

open MeasureTheory TwoArmBinomial

abbrev Parameters (m : ℕ) := Fin m → TwoArmBinomial.Parameters
abbrev Outcomes (m : ℕ) := Fin m → Counts

variable {m : ℕ}

/-- Each outcome's counts follow that outcome's two-arm binomial model. -/
def MarginalContract (designs : Fin m → FixedSampleDesign)
    (law : Core.SamplingLaw (Parameters m) (Outcomes m)) : Prop :=
  ∀ parameter i,
    (law.law parameter).map (fun outcome : Outcomes m => outcome i) = (model (designs i)).law (parameter i)

noncomputable def family (designs : Fin m → FixedSampleDesign)
    (levels : Fin m → SignificanceLevel)
    (law : Core.SamplingLaw (Parameters m) (Outcomes m)) :
    Bonferroni.Family m (Parameters m) (Outcomes m) where
  samplingLaw := law
  hypothesis := fun i parameter => equalProportions (parameter i)
  rejectionEvent := fun i =>
    (fun outcome : Outcomes m => outcome i) ⁻¹'
      (Fisher.procedure (designs i) (levels i)).rejectionEvent
  rejection_measurable := fun i =>
    (Fisher.procedure (designs i) (levels i)).rejection_measurable.preimage
      (measurable_pi_apply i)
  budget := fun i => ((levels i).value : ℝ)
  budget_nonnegative := fun i => by exact_mod_cast (levels i).nonnegative

theorem marginal_bounds (designs : Fin m → FixedSampleDesign)
    (levels : Fin m → SignificanceLevel)
    (law : Core.SamplingLaw (Parameters m) (Outcomes m))
    (matching : MarginalContract designs law) :
    (family designs levels law).marginalBounds := by
  intro i parameter null
  exact FisherFamily.marginal_bound (designs i) (levels i) _ (fun outcome : Outcomes m => outcome i)
    (measurable_pi_apply i) (parameter i) (matching parameter i) null

/-- Strong control: valid for every configuration of true and false nulls. -/
theorem strong_control (designs : Fin m → FixedSampleDesign)
    (levels : Fin m → SignificanceLevel) (alpha : ℚ)
    (allocation : ∑ i, (levels i).value ≤ alpha)
    (law : Core.SamplingLaw (Parameters m) (Outcomes m))
    (matching : MarginalContract designs law) :
    ((family designs levels law).familywiseClaim (alpha : ℝ)).statement := by
  apply Bonferroni.strong_control _ (marginal_bounds designs levels law matching)
  have cast : ((∑ i, (levels i).value : ℚ) : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast allocation
  simpa [family] using cast

end StatClaim.Modules.FisherFamilyN
