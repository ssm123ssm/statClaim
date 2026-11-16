module

public import StatClaim.Modules.Fisher
public import StatClaim.Modules.Bonferroni

/-!
Two Fisher analyses composed with Bonferroni. The joint sampling law is an
explicit input; its binomial marginal contracts must be proved. Dependence
between the two outcomes is unrestricted. Within each outcome, the two arms
still have the independent-binomial law specified by TwoArmBinomial.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.FisherFamily

open MeasureTheory TwoArmBinomial

abbrev Parameters := TwoArmBinomial.Parameters × TwoArmBinomial.Parameters
abbrev Outcomes := Counts × Counts

def MarginalContract (left right : FixedSampleDesign)
    (law : Core.SamplingLaw Parameters Outcomes) : Prop :=
  ∀ parameter,
    (law.law parameter).map Prod.fst = (model left).law parameter.1 ∧
    (law.law parameter).map Prod.snd = (model right).law parameter.2

noncomputable def family (left right : FixedSampleDesign)
    (leftLevel rightLevel : SignificanceLevel)
    (law : Core.SamplingLaw Parameters Outcomes) : Bonferroni.Family 2 Parameters Outcomes where
  samplingLaw := law
  hypothesis := fun i parameter => if i = 0 then equalProportions parameter.1
    else equalProportions parameter.2
  rejectionEvent := fun i => if i = 0 then
    Prod.fst ⁻¹' (Fisher.procedure left leftLevel).rejectionEvent
    else Prod.snd ⁻¹' (Fisher.procedure right rightLevel).rejectionEvent
  rejection_measurable := fun i => by
    split_ifs
    · exact (Fisher.procedure left leftLevel).rejection_measurable.preimage measurable_fst
    · exact (Fisher.procedure right rightLevel).rejection_measurable.preimage measurable_snd
  budget := fun i => if i = 0 then (leftLevel.value : ℝ) else (rightLevel.value : ℝ)
  budget_nonnegative := fun i => by
    split_ifs
    · exact_mod_cast leftLevel.nonnegative
    · exact_mod_cast rightLevel.nonnegative

/-- Transport a Fisher guarantee along a proved marginal-law equality. -/
theorem marginal_bound {Ω : Type} [MeasurableSpace Ω] (sizes : FixedSampleDesign)
    (level : SignificanceLevel) (μ : Measure Ω) (projection : Ω → Counts)
    (measurable : Measurable projection) (parameter : TwoArmBinomial.Parameters)
    (matching : μ.map projection = (model sizes).law parameter)
    (null : equalProportions parameter) :
    μ.real (projection ⁻¹' (Fisher.procedure sizes level).rejectionEvent) ≤ (level.value : ℝ) := by
  rw [← map_measureReal_apply (μ := μ) (s := (Fisher.procedure sizes level).rejectionEvent)
      measurable (Fisher.procedure sizes level).rejection_measurable,
    matching, law_under_null sizes parameter null, Fisher.rejectionEvent_eq sizes level]
  exact fisher_typeI_error_le_alpha sizes.nControl sizes.nTreatment parameter.1
    level.value level.nonnegative

theorem marginal_bounds (left right : FixedSampleDesign) (a b : SignificanceLevel)
    (law : Core.SamplingLaw Parameters Outcomes) (matching : MarginalContract left right law) :
    (family left right a b law).marginalBounds := by
  intro i parameter null
  by_cases first : i = 0
  · simp only [family, first, ite_true] at null ⊢
    exact marginal_bound left a _ Prod.fst measurable_fst parameter.1 (matching parameter).1 null
  · simp only [family, first, ite_false] at null ⊢
    exact marginal_bound right b _ Prod.snd measurable_snd parameter.2 (matching parameter).2 null

theorem allocation_eq (left right : FixedSampleDesign) (a b : SignificanceLevel)
    (law : Core.SamplingLaw Parameters Outcomes) :
    (∑ i, (family left right a b law).budget i) = (a.value : ℝ) + (b.value : ℝ) := by
  simp [Fin.sum_univ_two, family]

/-- Strong control: valid for every configuration of true and false endpoint nulls. -/
theorem strong_control (left right : FixedSampleDesign) (a b : SignificanceLevel)
    (alpha : ℝ) (allocation : (a.value : ℝ) + (b.value : ℝ) ≤ alpha)
    (law : Core.SamplingLaw Parameters Outcomes) (matching : MarginalContract left right law) :
    ((family left right a b law).familywiseClaim alpha).statement := by
  apply Bonferroni.strong_control _ (marginal_bounds left right a b law matching) alpha
  simpa only [allocation_eq] using allocation

noncomputable def module (left right : FixedSampleDesign) (a b : SignificanceLevel)
    (alpha : ℝ) : Core.Module (Core.SamplingLaw Parameters Outcomes) where
  name := "multiplicity.bonferroni.two_fisher"
  version := "0.1.0"
  Requires := fun law => MarginalContract left right law ∧ (a.value : ℝ) + (b.value : ℝ) ≤ alpha
  Output := fun law => Bonferroni.FamilywiseGuarantee (family left right a b law) alpha
  provide := fun law requirement =>
    ⟨⟨strong_control left right a b alpha requirement.2 law requirement.1⟩⟩

end StatClaim.Modules.FisherFamily
