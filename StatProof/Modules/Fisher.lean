module

public import StatProof.Modules.TwoArmBinomial

/-!
Fisher as a provider over the shared objects. The model theorem is reused;
sampling compatibility is required explicitly, and missing law information is
an unresolved requirement rather than a claim about the actual error rate.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.Fisher

open TwoArmBinomial

noncomputable def procedure (sizes : FixedSampleDesign) : Core.Procedure (model sizes) where
  Output := ℚ
  evaluate := fun counts =>
    hypergeometricPValue sizes.nControl sizes.nTreatment (counts.1 + counts.2) counts.1
  reject := fun value => value ≤ targetAlpha
  rejection_measurable := .of_discrete

noncomputable def analysis (sizes : FixedSampleDesign) (design : Core.StudyDesign (model sizes)) :
    Core.Analysis (model sizes) where
  design := design
  hypothesis := equalProportions
  procedure := procedure sizes

/-- The shared procedure denotes exactly the existing formal rejection region. -/
theorem rejectionEvent_eq (sizes : FixedSampleDesign) :
    (procedure sizes).rejectionEvent =
      (↑(fisherRejectionRegion sizes.nControl sizes.nTreatment) : Set Counts) := by
  ext counts
  change ((counts.1 ≤ sizes.nControl ∧ counts.2 ≤ sizes.nTreatment) ∧
    hypergeometricPValue sizes.nControl sizes.nTreatment (counts.1 + counts.2) counts.1 ≤
      targetAlpha) ↔ counts ∈ fisherRejectionRegion sizes.nControl sizes.nTreatment
  simp [fisherRejectionRegion, binomialCountSupport]

/-- Lift the existing Type I theorem into a claim about the analysis and the
explicitly supplied sampling law. It requires no observed data. -/
theorem typeI_statement (sizes : FixedSampleDesign) (design : Core.StudyDesign (model sizes))
    (compatibility : Core.Compatibility design) :
    ((analysis sizes design).typeIClaim compatibility (1 / 20 : ℝ)).statement := by
  intro parameter null
  change (compatibility.samplingLaw.law parameter).real (procedure sizes).rejectionEvent ≤ _
  rw [compatibility.agrees, law_under_null sizes parameter null, rejectionEvent_eq]
  exact fisher_typeI_error_le sizes.nControl sizes.nTreatment parameter.1

/-- Contract-driven provider for the fixed Fisher specification. A new design
must supply matching-law evidence before obtaining the output guarantee. -/
noncomputable def module (sizes : FixedSampleDesign) : Core.Module (Core.StudyDesign (model sizes)) where
  name := "tests.fisher.two_sided_probability_ordered"
  version := "0.1.0"
  Requires := fun design => Nonempty (Core.Compatibility design)
  Output := fun design => Core.TypeIGuarantee (analysis sizes design) (1 / 20 : ℝ)
  provide := fun design requirement => {
    compatibility := Classical.choice requirement
    certificate := ⟨typeI_statement sizes design (Classical.choice requirement)⟩ }

noncomputable def fixedGuarantee (sizes : FixedSampleDesign) :
    Core.TypeIGuarantee (analysis sizes (Core.StudyDesign.fixed (model sizes))) (1 / 20 : ℝ) :=
  (module sizes).provide _ ⟨Core.Compatibility.fixed (model sizes)⟩

/-- This only states that the provider's contract is not discharged for an
unspecified adaptive law. It does not refute the proposed statistical guarantee. -/
theorem adaptive_requirement_missing (sizes : FixedSampleDesign) :
    ¬ (module sizes).Requires (Core.StudyDesign.unresolvedAdaptive (model sizes)) := by
  exact Core.no_compatibility_without_law _ rfl

def adaptiveObligations : List String := [
  "Specify the sampling law induced by the data-dependent stopping mechanism.",
  "Establish compatibility with the model, or supply a suitable replacement error-bound theorem."]

end StatProof.Modules.Fisher
