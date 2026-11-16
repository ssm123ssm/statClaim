import StatClaim.Modules.Fisher
import StatClaim.Computation

/-!
The first analysis expressed through the shared objects. This is ordinary Lean
code, not the proposed statistical grammar. Run `make objects-demo` to check it.
-/

namespace StatClaim.Examples.FisherObjects

open Core

def sizes : FixedSampleDesign := ⟨100, 100, by decide, by decide⟩

noncomputable def studyModel := Modules.TwoArmBinomial.model sizes
noncomputable def design := StudyDesign.fixed studyModel
noncomputable def analysis := Modules.Fisher.analysis sizes design

-- The design-level guarantee exists before any observations are supplied.
noncomputable def guarantee : TypeIGuarantee analysis (defaultLevel.value : ℝ) :=
  (Modules.Fisher.module sizes).provide design ⟨Compatibility.fixed studyModel⟩

def observation : Observation studyModel :=
  Modules.TwoArmBinomial.observe sizes 10 25 (by decide) (by decide)

-- A proposed value is not automatically accompanied by a correctness proof.
def proposedResult : Result analysis where
  observation := observation
  value := (19912805355158606332329 : ℚ) / 2341699062001756564467919

theorem result_matches_definition : proposedResult.exactClaim.statement := by
  change (19912805355158606332329 : ℚ) / 2341699062001756564467919 =
    hypergeometricPValue 100 100 35 10
  symm
  apply hypergeometricPValue_eq_of_cross_product 100 100 35 10
    19912805355158606332329 2341699062001756564467919 (by decide) (by decide)
  decide +kernel

theorem resultCertificate : Certificate proposedResult.exactClaim := ⟨result_matches_definition⟩

noncomputable def modifiedDesign := StudyDesign.unresolvedAdaptive studyModel
noncomputable def modifiedAnalysis := Modules.Fisher.analysis sizes modifiedDesign

-- This establishes a missing provider requirement, not an inflated error rate.
theorem stopping_justification_missing :
    ¬ (Modules.Fisher.module sizes).Requires modifiedDesign :=
  Modules.Fisher.adaptive_requirement_missing sizes

#check analysis
#check guarantee.certificate.establishes
#check resultCertificate.establishes
#check stopping_justification_missing

end StatClaim.Examples.FisherObjects
