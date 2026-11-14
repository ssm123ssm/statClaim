import StatProof.Modules.Fisher

/-!
Verify the design before collecting data. No observed success counts, numerical
p-values, or proposed calculation results are needed for this guarantee.
-/

namespace StatProof.Examples.DesignGuarantee

open Core

def sizes : FixedSampleDesign := ⟨100, 100, by decide, by decide⟩
noncomputable def studyModel := Modules.TwoArmBinomial.model sizes
noncomputable def design := StudyDesign.fixed studyModel
noncomputable def analysis := Modules.Fisher.analysis sizes design

noncomputable def guarantee : TypeIGuarantee analysis (1 / 20 : ℝ) :=
  (Modules.Fisher.module sizes).provide design ⟨Compatibility.fixed studyModel⟩

-- The guarantee quantifies over the null-model parameters; no data are supplied.
#check analysis
#check guarantee.certificate.establishes

noncomputable def modifiedDesign := StudyDesign.unresolvedAdaptive studyModel
theorem stopping_justification_missing :
    ¬ (Modules.Fisher.module sizes).Requires modifiedDesign :=
  Modules.Fisher.adaptive_requirement_missing sizes

#check stopping_justification_missing

end StatProof.Examples.DesignGuarantee
