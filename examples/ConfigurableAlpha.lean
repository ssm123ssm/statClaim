import StatProof.Modules.Fisher

namespace StatProof.Examples.ConfigurableAlpha

open Core

def sizes : FixedSampleDesign := ⟨200, 100, by decide, by decide⟩
def level : SignificanceLevel := ⟨1 / 40, by norm_num, by norm_num⟩
noncomputable def studyModel := Modules.TwoArmBinomial.model sizes
noncomputable def design := StudyDesign.fixed studyModel
noncomputable def analysis := Modules.Fisher.analysis sizes design level

noncomputable def guarantee : TypeIGuarantee analysis (level.value : ℝ) :=
  (Modules.Fisher.module sizes level).provide design ⟨Compatibility.fixed studyModel⟩

#check guarantee.certificate.establishes

end StatProof.Examples.ConfigurableAlpha
