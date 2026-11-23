set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes design analysis_level

-- Contract facts the Python compiler checks, decided by Lean.

theorem analysis_null :
    ∀ parameter, null parameter ↔ analysis.hypothesis parameter :=
  fun parameter => Iff.rfl

theorem analysis_contract :
    (StatClaim.Modules.Fisher.module study_sizes analysis_level).Requires
      design :=
  ⟨design_compatible⟩

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

theorem verification_claim (i : Instance) (premises : Premises i) :
    (analysis.typeIClaim design_compatible
      (analysis_level.value : ℝ)).statement :=
  StatClaim.Modules.Fisher.typeI_statement study_sizes design design_compatible analysis_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim design_compatible
      (analysis_level.value : ℝ)).statement

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance := ⟨⟩

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => verification_claim i premises
  satisfiable := ⟨witness, ⟨⟩⟩
