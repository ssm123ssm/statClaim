set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.unresolvedAdaptive study

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

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  True

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance := ⟨⟩

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => trivial
  satisfiable := ⟨witness, ⟨⟩⟩
