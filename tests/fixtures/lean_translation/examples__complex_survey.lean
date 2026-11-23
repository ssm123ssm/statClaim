set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  survey_Parameter : Type
  survey_Outcome : Type
  [survey_space : MeasurableSpace survey_Outcome]
  survey : StatClaim.Interface.ObservationalModel survey_Parameter survey_Outcome
  weighted_test : StatClaim.Interface.TestInterface survey_Outcome
  weighted_slack : ℝ
attribute [instance] Instance.survey_space

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.survey.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.survey.noAssociation

-- Contract facts the Python compiler checks, decided by Lean.

theorem weighted_contract :
    StatClaim.Generated.ObservationalDesign.cross_sectional ∈ StatClaim.Generated.Methods.survey_linear.designs ∧
    StatClaim.Generated.Scale.continuous ∈ StatClaim.Generated.Methods.survey_linear.outcomeScales ∧
    StatClaim.Generated.Scale.binary ∈ StatClaim.Generated.Methods.survey_linear.exposureScales ∧
    StatClaim.Generated.Survey.weighted ∈ StatClaim.Generated.Methods.survey_linear.surveys ∧
    StatClaim.Generated.Methods.survey_linear.minTotal ≤ 8000 ∧
    StatClaim.Generated.Methods.survey_linear.covariates = true := by decide

theorem weighted_values :
    (0 : ℚ) < ((1 : ℚ) / 20) ∧
    ((1 : ℚ) / 20) < 1 := by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  weighted_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.survey_linear.scope i.survey.law (null i)
    i.weighted_test ((1 : ℚ) / 20) i.weighted_slack

theorem checked_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.weighted_test ((↑((1 : ℚ) / 20) : ℝ) + i.weighted_slack) :=
  StatClaim.Interface.typeI_of_premise (design_compatible i) premises.weighted_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.weighted_test ((↑((1 : ℚ) / 20) : ℝ) + i.weighted_slack)

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  survey_Parameter := Unit
  survey_Outcome := Unit
  survey := StatClaim.Interface.ObservationalModel.trivial
  weighted_test := StatClaim.Interface.TestInterface.neverRejects _
  weighted_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => checked_claim i premises
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩
