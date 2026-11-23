set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  study_Parameter : Type
  study_Outcome : Type
  [study_space : MeasurableSpace study_Outcome]
  study : StatClaim.Interface.TwoArmModel study_Parameter study_Outcome
  pain_test : StatClaim.Interface.TestInterface study_Outcome
  pain_slack : ℝ
  function_test : StatClaim.Interface.TestInterface study_Outcome
  function_slack : ℝ
attribute [instance] Instance.study_space

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

-- Contract facts the Python compiler checks, decided by Lean.

-- Declared by the author: Van Elteren stratified rank test, stratified by site. Reference: Statistical analysis plan, section 9.2.

theorem pain_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 := by norm_num

theorem function_contract :
    StatClaim.Generated.NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls ∧
    StatClaim.Generated.NullKey.equal_means.outcome = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.Methods.t_test.unit = .participant ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 200 ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 200 ∧
    StatClaim.Generated.Methods.t_test.minTotal ≤ 200 + 200 ∧
    StatClaim.Generated.Methods.t_test.nullValue = none := by decide

theorem function_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 := by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  pain_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.study.law (null i)
    i.pain_test ((1 : ℚ) / 40) i.pain_slack
  function_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.function_test ((1 : ℚ) / 40) i.function_slack

theorem alone_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.pain_test ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack) :=
  StatClaim.Interface.typeI_of_premise (plan_compatible i) premises.pain_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.pain_test ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack)

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  study_Parameter := Unit
  study_Outcome := Unit
  study := StatClaim.Interface.TwoArmModel.trivial
  pain_test := StatClaim.Interface.TestInterface.neverRejects _
  pain_slack := 0
  function_test := StatClaim.Interface.TestInterface.neverRejects _
  function_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => alone_claim i premises
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩
