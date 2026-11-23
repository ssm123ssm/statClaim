set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  study_Parameter : Type
  study_Outcome : Type
  [study_space : MeasurableSpace study_Outcome]
  study : StatClaim.Interface.TwoArmModel study_Parameter study_Outcome
  analysis_test : StatClaim.Interface.TestInterface study_Outcome
  analysis_slack : ℝ
  welch_test : StatClaim.Interface.TestInterface study_Outcome
  welch_slack : ℝ
  small_arm_Parameter : Type
  small_arm_Outcome : Type
  [small_arm_space : MeasurableSpace small_arm_Outcome]
  small_arm : StatClaim.Interface.TwoArmModel small_arm_Parameter small_arm_Outcome
  student_test : StatClaim.Interface.TestInterface small_arm_Outcome
  student_slack : ℝ
attribute [instance] Instance.study_space
attribute [instance] Instance.small_arm_space

noncomputable def plan (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.study.toModel

noncomputable def plan_compatible (i : Instance) :
    StatClaim.Core.Compatibility (plan i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

def margin (i : Instance) :=
  i.study.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-2 : ℚ)

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.small_arm.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.small_arm.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

-- Contract facts the Python compiler checks, decided by Lean.

theorem analysis_contract :
    StatClaim.Generated.NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls ∧
    StatClaim.Generated.NullKey.equal_means.outcome = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.Methods.t_test.unit = .participant ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 60 ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 60 ∧
    StatClaim.Generated.Methods.t_test.minTotal ≤ 60 + 60 ∧
    StatClaim.Generated.Methods.t_test.nullValue = none :=
  by decide

theorem analysis_values :
    (0 : ℚ) < ((1 : ℚ) / 20) ∧
    ((1 : ℚ) / 20) < 1 :=
  by norm_num

theorem welch_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.welch_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.welch_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 60 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 60 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minTotal ≤ 60 + 60 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.nullValue = none :=
  by decide

theorem welch_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem student_contract :
    StatClaim.Generated.NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls ∧
    StatClaim.Generated.NullKey.equal_means.outcome = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.Methods.t_test.unit = .participant ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 20 ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 40 ∧
    StatClaim.Generated.Methods.t_test.minTotal ≤ 20 + 40 ∧
    StatClaim.Generated.Methods.t_test.nullValue = none :=
  by decide

theorem student_values :
    (0 : ℚ) < ((1 : ℚ) / 20) ∧
    ((1 : ℚ) / 20) < 1 :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  cited_analysis_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.analysis_test ((1 : ℚ) / 20) i.analysis_slack
  cited_welch_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.study.law (margin i)
    i.welch_test ((1 : ℚ) / 40) i.welch_slack
  cited_student_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.small_arm.law (null_1 i)
    i.student_test ((1 : ℚ) / 20) i.student_slack

theorem checked_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.analysis_test (↑((1 : ℚ) / 20) : ℝ) :=
  StatClaim.Interface.typeI_of_finite_premise (plan_compatible i) rfl premises.cited_analysis_level

theorem approximate_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim (plan_compatible i) (margin i) i.welch_test ((↑((1 : ℚ) / 40) : ℝ) + i.welch_slack) :=
  StatClaim.Interface.typeI_of_premise (plan_compatible i) premises.cited_welch_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.analysis_test (↑((1 : ℚ) / 20) : ℝ)) ∧
  (StatClaim.Interface.typeIClaim (plan_compatible i) (margin i) i.welch_test ((↑((1 : ℚ) / 40) : ℝ) + i.welch_slack))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  study_Parameter := Unit
  study_Outcome := Unit
  study := StatClaim.Interface.TwoArmModel.trivial
  analysis_test := StatClaim.Interface.TestInterface.neverRejects _
  analysis_slack := 0
  welch_test := StatClaim.Interface.TestInterface.neverRejects _
  welch_slack := 0
  small_arm_Parameter := Unit
  small_arm_Outcome := Unit
  small_arm := StatClaim.Interface.TwoArmModel.trivial
  student_test := StatClaim.Interface.TestInterface.neverRejects _
  student_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨checked_claim i premises, approximate_claim i premises⟩
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("checked_claim", ``checked_claim), ("approximate_claim", ``approximate_claim)] do
    let found ← IO.mkRef ({} : NameSet)
    let mut seen : NameSet := {}
    let mut stack := [claim]
    while !stack.isEmpty do
      let current := stack.head!
      stack := stack.tail!
      if seen.contains current then continue
      seen := seen.insert current
      let some info := env.find? current | continue
      let value := match info with
        | .thmInfo theorem_ => some theorem_.value
        | .defnInfo definition => some definition.value
        | _ => none
      for e in info.type :: value.toList do
        discard <| liftCoreM <| Core.transform e (pre := fun e => do
          if let .proj name index _ := e then
            if name == structureName then
              if let some field := fields[index]? then found.modify (·.insert field)
          return .continue)
        for constant in e.getUsedConstants do
          if claim.getPrefix.isPrefixOf constant && !seen.contains constant then
            stack := constant :: stack
    let used := (← found.get).toList.map toString |>.mergeSort (· < ·)
    logInfo m!"STATCLAIM_PREMISES examples/t_test.stat {short}: {String.intercalate "," used}"
