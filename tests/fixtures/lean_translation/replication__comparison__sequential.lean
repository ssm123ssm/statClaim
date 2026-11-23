set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  halfway_Parameter : Type
  halfway_Outcome : Type
  [halfway_space : MeasurableSpace halfway_Outcome]
  halfway : StatClaim.Interface.TwoArmModel halfway_Parameter halfway_Outcome
  complete_Parameter : Type
  complete_Outcome : Type
  [complete_space : MeasurableSpace complete_Outcome]
  complete : StatClaim.Interface.TwoArmModel complete_Parameter complete_Outcome
  interim_test : StatClaim.Interface.TestInterface halfway_Outcome
  interim_slack : ℝ
  final_test : StatClaim.Interface.TestInterface complete_Outcome
  final_slack : ℝ
attribute [instance] Instance.halfway_space
attribute [instance] Instance.complete_space

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.halfway.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.halfway.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.complete.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.complete.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

-- Contract facts the Python compiler checks, decided by Lean.

theorem interim_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.t_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.t_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.t_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.t_test_one_sided.minPerArm ≤ 100 ∧
    StatClaim.Generated.Methods.t_test_one_sided.minPerArm ≤ 100 ∧
    StatClaim.Generated.Methods.t_test_one_sided.minTotal ≤ 100 + 100 ∧
    StatClaim.Generated.Methods.t_test_one_sided.nullValue = none :=
  by decide

theorem interim_values :
    (0 : ℚ) < ((3 : ℚ) / 2000) ∧
    ((3 : ℚ) / 2000) < 1 :=
  by norm_num

theorem final_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.t_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.t_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.t_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.t_test_one_sided.minPerArm ≤ 200 ∧
    StatClaim.Generated.Methods.t_test_one_sided.minPerArm ≤ 200 ∧
    StatClaim.Generated.Methods.t_test_one_sided.minTotal ≤ 200 + 200 ∧
    StatClaim.Generated.Methods.t_test_one_sided.nullValue = none :=
  by decide

theorem final_values :
    (0 : ℚ) < ((47 : ℚ) / 2000) ∧
    ((47 : ℚ) / 2000) < 1 :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  cited_interim_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.halfway.law (null i)
    i.interim_test ((3 : ℚ) / 2000) i.interim_slack
  cited_final_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test_one_sided.scope i.complete.law (null_1 i)
    i.final_test ((47 : ℚ) / 2000) i.final_slack

theorem error_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.halfway_Parameter i.halfway_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.complete_Parameter i.complete_Outcome),
      v₀.Marginal σ i.halfway.law →
      v₁.Marginal σ i.complete.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k) := by
  intro Θ Ω _ σ v₀ v₁ m₀ m₁
  have o₀ : ∀ parameter, (null i) parameter → (i.halfway.law parameter).real i.interim_test.reject ≤ ((↑((3 : ℚ) / 2000) : ℝ) + i.interim_slack) :=
    premises.cited_interim_level.2
  have b₀ := v₀.bound m₀ i.interim_test.measurable o₀
  have s₀ : 0 ≤ i.interim_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_interim_level.1
  have o₁ : ∀ parameter, (null_1 i) parameter → (i.complete.law parameter).real i.final_test.reject ≤ ((↑((47 : ℚ) / 2000) : ℝ) + i.final_slack) :=
    premises.cited_final_level.2
  have b₁ := v₁.bound m₁ i.final_test.measurable o₁
  have s₁ : 0 ≤ i.final_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_final_level.1
  apply StatClaim.Interface.familywise_of_members σ _ _ ![((3 : ℚ) / 2000), ((47 : ℚ) / 2000)]
  all_goals statclaim

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.halfway_Parameter i.halfway_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.complete_Parameter i.complete_Outcome),
      v₀.Marginal σ i.halfway.law →
      v₁.Marginal σ i.complete.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.interim_test.reject,
        v₁.outcome ⁻¹' i.final_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.interim_slack, i.final_slack] k)

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  halfway_Parameter := Unit
  halfway_Outcome := Unit
  halfway := StatClaim.Interface.TwoArmModel.trivial
  complete_Parameter := Unit
  complete_Outcome := Unit
  complete := StatClaim.Interface.TwoArmModel.trivial
  interim_test := StatClaim.Interface.TestInterface.neverRejects _
  interim_slack := 0
  final_test := StatClaim.Interface.TestInterface.neverRejects _
  final_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => error_claim i premises
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("error_claim", ``error_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES replication/comparison/sequential.stat {short}: {String.intercalate "," used}"
