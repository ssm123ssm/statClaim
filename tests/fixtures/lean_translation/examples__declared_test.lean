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
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem function_contract :
    StatClaim.Generated.NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls ∧
    StatClaim.Generated.NullKey.equal_means.outcome = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.Methods.t_test.unit = .participant ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 200 ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 200 ∧
    StatClaim.Generated.Methods.t_test.minTotal ≤ 200 + 200 ∧
    StatClaim.Generated.Methods.t_test.nullValue = none :=
  by decide

theorem function_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  declared_pain_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.largeSample i.study.law (null i)
    i.pain_test ((1 : ℚ) / 40) i.pain_slack
  cited_function_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.study.law (null i)
    i.function_test ((1 : ℚ) / 40) i.function_slack

theorem family_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome),
      v₀.Marginal σ i.study.law →
      v₁.Marginal σ i.study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.pain_test.reject,
        v₁.outcome ⁻¹' i.function_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.pain_slack, i.function_slack] k) := by
  intro Θ Ω _ σ v₀ v₁ m₀ m₁
  have o₀ : ∀ parameter, (null i) parameter → (i.study.law parameter).real i.pain_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack) :=
    premises.declared_pain_level.2
  have b₀ := v₀.bound m₀ i.pain_test.measurable o₀
  have s₀ : 0 ≤ i.pain_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.declared_pain_level.1
  have o₁ : ∀ parameter, (null i) parameter → (i.study.law parameter).real i.function_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.function_slack) :=
    premises.cited_function_level.2
  have b₁ := v₁.bound m₁ i.function_test.measurable o₁
  have s₁ : 0 ≤ i.function_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_function_level.1
  have c₀ : StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.pain_test.reject,
        v₁.outcome ⁻¹' i.function_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.pain_slack, i.function_slack] k) := by
    apply StatClaim.Interface.familywise_of_members σ _ _ ![((1 : ℚ) / 40), ((1 : ℚ) / 40)]
    all_goals statclaim
  exact c₀

theorem alone_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.pain_test ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack) :=
  StatClaim.Interface.typeI_of_premise (plan_compatible i) premises.declared_pain_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.study_Parameter i.study_Outcome),
      v₀.Marginal σ i.study.law →
      v₁.Marginal σ i.study.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.pain_test.reject,
        v₁.outcome ⁻¹' i.function_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![i.pain_slack, i.function_slack] k)) ∧
  (StatClaim.Interface.typeIClaim (plan_compatible i) (null i) i.pain_test ((↑((1 : ℚ) / 40) : ℝ) + i.pain_slack))

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
  implies := fun i premises => ⟨family_claim i premises, alone_claim i premises⟩
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("family_claim", ``family_claim), ("alone_claim", ``alone_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/declared_test.stat {short}: {String.intercalate "," used}"
