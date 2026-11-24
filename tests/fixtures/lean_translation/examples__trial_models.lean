set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  measured_Parameter : Type
  measured_Outcome : Type
  [measured_space : MeasurableSpace measured_Outcome]
  measured : StatClaim.Interface.TwoArmModel measured_Parameter measured_Outcome
  lung_function_test : StatClaim.Interface.TestInterface measured_Outcome
  lung_function_slack : ℝ
  response_test : StatClaim.Interface.TestInterface StatClaim.Modules.TwoArmBinomial.Counts
  response_slack : ℝ
attribute [instance] Instance.measured_space

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨300, 300, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.measured.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.measured.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_1_compatible :
    StatClaim.Core.Compatibility design_1 :=
  StatClaim.Core.Compatibility.fixed _

def null_1 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

-- Contract facts the Python compiler checks, decided by Lean.

theorem lung_function_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 300 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 300 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 300 + 300 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem lung_function_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem response_contract :
    StatClaim.Generated.NullKey.proportion_difference_at_most ∈ StatClaim.Generated.Methods.logistic_regression_one_sided.nulls ∧
    StatClaim.Generated.NullKey.proportion_difference_at_most.outcome = StatClaim.Generated.Methods.logistic_regression_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.binary = StatClaim.Generated.Methods.logistic_regression_one_sided.outcome ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.minPerArm ≤ 300 ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.minPerArm ≤ 300 ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.minTotal ≤ 300 + 300 :=
  by decide

theorem response_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.nullValue = some (0 : ℚ) :=
  by norm_num [StatClaim.Generated.Methods.logistic_regression_one_sided]

theorem sequence_levels :
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  cited_lung_function_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.measured.law (null i)
    i.lung_function_test ((1 : ℚ) / 40) i.lung_function_slack
  cited_response_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_regression_one_sided.scope responders.law null_1
    i.response_test ((1 : ℚ) / 40) i.response_slack

theorem overall_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.measured_Parameter i.measured_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ i.measured.law →
      v₁.Marginal σ responders.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => null_1 (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.lung_function_test.reject,
        v₁.outcome ⁻¹' i.response_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.lung_function_slack, i.response_slack] k) := by
  intro Θ Ω _ σ v₀ v₁ m₀ m₁
  have o₀ : ∀ parameter, (null i) parameter → (i.measured.law parameter).real i.lung_function_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.lung_function_slack) :=
    premises.cited_lung_function_level.2
  have b₀ := v₀.bound m₀ i.lung_function_test.measurable o₀
  have s₀ : 0 ≤ i.lung_function_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_lung_function_level.1
  have o₁ : ∀ parameter, null_1 parameter → (responders.law parameter).real i.response_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.response_slack) :=
    premises.cited_response_level.2
  have b₁ := v₁.bound m₁ i.response_test.measurable o₁
  have s₁ : 0 ≤ i.response_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_response_level.1
  have c₀ : StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => null_1 (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.lung_function_test.reject,
        v₁.outcome ⁻¹' i.response_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.lung_function_slack, i.response_slack] k) := by
    apply StatClaim.Interface.sequence_of_members σ _ _ ((1 : ℚ) / 40)
    all_goals statclaim
  exact c₀

theorem first_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.lung_function_test ((↑((1 : ℚ) / 40) : ℝ) + i.lung_function_slack) :=
  StatClaim.Interface.typeI_of_premise (design_compatible i) premises.cited_lung_function_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.measured_Parameter i.measured_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts),
      v₀.Marginal σ i.measured.law →
      v₁.Marginal σ responders.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => null_1 (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' i.lung_function_test.reject,
        v₁.outcome ⁻¹' i.response_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.lung_function_slack, i.response_slack] k)) ∧
  (StatClaim.Interface.typeIClaim (design_compatible i) (null i) i.lung_function_test ((↑((1 : ℚ) / 40) : ℝ) + i.lung_function_slack))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  measured_Parameter := Unit
  measured_Outcome := Unit
  measured := StatClaim.Interface.TwoArmModel.trivial
  lung_function_test := StatClaim.Interface.TestInterface.neverRejects _
  lung_function_slack := 0
  response_test := StatClaim.Interface.TestInterface.neverRejects _
  response_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨overall_claim i premises, first_claim i premises⟩
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("overall_claim", ``overall_claim), ("first_claim", ``first_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/trial_models.stat {short}: {String.intercalate "," used}"
