set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  scores_Parameter : Type
  scores_Outcome : Type
  [scores_space : MeasurableSpace scores_Outcome]
  scores : StatClaim.Interface.TwoArmModel scores_Parameter scores_Outcome
  symptoms_test : StatClaim.Interface.TestInterface scores_Outcome
  symptoms_slack : ℝ
attribute [instance] Instance.scores_space

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨120, 120, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def response_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def response :=
  StatClaim.Modules.Fisher.analysis responders_sizes design response_level

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.scores.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.scores.null StatClaim.Generated.NullKey.equal_means.shape (0 : ℚ)

-- Contract facts the Python compiler checks, decided by Lean.

theorem response_null :
    ∀ parameter, null parameter ↔ response.hypothesis parameter :=
  fun parameter => Iff.rfl

theorem response_contract :
    (StatClaim.Modules.Fisher.module responders_sizes response_level).Requires
      design :=
  ⟨design_compatible⟩

theorem symptoms_contract :
    StatClaim.Generated.NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls ∧
    StatClaim.Generated.NullKey.equal_means.outcome = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.t_test.outcome ∧
    StatClaim.Generated.Methods.t_test.unit = .participant ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 120 ∧
    StatClaim.Generated.Methods.t_test.minPerArm ≤ 120 ∧
    StatClaim.Generated.Methods.t_test.minTotal ≤ 120 + 120 ∧
    StatClaim.Generated.Methods.t_test.nullValue = none :=
  by decide

theorem symptoms_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_1 i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack

theorem family_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome),
      v₀.Marginal σ responders.law →
      v₁.Marginal σ i.scores.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k) := by
  intro Θ Ω _ σ v₀ v₁ m₀ m₁
  have o₀ : ∀ parameter, response.hypothesis parameter → (responders.law parameter).real response.procedure.rejectionEvent ≤ (↑((1 : ℚ) / 40) : ℝ) :=
    StatClaim.Interface.model_bound design_compatible
      (StatClaim.Modules.Fisher.typeI_statement responders_sizes design design_compatible response_level)
  have b₀ := v₀.bound m₀ response.procedure.rejection_measurable o₀
  have o₁ : ∀ parameter, (null_1 i) parameter → (i.scores.law parameter).real i.symptoms_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.symptoms_slack) :=
    premises.cited_symptoms_level.2
  have b₁ := v₁.bound m₁ i.symptoms_test.measurable o₁
  have s₁ : 0 ≤ i.symptoms_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_symptoms_level.1
  apply StatClaim.Interface.familywise_of_members σ _ _ ![((1 : ℚ) / 40), ((1 : ℚ) / 40)]
  all_goals statclaim

theorem primary_claim (i : Instance) (premises : Premises i) :
    (response.typeIClaim design_compatible
      (response_level.value : ℝ)).statement :=
  StatClaim.Modules.Fisher.typeI_statement responders_sizes design design_compatible response_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₁ : StatClaim.Interface.MemberView Θ Ω i.scores_Parameter i.scores_Outcome),
      v₀.Marginal σ responders.law →
      v₁.Marginal σ i.scores.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k)) ∧
  ((response.typeIClaim design_compatible
      (response_level.value : ℝ)).statement)

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  scores_Parameter := Unit
  scores_Outcome := Unit
  scores := StatClaim.Interface.TwoArmModel.trivial
  symptoms_test := StatClaim.Interface.TestInterface.neverRejects _
  symptoms_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨family_claim i premises, primary_claim i premises⟩
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("family_claim", ``family_claim), ("primary_claim", ``primary_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/mixed_endpoints.stat {short}: {String.intercalate "," used}"
