set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  per_protocol_Parameter : Type
  per_protocol_Outcome : Type
  [per_protocol_space : MeasurableSpace per_protocol_Outcome]
  per_protocol : StatClaim.Interface.TwoArmModel per_protocol_Parameter per_protocol_Outcome
  everyone_Parameter : Type
  everyone_Outcome : Type
  [everyone_space : MeasurableSpace everyone_Outcome]
  everyone : StatClaim.Interface.TwoArmModel everyone_Parameter everyone_Outcome
  trough_not_worse_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  trough_not_worse_slack : ℝ
  peak_not_worse_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  peak_not_worse_slack : ℝ
  peak_better_test : StatClaim.Interface.TestInterface everyone_Outcome
  peak_better_slack : ℝ
  graph_procedure : ∀ (Θ Ω : Type) [MeasurableSpace Ω], StatClaim.Interface.JointStudy Θ Ω → StatClaim.Interface.MemberView Θ Ω per_protocol_Parameter per_protocol_Outcome → StatClaim.Interface.MemberView Θ Ω per_protocol_Parameter per_protocol_Outcome → StatClaim.Interface.MemberView Θ Ω everyone_Parameter everyone_Outcome → Fin 3 → Set Ω
  graph_slack : ℝ
  capacity_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  capacity_slack : ℝ
  onset_member_Parameter : Type
  onset_member_Outcome : Type
  [onset_member_space : MeasurableSpace onset_member_Outcome]
  onset_member : StatClaim.Interface.TwoArmModel onset_member_Parameter onset_member_Outcome
  onset_member_hypothesis : onset_member_Parameter → Prop
  onset_member_test : StatClaim.Interface.TestInterface onset_member_Outcome
  onset_member_slack : ℝ
attribute [instance] Instance.per_protocol_space
attribute [instance] Instance.everyone_space
attribute [instance] Instance.onset_member_space

def responders_sizes : StatClaim.FixedSampleDesign :=
  ⟨500, 500, by decide, by decide⟩

noncomputable def responders := StatClaim.Modules.TwoArmBinomial.model responders_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.per_protocol.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.everyone.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.everyone.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

def onset_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def design_2 :=
  StatClaim.Core.StudyDesign.fixed responders

noncomputable def design_2_compatible :
    StatClaim.Core.Compatibility design_2 :=
  StatClaim.Core.Compatibility.fixed _

def null_2 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

noncomputable def onset :=
  StatClaim.Modules.FisherOneSided.analysis responders_sizes onset_level

def onset_member_null (i : Instance) :=
  i.onset_member_hypothesis

-- Contract facts the Python compiler checks, decided by Lean.

theorem trough_not_worse_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.welch_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.welch_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.nullValue = none :=
  by decide

theorem trough_not_worse_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem peak_not_worse_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.welch_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.welch_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.nullValue = none :=
  by decide

theorem peak_not_worse_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem peak_better_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.welch_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.welch_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 500 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 500 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minTotal ≤ 500 + 500 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.nullValue = none :=
  by decide

theorem peak_better_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem graph_weights :
    (0 : ℚ) ≤ ((1 : ℚ) / 2) ∧
    (0 : ℚ) ≤ ((1 : ℚ) / 2) ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    ((1 : ℚ) / 2) + ((1 : ℚ) / 2) + (0 : ℚ) ≤ 1 :=
  by norm_num

theorem graph_transitions :
    (0 : ℚ) = 0 ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    (0 : ℚ) ≤ (1 : ℚ) ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    (0 : ℚ) + (1 : ℚ) + (0 : ℚ) ≤ 1 ∧
    (0 : ℚ) = 0 ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    (0 : ℚ) ≤ (1 : ℚ) ∧
    (0 : ℚ) + (0 : ℚ) + (1 : ℚ) ≤ 1 ∧
    (0 : ℚ) = 0 ∧
    (0 : ℚ) ≤ (1 : ℚ) ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    (0 : ℚ) ≤ (0 : ℚ) ∧
    (1 : ℚ) + (0 : ℚ) + (0 : ℚ) ≤ 1 :=
  by norm_num

theorem graph_levels :
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) :=
  by norm_num

theorem capacity_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.welch_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.welch_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.welch_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.welch_test_one_sided.nullValue = none :=
  by decide

theorem capacity_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem onset_null :
    ∀ parameter, null_2 parameter ↔ onset.hypothesis parameter :=
  fun parameter => Iff.rfl

theorem sequence_levels :
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  cited_trough_not_worse_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.trough_not_worse_test ((1 : ℚ) / 40) i.trough_not_worse_slack
  cited_peak_not_worse_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.peak_not_worse_test ((1 : ℚ) / 40) i.peak_not_worse_slack
  cited_peak_better_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.everyone.law (null_1 i)
    i.peak_better_test ((1 : ℚ) / 40) i.peak_better_slack
  cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)
  cited_capacity_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.welch_test_one_sided.scope i.per_protocol.law (null i)
    i.capacity_test ((1 : ℚ) / 40) i.capacity_slack
  member_onset_member_level : StatClaim.Interface.LevelPremise StatClaim.Interface.Scope.finiteSample i.onset_member.law (onset_member_null i)
    i.onset_member_test ((1 : ℚ) / 40) i.onset_member_slack

theorem primary_error_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack) := by
  intro Θ Ω _ σ v₀ v₁ v₂ m₀ m₁ m₂
  have c₀ : StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack) :=
    premises.cited_graph_rule.2 Θ Ω σ v₀ v₁ v₂ m₀ m₁ m₂
  exact c₀

theorem overall_error_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω i.onset_member_Parameter i.onset_member_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ i.onset_member.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => (onset_member_null i) (v₄.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.capacity_test.reject,
        v₄.outcome ⁻¹' i.onset_member_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.capacity_slack, i.onset_member_slack] k) := by
  intro Θ Ω _ σ v₀ v₁ v₂ v₃ v₄ m₀ m₁ m₂ m₃ m₄
  have o₃ : ∀ parameter, (null i) parameter → (i.per_protocol.law parameter).real i.capacity_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.capacity_slack) :=
    premises.cited_capacity_level.2
  have b₃ := v₃.bound m₃ i.capacity_test.measurable o₃
  have s₃ : 0 ≤ i.capacity_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_capacity_level.1
  have o₄ : ∀ parameter, (onset_member_null i) parameter → (i.onset_member.law parameter).real i.onset_member_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.onset_member_slack) :=
    premises.member_onset_member_level.2
  have b₄ := v₄.bound m₄ i.onset_member_test.measurable o₄
  have s₄ : 0 ≤ i.onset_member_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.member_onset_member_level.1
  have g₀ : 0 ≤ i.graph_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_graph_rule.1
  have c₁ : StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack) :=
    premises.cited_graph_rule.2 Θ Ω σ v₀ v₁ v₂ m₀ m₁ m₂
  have n₂ := StatClaim.Interface.family_member σ c₁
  have c₀ : StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => (onset_member_null i) (v₄.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.capacity_test.reject,
        v₄.outcome ⁻¹' i.onset_member_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.capacity_slack, i.onset_member_slack] k) := by
    apply StatClaim.Interface.sequence_of_members σ _ _ ((1 : ℚ) / 40)
    all_goals statclaim
  exact c₀

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.everyone_Parameter i.everyone_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω i.onset_member_Parameter i.onset_member_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.everyone.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ i.onset_member.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => (onset_member_null i) (v₄.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.capacity_test.reject,
        v₄.outcome ⁻¹' i.onset_member_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.capacity_slack, i.onset_member_slack] k))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  per_protocol_Parameter := Unit
  per_protocol_Outcome := Unit
  per_protocol := StatClaim.Interface.TwoArmModel.trivial
  everyone_Parameter := Unit
  everyone_Outcome := Unit
  everyone := StatClaim.Interface.TwoArmModel.trivial
  trough_not_worse_test := StatClaim.Interface.TestInterface.neverRejects _
  trough_not_worse_slack := 0
  peak_not_worse_test := StatClaim.Interface.TestInterface.neverRejects _
  peak_not_worse_slack := 0
  peak_better_test := StatClaim.Interface.TestInterface.neverRejects _
  peak_better_slack := 0
  graph_procedure := fun _ _ _ _ _ _ _ _ => ∅
  graph_slack := 0
  capacity_test := StatClaim.Interface.TestInterface.neverRejects _
  capacity_slack := 0
  onset_member_Parameter := Unit
  onset_member_Outcome := Unit
  onset_member := StatClaim.Interface.TwoArmModel.trivial
  onset_member_hypothesis := fun _ => True
  onset_member_test := StatClaim.Interface.TestInterface.neverRejects _
  onset_member_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨primary_error_claim i premises, overall_error_claim i premises⟩
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), ⟨StatClaim.Interface.Scope.permits_zero _, by
      intro Θ Ω _ σ v₀ v₁ v₂ m₀ m₁ m₂
      exact StatClaim.Interface.familywise_of_nothing σ.law _ (by norm_num [witness])⟩, StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("primary_error_claim", ``primary_error_claim), ("overall_error_claim", ``overall_error_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/recycling.stat {short}: {String.intercalate "," used}"
