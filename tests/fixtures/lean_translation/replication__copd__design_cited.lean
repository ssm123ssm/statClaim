set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  per_protocol_Parameter : Type
  per_protocol_Outcome : Type
  [per_protocol_space : MeasurableSpace per_protocol_Outcome]
  per_protocol : StatClaim.Interface.TwoArmModel per_protocol_Parameter per_protocol_Outcome
  full_set_Parameter : Type
  full_set_Outcome : Type
  [full_set_space : MeasurableSpace full_set_Outcome]
  full_set : StatClaim.Interface.TwoArmModel full_set_Parameter full_set_Outcome
  trough_fev1_ni_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  trough_fev1_ni_slack : ℝ
  peak_fev1_ni_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  peak_fev1_ni_slack : ℝ
  peak_fev1_sup_test : StatClaim.Interface.TestInterface full_set_Outcome
  peak_fev1_sup_slack : ℝ
  graph_procedure : ∀ (Θ Ω : Type) [MeasurableSpace Ω], StatClaim.Interface.JointStudy Θ Ω → StatClaim.Interface.MemberView Θ Ω per_protocol_Parameter per_protocol_Outcome → StatClaim.Interface.MemberView Θ Ω per_protocol_Parameter per_protocol_Outcome → StatClaim.Interface.MemberView Θ Ω full_set_Parameter full_set_Outcome → Fin 3 → Set Ω
  graph_slack : ℝ
  inspiratory_capacity_ni_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  inspiratory_capacity_ni_slack : ℝ
  onset_of_action_sup_test : StatClaim.Interface.TestInterface StatClaim.Modules.TwoArmBinomial.Counts
  onset_of_action_sup_slack : ℝ
  tdi_ni_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  tdi_ni_slack : ℝ
  emsci_ni_test : StatClaim.Interface.TestInterface per_protocol_Outcome
  emsci_ni_slack : ℝ
attribute [instance] Instance.per_protocol_space
attribute [instance] Instance.full_set_space

def full_set_binary_sizes : StatClaim.FixedSampleDesign :=
  ⟨500, 500, by decide, by decide⟩

noncomputable def full_set_binary := StatClaim.Modules.TwoArmBinomial.model full_set_binary_sizes

noncomputable def design (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.per_protocol.toModel

noncomputable def design_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design i) :=
  StatClaim.Core.Compatibility.fixed _

def null (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-50 : ℚ)

noncomputable def design_1 (i : Instance) :=
  StatClaim.Core.StudyDesign.fixed i.full_set.toModel

noncomputable def design_1_compatible (i : Instance) :
    StatClaim.Core.Compatibility (design_1 i) :=
  StatClaim.Core.Compatibility.fixed _

def null_1 (i : Instance) :=
  i.full_set.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (0 : ℚ)

noncomputable def design_2 :=
  StatClaim.Core.StudyDesign.fixed full_set_binary

noncomputable def design_2_compatible :
    StatClaim.Core.Compatibility design_2 :=
  StatClaim.Core.Compatibility.fixed _

def null_2 : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

def null_3 (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape (-1 : ℚ)

def null_4 (i : Instance) :=
  i.per_protocol.null StatClaim.Generated.NullKey.mean_difference_at_most.shape ((-1 : ℚ) / 10)

-- Contract facts the Python compiler checks, decided by Lean.

theorem trough_fev1_ni_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem trough_fev1_ni_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem peak_fev1_ni_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem peak_fev1_ni_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem peak_fev1_sup_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 500 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 500 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 500 + 500 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem peak_fev1_sup_values :
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

theorem inspiratory_capacity_ni_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem inspiratory_capacity_ni_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem onset_of_action_sup_contract :
    StatClaim.Generated.NullKey.proportion_difference_at_most ∈ StatClaim.Generated.Methods.logistic_regression_one_sided.nulls ∧
    StatClaim.Generated.NullKey.proportion_difference_at_most.outcome = StatClaim.Generated.Methods.logistic_regression_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.binary = StatClaim.Generated.Methods.logistic_regression_one_sided.outcome ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.minPerArm ≤ 500 ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.minPerArm ≤ 500 ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.minTotal ≤ 500 + 500 :=
  by decide

theorem onset_of_action_sup_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 ∧
    StatClaim.Generated.Methods.logistic_regression_one_sided.nullValue = some (0 : ℚ) :=
  by norm_num [StatClaim.Generated.Methods.logistic_regression_one_sided]

theorem tdi_ni_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem tdi_ni_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem emsci_ni_contract :
    StatClaim.Generated.NullKey.mean_difference_at_most ∈ StatClaim.Generated.Methods.mmrm_test_one_sided.nulls ∧
    StatClaim.Generated.NullKey.mean_difference_at_most.outcome = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.OutcomeKind.continuous = StatClaim.Generated.Methods.mmrm_test_one_sided.outcome ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.unit = .participant ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minPerArm ≤ 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.minTotal ≤ 440 + 440 ∧
    StatClaim.Generated.Methods.mmrm_test_one_sided.nullValue = none :=
  by decide

theorem emsci_ni_values :
    (0 : ℚ) < ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) < 1 :=
  by norm_num

theorem sequence_levels :
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) ∧
    ((1 : ℚ) / 40) = ((1 : ℚ) / 40) :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where
  cited_trough_fev1_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.trough_fev1_ni_test ((1 : ℚ) / 40) i.trough_fev1_ni_slack
  cited_peak_fev1_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.peak_fev1_ni_test ((1 : ℚ) / 40) i.peak_fev1_ni_slack
  cited_peak_fev1_sup_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.full_set.law (null_1 i)
    i.peak_fev1_sup_test ((1 : ℚ) / 40) i.peak_fev1_sup_slack
  cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)
  cited_inspiratory_capacity_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.inspiratory_capacity_ni_test ((1 : ℚ) / 40) i.inspiratory_capacity_ni_slack
  cited_onset_of_action_sup_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_regression_one_sided.scope full_set_binary.law null_2
    i.onset_of_action_sup_test ((1 : ℚ) / 40) i.onset_of_action_sup_slack
  cited_tdi_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null_3 i)
    i.tdi_ni_test ((1 : ℚ) / 40) i.tdi_ni_slack
  cited_emsci_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null_4 i)
    i.emsci_ni_test ((1 : ℚ) / 40) i.emsci_ni_slack

theorem primary_error_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
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

set_option maxHeartbeats 2800000 in
theorem overall_error_claim (i : Instance) (premises : Premises i) :
    ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₅ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₆ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ full_set_binary.law →
      v₅.Marginal σ i.per_protocol.law →
      v₆.Marginal σ i.per_protocol.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => null_2 (v₄.parameter θ),
        fun θ => (null_3 i) (v₅.parameter θ),
        fun θ => (null_4 i) (v₆.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.inspiratory_capacity_ni_test.reject,
        v₄.outcome ⁻¹' i.onset_of_action_sup_test.reject,
        v₅.outcome ⁻¹' i.tdi_ni_test.reject,
        v₆.outcome ⁻¹' i.emsci_ni_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.inspiratory_capacity_ni_slack, i.onset_of_action_sup_slack, i.tdi_ni_slack, i.emsci_ni_slack] k) := by
  intro Θ Ω _ σ v₀ v₁ v₂ v₃ v₄ v₅ v₆ m₀ m₁ m₂ m₃ m₄ m₅ m₆
  have o₃ : ∀ parameter, (null i) parameter → (i.per_protocol.law parameter).real i.inspiratory_capacity_ni_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.inspiratory_capacity_ni_slack) :=
    premises.cited_inspiratory_capacity_ni_level.2
  have b₃ := v₃.bound m₃ i.inspiratory_capacity_ni_test.measurable o₃
  have s₃ : 0 ≤ i.inspiratory_capacity_ni_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_inspiratory_capacity_ni_level.1
  have o₄ : ∀ parameter, null_2 parameter → (full_set_binary.law parameter).real i.onset_of_action_sup_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.onset_of_action_sup_slack) :=
    premises.cited_onset_of_action_sup_level.2
  have b₄ := v₄.bound m₄ i.onset_of_action_sup_test.measurable o₄
  have s₄ : 0 ≤ i.onset_of_action_sup_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_onset_of_action_sup_level.1
  have o₅ : ∀ parameter, (null_3 i) parameter → (i.per_protocol.law parameter).real i.tdi_ni_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.tdi_ni_slack) :=
    premises.cited_tdi_ni_level.2
  have b₅ := v₅.bound m₅ i.tdi_ni_test.measurable o₅
  have s₅ : 0 ≤ i.tdi_ni_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_tdi_ni_level.1
  have o₆ : ∀ parameter, (null_4 i) parameter → (i.per_protocol.law parameter).real i.emsci_ni_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.emsci_ni_slack) :=
    premises.cited_emsci_ni_level.2
  have b₆ := v₆.bound m₆ i.emsci_ni_test.measurable o₆
  have s₆ : 0 ≤ i.emsci_ni_slack :=
    StatClaim.Interface.Scope.permits_nonnegative premises.cited_emsci_ni_level.1
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
        fun θ => null_2 (v₄.parameter θ),
        fun θ => (null_3 i) (v₅.parameter θ),
        fun θ => (null_4 i) (v₆.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.inspiratory_capacity_ni_test.reject,
        v₄.outcome ⁻¹' i.onset_of_action_sup_test.reject,
        v₅.outcome ⁻¹' i.tdi_ni_test.reject,
        v₆.outcome ⁻¹' i.emsci_ni_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.inspiratory_capacity_ni_slack, i.onset_of_action_sup_slack, i.tdi_ni_slack, i.emsci_ni_slack] k) := by
    apply StatClaim.Interface.sequence_of_members σ _ _ ((1 : ℚ) / 40)
    all_goals statclaim
  exact c₀

theorem onset_error_claim (i : Instance) (premises : Premises i) :
    StatClaim.Interface.typeIClaim design_2_compatible null_2 i.onset_of_action_sup_test ((↑((1 : ℚ) / 40) : ℝ) + i.onset_of_action_sup_slack) :=
  StatClaim.Interface.typeI_of_premise design_2_compatible premises.cited_onset_of_action_sup_level

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) ∧
  (∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : StatClaim.Interface.JointStudy Θ Ω)
      (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome) (v₃ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₄ : StatClaim.Interface.MemberView Θ Ω StatClaim.Modules.TwoArmBinomial.Parameters StatClaim.Modules.TwoArmBinomial.Counts) (v₅ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome) (v₆ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome),
      v₀.Marginal σ i.per_protocol.law →
      v₁.Marginal σ i.per_protocol.law →
      v₂.Marginal σ i.full_set.law →
      v₃.Marginal σ i.per_protocol.law →
      v₄.Marginal σ full_set_binary.law →
      v₅.Marginal σ i.per_protocol.law →
      v₆.Marginal σ i.per_protocol.law →
      StatClaim.Interface.sequenceClaim σ.law
        ![fun θ => ∃ k, ![fun θ => (null i) (v₀.parameter θ), fun θ => (null i) (v₁.parameter θ), fun θ => (null_1 i) (v₂.parameter θ)] k θ,
        fun θ => (null i) (v₃.parameter θ),
        fun θ => null_2 (v₄.parameter θ),
        fun θ => (null_3 i) (v₅.parameter θ),
        fun θ => (null_4 i) (v₆.parameter θ)]
        ![(⋂ k, (i.graph_procedure Θ Ω σ v₀ v₁ v₂) k),
        v₃.outcome ⁻¹' i.inspiratory_capacity_ni_test.reject,
        v₄.outcome ⁻¹' i.onset_of_action_sup_test.reject,
        v₅.outcome ⁻¹' i.tdi_ni_test.reject,
        v₆.outcome ⁻¹' i.emsci_ni_test.reject]
        ((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.graph_slack, i.inspiratory_capacity_ni_slack, i.onset_of_action_sup_slack, i.tdi_ni_slack, i.emsci_ni_slack] k)) ∧
  (StatClaim.Interface.typeIClaim design_2_compatible null_2 i.onset_of_action_sup_test ((↑((1 : ℚ) / 40) : ℝ) + i.onset_of_action_sup_slack))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  per_protocol_Parameter := Unit
  per_protocol_Outcome := Unit
  per_protocol := StatClaim.Interface.TwoArmModel.trivial
  full_set_Parameter := Unit
  full_set_Outcome := Unit
  full_set := StatClaim.Interface.TwoArmModel.trivial
  trough_fev1_ni_test := StatClaim.Interface.TestInterface.neverRejects _
  trough_fev1_ni_slack := 0
  peak_fev1_ni_test := StatClaim.Interface.TestInterface.neverRejects _
  peak_fev1_ni_slack := 0
  peak_fev1_sup_test := StatClaim.Interface.TestInterface.neverRejects _
  peak_fev1_sup_slack := 0
  graph_procedure := fun _ _ _ _ _ _ _ _ => ∅
  graph_slack := 0
  inspiratory_capacity_ni_test := StatClaim.Interface.TestInterface.neverRejects _
  inspiratory_capacity_ni_slack := 0
  onset_of_action_sup_test := StatClaim.Interface.TestInterface.neverRejects _
  onset_of_action_sup_slack := 0
  tdi_ni_test := StatClaim.Interface.TestInterface.neverRejects _
  tdi_ni_slack := 0
  emsci_ni_test := StatClaim.Interface.TestInterface.neverRejects _
  emsci_ni_slack := 0

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨primary_error_claim i premises, overall_error_claim i premises, onset_error_claim i premises⟩
  satisfiable := ⟨witness, ⟨StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), ⟨StatClaim.Interface.Scope.permits_zero _, by
      intro Θ Ω _ σ v₀ v₁ v₂ m₀ m₁ m₂
      exact StatClaim.Interface.familywise_of_nothing σ.law _ (by norm_num [witness])⟩, StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num), StatClaim.Interface.neverRejects_meets_level _ _ _ _ (by norm_num)⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("primary_error_claim", ``primary_error_claim), ("overall_error_claim", ``overall_error_claim), ("onset_error_claim", ``onset_error_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES replication/copd/design_cited.stat {short}: {String.intercalate "," used}"
