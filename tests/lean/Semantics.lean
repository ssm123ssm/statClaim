import StatClaim

set_option linter.unusedVariables false

/-!
Two programs stated by the semantics of `StatClaim.Semantics`
(docs/proposals/lean-semantics.md): `examples/mixed_endpoints.stat` and
`replication/copd/design_cited.stat`, as data written by `lean_translation/data.py`.

Each `Old` namespace is the pinned translation of today's translator, with its
abstract parts read off the semantics' instance and each claim taking only the
premises it uses. The semantics' claims are proved with those proofs, and Lean accepts
`Iff.rfl` between the two statements.
-/

namespace MixedEndpoints.Old

abbrev Instance := StatClaim.Semantics.Instance
def Instance.scores_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).Parameter
def Instance.scores_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace i.scores_Outcome := (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).space
def Instance.scores (i : Instance) : StatClaim.Interface.TwoArmModel i.scores_Parameter i.scores_Outcome :=
  (i.laws { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }).model
def Instance.symptoms_test (i : Instance) : StatClaim.Interface.TestInterface i.scores_Outcome :=
  i.test "symptoms" { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }
def Instance.symptoms_slack (i : Instance) : ℝ := i.slack "symptoms"

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


theorem family_claim' (i : Instance)
    (cited_symptoms_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.t_test.scope i.scores.law (null_1 i)
    i.symptoms_test ((1 : ℚ) / 40) i.symptoms_slack) :
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
    cited_symptoms_level.2
  have b₁ := v₁.bound m₁ i.symptoms_test.measurable o₁
  have s₁ : 0 ≤ i.symptoms_slack :=
    StatClaim.Interface.Scope.permits_nonnegative cited_symptoms_level.1
  have c₀ : StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => response.hypothesis (v₀.parameter θ),
        fun θ => (null_1 i) (v₁.parameter θ)]
        ![v₀.outcome ⁻¹' response.procedure.rejectionEvent,
        v₁.outcome ⁻¹' i.symptoms_test.reject]
        ((↑((1 : ℚ) / 20) : ℝ) + ∑ k, ![0, i.symptoms_slack] k) := by
    apply StatClaim.Interface.familywise_of_members σ _ _ ![((1 : ℚ) / 40), ((1 : ℚ) / 40)]
    all_goals statclaim
  exact c₀

theorem primary_claim' (i : Instance) :
    (response.typeIClaim design_compatible
      (response_level.value : ℝ)).statement :=
  StatClaim.Modules.Fisher.typeI_statement responders_sizes design design_compatible response_level

end MixedEndpoints.Old

namespace MixedEndpoints

open StatClaim StatClaim.Semantics

/-- The program as data, as `lean_translation/data.py` writes it. -/
def program : StatClaim.Semantics.Program := ⟨[
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "symptoms" StatClaim.Generated.Methods.t_test
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

theorem contracts : program.Contracts := by decide +kernel

theorem grades : [program.grade 0 [0], program.grade 1 []] = [.conditional, .proved] := by
  decide +kernel

/-- Claims stated by the semantics, proved with today's proofs. -/
theorem claim_0 : program.ClaimFrom 0 [0] := fun i h => Old.family_claim' i h.1

theorem claim_1 : program.ClaimFrom 1 [] := fun i _ => Old.primary_claim' i

/-! The semantics states what today's translation states, definitionally. -/

example (i : Instance) : Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i := Iff.rfl
example (i : Instance) (h : program.Using i [0]) : Old.Premises i := ⟨h.1⟩
example (i : Instance) (h : Old.Premises i) : program.Using i [0] := ⟨h.1, trivial⟩

/-! Lean refuses what breaks a contract or overstates a grade, in data written by
`data.py` from the program with one change. -/

/-- The family's level below its members' sum. -/
def overallocated : StatClaim.Semantics.Program := ⟨[
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "symptoms" StatClaim.Generated.Methods.t_test
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

example : ¬ overallocated.Contracts := by decide +kernel

/-- A null the t-test does not support. -/
def unsupported : StatClaim.Semantics.Program := ⟨[
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "symptoms" StatClaim.Generated.Methods.t_test
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_least, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

example : ¬ unsupported.Contracts := by decide +kernel

/-- Fewer participants than the t-test needs. -/
def tooFew : StatClaim.Semantics.Program := ⟨[
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "symptoms" StatClaim.Generated.Methods.t_test
      { model := { outcome := .continuous, sizes := ⟨1, 1, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨1, 1, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

example : ¬ tooFew.Contracts := by decide +kernel

/-- A null about another model than the design's. -/
def otherModel : StatClaim.Semantics.Program := ⟨[
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "symptoms" StatClaim.Generated.Methods.t_test
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨121, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

example : ¬ otherModel.Contracts := by decide +kernel

/-- A design that stops by a rule depending on the data supplies no law: its claim is
`False`. -/
def adaptive : StatClaim.Semantics.Program := ⟨[
  .familywise (.bonferroni "endpoints"
    [.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "symptoms" StatClaim.Generated.Methods.t_test
      { model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .fixed }
      { key := .equal_means, model := { outcome := .continuous, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩),
  .typeI (.fisher "response"
      { model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ }, stopping := .data_dependent }
      { key := .equal_proportions, model := { outcome := .binary, sizes := ⟨120, 120, by decide, by decide⟩ } }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

example (i : Instance) : ¬ adaptive.claimAt 1 i := id

example : program.grade 0 [0] ≠ .proved := by decide +kernel

/-- The premises can hold together: proved once, for every program. -/
example : program.Using Instance.trivial [0] := Program.satisfiable _ _

end MixedEndpoints

namespace Copd.Old

set_option linter.unusedVariables false

abbrev Instance := StatClaim.Semantics.Instance
def Instance.per_protocol_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Parameter
def Instance.per_protocol_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace i.per_protocol_Outcome := (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).space
def Instance.per_protocol (i : Instance) :
    StatClaim.Interface.TwoArmModel i.per_protocol_Parameter i.per_protocol_Outcome :=
  (i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }).model
def Instance.full_set_Parameter (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Parameter
def Instance.full_set_Outcome (i : Instance) : Type := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).Outcome
instance (i : Instance) : MeasurableSpace i.full_set_Outcome := (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).space
def Instance.full_set (i : Instance) :
    StatClaim.Interface.TwoArmModel i.full_set_Parameter i.full_set_Outcome :=
  (i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }).model
def Instance.trough_fev1_ni_test (i : Instance) : StatClaim.Interface.TestInterface i.per_protocol_Outcome :=
  i.test "trough_fev1_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.trough_fev1_ni_slack (i : Instance) : ℝ := i.slack "trough_fev1_ni"
def Instance.peak_fev1_ni_test (i : Instance) : StatClaim.Interface.TestInterface i.per_protocol_Outcome :=
  i.test "peak_fev1_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.peak_fev1_ni_slack (i : Instance) : ℝ := i.slack "peak_fev1_ni"
def Instance.peak_fev1_sup_test (i : Instance) : StatClaim.Interface.TestInterface i.full_set_Outcome :=
  i.test "peak_fev1_sup" { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.peak_fev1_sup_slack (i : Instance) : ℝ := i.slack "peak_fev1_sup"
def Instance.inspiratory_capacity_ni_test (i : Instance) : StatClaim.Interface.TestInterface i.per_protocol_Outcome :=
  i.test "inspiratory_capacity_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.inspiratory_capacity_ni_slack (i : Instance) : ℝ := i.slack "inspiratory_capacity_ni"
def Instance.tdi_ni_test (i : Instance) : StatClaim.Interface.TestInterface i.per_protocol_Outcome :=
  i.test "tdi_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.tdi_ni_slack (i : Instance) : ℝ := i.slack "tdi_ni"
def Instance.emsci_ni_test (i : Instance) : StatClaim.Interface.TestInterface i.per_protocol_Outcome :=
  i.test "emsci_ni" { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }
def Instance.emsci_ni_slack (i : Instance) : ℝ := i.slack "emsci_ni"
def Instance.onset_of_action_sup_test (i : Instance) :
    StatClaim.Interface.TestInterface StatClaim.Modules.TwoArmBinomial.Counts :=
  i.test "onset_of_action_sup" { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }
def Instance.onset_of_action_sup_slack (i : Instance) : ℝ := i.slack "onset_of_action_sup"
def Instance.graph_procedure (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]
    (σ : StatClaim.Interface.JointStudy Θ Ω)
    (v₀ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome)
    (v₁ : StatClaim.Interface.MemberView Θ Ω i.per_protocol_Parameter i.per_protocol_Outcome)
    (v₂ : StatClaim.Interface.MemberView Θ Ω i.full_set_Parameter i.full_set_Outcome) :
    Fin 3 → Set Ω :=
  i.graph "co_primary"
    [StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ },
      StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ },
      StatClaim.Semantics.Model.view i.laws { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }] 3 Θ Ω σ (v₀, v₁, v₂, PUnit.unit)
def Instance.graph_slack (i : Instance) : ℝ := i.slack "co_primary"

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


theorem primary_error_claim' (i : Instance)
    (cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
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
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack)) :
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
    cited_graph_rule.2 Θ Ω σ v₀ v₁ v₂ m₀ m₁ m₂
  exact c₀

set_option maxHeartbeats 2800000 in
theorem overall_error_claim' (i : Instance)
    (cited_graph_rule : StatClaim.Interface.Scope.largeSample.permits i.graph_slack ∧
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
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack))
    (cited_inspiratory_capacity_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null i)
    i.inspiratory_capacity_ni_test ((1 : ℚ) / 40) i.inspiratory_capacity_ni_slack)
    (cited_onset_of_action_sup_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_regression_one_sided.scope full_set_binary.law null_2
    i.onset_of_action_sup_test ((1 : ℚ) / 40) i.onset_of_action_sup_slack)
    (cited_tdi_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null_3 i)
    i.tdi_ni_test ((1 : ℚ) / 40) i.tdi_ni_slack)
    (cited_emsci_ni_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.mmrm_test_one_sided.scope i.per_protocol.law (null_4 i)
    i.emsci_ni_test ((1 : ℚ) / 40) i.emsci_ni_slack) :
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
    cited_inspiratory_capacity_ni_level.2
  have b₃ := v₃.bound m₃ i.inspiratory_capacity_ni_test.measurable o₃
  have s₃ : 0 ≤ i.inspiratory_capacity_ni_slack :=
    StatClaim.Interface.Scope.permits_nonnegative cited_inspiratory_capacity_ni_level.1
  have o₄ : ∀ parameter, null_2 parameter → (full_set_binary.law parameter).real i.onset_of_action_sup_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.onset_of_action_sup_slack) :=
    cited_onset_of_action_sup_level.2
  have b₄ := v₄.bound m₄ i.onset_of_action_sup_test.measurable o₄
  have s₄ : 0 ≤ i.onset_of_action_sup_slack :=
    StatClaim.Interface.Scope.permits_nonnegative cited_onset_of_action_sup_level.1
  have o₅ : ∀ parameter, (null_3 i) parameter → (i.per_protocol.law parameter).real i.tdi_ni_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.tdi_ni_slack) :=
    cited_tdi_ni_level.2
  have b₅ := v₅.bound m₅ i.tdi_ni_test.measurable o₅
  have s₅ : 0 ≤ i.tdi_ni_slack :=
    StatClaim.Interface.Scope.permits_nonnegative cited_tdi_ni_level.1
  have o₆ : ∀ parameter, (null_4 i) parameter → (i.per_protocol.law parameter).real i.emsci_ni_test.reject ≤ ((↑((1 : ℚ) / 40) : ℝ) + i.emsci_ni_slack) :=
    cited_emsci_ni_level.2
  have b₆ := v₆.bound m₆ i.emsci_ni_test.measurable o₆
  have s₆ : 0 ≤ i.emsci_ni_slack :=
    StatClaim.Interface.Scope.permits_nonnegative cited_emsci_ni_level.1
  have g₀ : 0 ≤ i.graph_slack :=
    StatClaim.Interface.Scope.permits_nonnegative cited_graph_rule.1
  have c₁ : StatClaim.Interface.familywiseClaim σ.law
        ![fun θ => (null i) (v₀.parameter θ),
        fun θ => (null i) (v₁.parameter θ),
        fun θ => (null_1 i) (v₂.parameter θ)]
        (i.graph_procedure Θ Ω σ v₀ v₁ v₂)
        ((↑((1 : ℚ) / 40) : ℝ) + i.graph_slack) :=
    cited_graph_rule.2 Θ Ω σ v₀ v₁ v₂ m₀ m₁ m₂
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

theorem onset_error_claim' (i : Instance)
    (cited_onset_of_action_sup_level : StatClaim.Interface.LevelPremise StatClaim.Generated.Methods.logistic_regression_one_sided.scope full_set_binary.law null_2
    i.onset_of_action_sup_test ((1 : ℚ) / 40) i.onset_of_action_sup_slack) :
    StatClaim.Interface.typeIClaim design_2_compatible null_2 i.onset_of_action_sup_test ((↑((1 : ℚ) / 40) : ℝ) + i.onset_of_action_sup_slack) :=
  StatClaim.Interface.typeI_of_premise design_2_compatible cited_onset_of_action_sup_level

end Copd.Old

namespace Copd

open StatClaim StatClaim.Semantics

/-- The program as data, as `lean_translation/data.py` writes it. -/
def program : StatClaim.Semantics.Program := ⟨[
  .familywise (.graphical "co_primary"
    [.cited "trough_fev1_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "peak_fev1_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "peak_fev1_sup" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    [((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] [[(0 : ℚ), (1 : ℚ), (0 : ℚ)], [(0 : ℚ), (0 : ℚ), (1 : ℚ)], [(1 : ℚ), (0 : ℚ), (0 : ℚ)]] ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩),
  .familywise (.sequence "trial"
    [.graphical "co_primary"
    [.cited "trough_fev1_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "peak_fev1_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "peak_fev1_sup" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    [((1 : ℚ) / 2), ((1 : ℚ) / 2), (0 : ℚ)] [[(0 : ℚ), (1 : ℚ), (0 : ℚ)], [(0 : ℚ), (0 : ℚ), (1 : ℚ)], [(1 : ℚ), (0 : ℚ), (0 : ℚ)]] ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "inspiratory_capacity_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-50 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "onset_of_action_sup" StatClaim.Generated.Methods.logistic_regression_one_sided
      { model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .proportion_difference_at_most, model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "tdi_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some (-1 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩,
    .cited "emsci_ni" StatClaim.Generated.Methods.mmrm_test_one_sided
      { model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, stopping := .fixed }
      { key := .mean_difference_at_most, model := { outcome := .continuous, sizes := ⟨440, 440, by decide, by decide⟩ }, value := some ((-1 : ℚ) / 10) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩]
    ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩),
  .typeI (.cited "onset_of_action_sup" StatClaim.Generated.Methods.logistic_regression_one_sided
      { model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, stopping := .fixed }
      { key := .proportion_difference_at_most, model := { outcome := .binary, sizes := ⟨500, 500, by decide, by decide⟩ }, value := some (0 : ℚ) }
      ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩)]⟩

theorem contracts : program.Contracts := by decide +kernel

theorem grades :
    [program.grade 0 [3], program.grade 1 [7, 8, 9, 10, 11], program.grade 2 [12]] =
      [.cited, .conditional, .cited] := by
  decide +kernel

/-- Claims stated by the semantics, proved with today's proofs. -/
theorem claim_0 : program.ClaimFrom 0 [3] := fun _ h => h.1.2

set_option maxHeartbeats 2800000 in
theorem claim_1 : program.ClaimFrom 1 [7, 8, 9, 10, 11] := fun i h =>
  Old.overall_error_claim' i h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1

theorem claim_2 : program.ClaimFrom 2 [12] := fun i h => Old.onset_error_claim' i h.1

/-! The semantics states what today's translation states, definitionally. -/

example (i : Instance) :
    Old.Claims i ↔ program.claimAt 0 i ∧ program.claimAt 1 i ∧ program.claimAt 2 i := Iff.rfl
example (i : Instance) (h : program.Using i [0, 1, 2, 3, 8, 9, 10, 11]) : Old.Premises i :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩
example (i : Instance) (h : Old.Premises i) : program.Using i [0, 1, 2, 3, 8, 9, 10, 11] :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, trivial⟩

end Copd
