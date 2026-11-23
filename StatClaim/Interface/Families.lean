module

public import StatClaim.Core.Objects
public import StatClaim.Modules.Composition
public import Mathlib.Tactic.Linarith

/-!
Families of tests in translated programs.

A family's claim is about a joint study: one law over everything its members
measure. Each member is read off the joint study through a view, which gives the
member's parameter and outcome. A family claim holds for every joint study whose
marginal for each member is that member's declared law, whatever the dependence
between members. The members' own guarantees carry over to the joint study
through those marginals, and a composition rule combines them.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Interface

open MeasureTheory

variable {Parameter : Type} {Outcome : Type} [MeasurableSpace Outcome]

/-- One law over everything a family's members measure. -/
structure JointStudy (Parameter : Type) (Outcome : Type) [MeasurableSpace Outcome] where
  law : Parameter → Measure Outcome
  probability : ∀ parameter, IsProbabilityMeasure (law parameter)

/-- How a member is read off a joint study: its parameter and its outcome. -/
structure MemberView (Parameter : Type) (Outcome : Type) (MemberParameter : Type)
    (MemberOutcome : Type) [MeasurableSpace Outcome] [MeasurableSpace MemberOutcome] where
  parameter : Parameter → MemberParameter
  outcome : Outcome → MemberOutcome
  measurable : Measurable outcome

/-- The joint study's marginal for the member's outcome is the member's declared law. -/
def MemberView.Marginal {MemberParameter : Type} {MemberOutcome : Type}
    [MeasurableSpace MemberOutcome]
    (view : MemberView Parameter Outcome MemberParameter MemberOutcome)
    (joint : JointStudy Parameter Outcome) (memberLaw : MemberParameter → Measure MemberOutcome) :
    Prop :=
  ∀ parameter, (joint.law parameter).map view.outcome = memberLaw (view.parameter parameter)

/-- A member's own bound carries over to a joint study through its marginal. -/
theorem MemberView.bound {MemberParameter : Type} {MemberOutcome : Type}
    [MeasurableSpace MemberOutcome]
    (view : MemberView Parameter Outcome MemberParameter MemberOutcome)
    {joint : JointStudy Parameter Outcome} {memberLaw : MemberParameter → Measure MemberOutcome}
    (marginal : view.Marginal joint memberLaw) {null : Core.Hypothesis MemberParameter}
    {reject : Set MemberOutcome} (measurable : MeasurableSet reject) {bound : ℝ}
    (member : ∀ parameter, null parameter → (memberLaw parameter).real reject ≤ bound) :
    ∀ parameter, null (view.parameter parameter) →
      (joint.law parameter).real (view.outcome ⁻¹' reject) ≤ bound := by
  intro parameter holds
  rw [← map_measureReal_apply view.measurable measurable, marginal parameter]
  exact member _ holds

/-- A Type I claim under a design's sampling law is a bound under the model's law. -/
theorem model_bound {model : Core.Model Parameter Outcome} {design : Core.StudyDesign model}
    (compatibility : Core.Compatibility design) {null : Core.Hypothesis Parameter}
    {reject : Set Outcome} {bound : ℝ}
    (claim : ∀ parameter, null parameter →
      (compatibility.samplingLaw.law parameter).real reject ≤ bound) :
    ∀ parameter, null parameter → (model.law parameter).real reject ≤ bound := by
  intro parameter holds
  rw [← compatibility.agrees]
  exact claim parameter holds

/-- The familywise claim: some true null is rejected with probability at most the bound. -/
def familywiseClaim {m : ℕ} (law : Parameter → Measure Outcome)
    (nulls : Fin m → Core.Hypothesis Parameter) (rejects : Fin m → Set Outcome) (bound : ℝ) :
    Prop :=
  ∀ parameter, (law parameter).real
    (StatClaim.Modules.Composition.falseRejection (fun k => nulls k parameter) rejects) ≤ bound

/-- The union bound over members: with levels summing to at most the family's level,
some true null is rejected with probability at most that level plus the slacks. -/
theorem familywise_of_members {m : ℕ} (joint : JointStudy Parameter Outcome)
    (nulls : Fin m → Core.Hypothesis Parameter) (rejects : Fin m → Set Outcome)
    (levels : Fin m → ℚ) (slacks : Fin m → ℝ) (levels_nonnegative : ∀ k, 0 ≤ levels k)
    (slacks_nonnegative : ∀ k, 0 ≤ slacks k)
    (members : ∀ k parameter, nulls k parameter →
      (joint.law parameter).real (rejects k) ≤ levels k + slacks k)
    (alpha : ℚ) (allocation : ∑ k, levels k ≤ alpha) :
    familywiseClaim joint.law nulls rejects (alpha + ∑ k, slacks k) := by
  intro parameter
  have := joint.probability parameter
  have total : ∑ k, (levels k : ℝ) ≤ alpha := by exact_mod_cast allocation
  exact StatClaim.Modules.Composition.familywise_le (joint.law parameter)
    (fun k => nulls k parameter) rejects (fun k => (levels k : ℝ)) slacks
    (fun k => by exact_mod_cast levels_nonnegative k) slacks_nonnegative
    (fun k holds => members k parameter holds) alpha total

/-- The fixed-sequence claim: testing in order, each test only after every earlier
test rejected, some true null is rejected with probability at most the bound. -/
def sequenceClaim {m : ℕ} (law : Parameter → Measure Outcome)
    (nulls : Fin m → Core.Hypothesis Parameter) (rejects : Fin m → Set Outcome) (bound : ℝ) :
    Prop :=
  ∀ parameter, (law parameter).real
    (StatClaim.Modules.Composition.sequenceFalseRejection (fun k => nulls k parameter) rejects)
      ≤ bound

/-- A fixed sequence of members, each at the full level: some true null is rejected
with probability at most that level plus the members' slacks. -/
theorem sequence_of_members {m : ℕ} (joint : JointStudy Parameter Outcome)
    (nulls : Fin m → Core.Hypothesis Parameter) (rejects : Fin m → Set Outcome)
    (alpha : ℚ) (slacks : Fin m → ℝ) (alpha_nonnegative : 0 ≤ alpha)
    (slacks_nonnegative : ∀ k, 0 ≤ slacks k)
    (members : ∀ k parameter, nulls k parameter →
      (joint.law parameter).real (rejects k) ≤ alpha + slacks k) :
    sequenceClaim joint.law nulls rejects (alpha + ∑ k, slacks k) := by
  intro parameter
  have := joint.probability parameter
  apply StatClaim.Modules.Composition.fixed_sequence_le (joint.law parameter) _ rejects alpha
    (∑ k, slacks k) (by exact_mod_cast alpha_nonnegative)
    (Finset.sum_nonneg fun k _ => slacks_nonnegative k)
  intro k holds
  have bound := members k parameter holds
  have within : slacks k ≤ ∑ j, slacks j :=
    Finset.single_le_sum (fun j _ => slacks_nonnegative j) (Finset.mem_univ k)
  linarith

/-- A design with looks as one member: under its question's null at every look, it
rejects at some look with probability at most its familywise bound. -/
theorem looks_member {m : ℕ} {law : Parameter → Measure Outcome}
    {nulls : Fin m → Core.Hypothesis Parameter} {rejects : Fin m → Set Outcome} {bound : ℝ}
    (claim : familywiseClaim law nulls rejects bound) :
    ∀ parameter, (∀ k, nulls k parameter) → (law parameter).real (⋃ k, rejects k) ≤ bound := by
  intro parameter all
  have rejection := claim parameter
  have same : StatClaim.Modules.Composition.falseRejection (fun k => nulls k parameter) rejects
      = ⋃ k, rejects k := by
    ext outcome
    simp [StatClaim.Modules.Composition.falseRejection, all]
  rwa [same] at rejection

/-- A family as one member of a sequence: it passes only if every member rejects, so
when one of its nulls is true it passes with probability at most its familywise bound. -/
theorem family_member {m : ℕ} (joint : JointStudy Parameter Outcome)
    {nulls : Fin m → Core.Hypothesis Parameter} {rejects : Fin m → Set Outcome} {bound : ℝ}
    (claim : familywiseClaim joint.law nulls rejects bound) :
    ∀ parameter, (∃ k, nulls k parameter) →
      (joint.law parameter).real (⋂ k, rejects k) ≤ bound := by
  rintro parameter ⟨k, true_null⟩
  have := joint.probability parameter
  refine le_trans (measureReal_mono fun outcome passed => ?_) (claim parameter)
  simp only [StatClaim.Modules.Composition.falseRejection, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨k, true_null, Set.mem_iInter.1 passed k⟩

/-- A fixed sequence as one member of another: the same, for its sequence bound. -/
theorem sequence_member {m : ℕ} (joint : JointStudy Parameter Outcome)
    {nulls : Fin m → Core.Hypothesis Parameter} {rejects : Fin m → Set Outcome} {bound : ℝ}
    (claim : sequenceClaim joint.law nulls rejects bound) :
    ∀ parameter, (∃ k, nulls k parameter) →
      (joint.law parameter).real (⋂ k, rejects k) ≤ bound := by
  rintro parameter ⟨k, true_null⟩
  have := joint.probability parameter
  refine le_trans (measureReal_mono fun outcome passed => ?_) (claim parameter)
  exact ⟨k, true_null, fun i _ => Set.mem_iInter.1 passed i⟩

/-- A procedure that rejects nothing meets any nonnegative familywise bound. This is how
a program's premise about a graphical procedure is shown satisfiable. -/
theorem familywise_of_nothing {m : ℕ} (law : Parameter → Measure Outcome)
    (nulls : Fin m → Core.Hypothesis Parameter) {bound : ℝ} (nonnegative : 0 ≤ bound) :
    familywiseClaim law nulls (fun _ => ∅) bound := by
  intro parameter
  have empty : StatClaim.Modules.Composition.falseRejection (fun k => nulls k parameter)
      (fun _ => (∅ : Set Outcome)) = ∅ := by
    ext outcome
    simp [StatClaim.Modules.Composition.falseRejection]
  rw [empty, measureReal_empty]
  exact nonnegative

end StatClaim.Interface
