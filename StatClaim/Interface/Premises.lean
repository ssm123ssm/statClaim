module

public import StatClaim.Core.Objects

/-!
Tests seen from outside, and the premises about them that a program rests on.

A cited or declared test enters a program as a rejection event and a level
premise. The premise is a hypothesis of the program's theorem, never a global
assumption: if it fails for a study, only the claims that use it say nothing
there. Premises state "at most"; a guarantee of equality implies it.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Interface

open MeasureTheory

/-- Where a premise's statement comes from. Reported with results; no proof uses it. -/
inductive Source where
  | literature
  | author
  deriving DecidableEq, Repr

/-- Whether a guarantee holds at the declared sizes or only as they grow. -/
inductive Scope where
  | finiteSample
  | largeSample
  deriving DecidableEq, Repr

/-- The slack a guarantee of each scope permits. A finite-sample guarantee has
none. A large-sample guarantee has an unknown, nonnegative excess over its level
at the declared sizes; conclusions carry it, so they never read as bounds at the
level itself. -/
def Scope.permits : Scope → ℝ → Prop
  | .finiteSample, slack => slack = 0
  | .largeSample, slack => 0 ≤ slack

theorem Scope.permits_zero (scope : Scope) : scope.permits 0 := by
  cases scope <;> simp [Scope.permits]

theorem Scope.permits_nonnegative {scope : Scope} {slack : ℝ} (permitted : scope.permits slack) :
    0 ≤ slack := by
  cases scope
  · exact le_of_eq (Eq.symm permitted)
  · exact permitted

/-- A test seen from outside: the outcomes on which it rejects. -/
structure TestInterface (Outcome : Type) [MeasurableSpace Outcome] where
  reject : Set Outcome
  measurable : MeasurableSet reject

/-- A test that never rejects. -/
def TestInterface.neverRejects (Outcome : Type) [MeasurableSpace Outcome] :
    TestInterface Outcome :=
  ⟨∅, MeasurableSet.empty⟩

variable {Parameter : Type} {Outcome : Type} [MeasurableSpace Outcome]

/-- The level premise: under every parameter of the null, the test rejects with
probability at most its level plus the slack its scope permits. -/
def LevelPremise (scope : Scope) (law : Parameter → Measure Outcome)
    (null : Core.Hypothesis Parameter) (test : TestInterface Outcome) (level : ℚ) (slack : ℝ) :
    Prop :=
  scope.permits slack ∧ ∀ parameter, null parameter → (law parameter).real test.reject ≤ level + slack

/-- A test that never rejects meets every level premise with a nonnegative level.
This is what makes a program's premises satisfiable. -/
theorem neverRejects_meets_level (scope : Scope) (law : Parameter → Measure Outcome)
    (null : Core.Hypothesis Parameter) (level : ℚ) (nonnegative : 0 ≤ level) :
    LevelPremise scope law null (TestInterface.neverRejects Outcome) level 0 := by
  refine ⟨scope.permits_zero, fun parameter _ => ?_⟩
  simp only [TestInterface.neverRejects, measureReal_empty, add_zero]
  exact_mod_cast nonnegative

/-- The Type I claim of a test seen from outside, under the sampling law its
design supplies. Without that law there is no claim to state. -/
def typeIClaim {model : Core.Model Parameter Outcome} {design : Core.StudyDesign model}
    (compatibility : Core.Compatibility design) (null : Core.Hypothesis Parameter)
    (test : TestInterface Outcome) (bound : ℝ) : Prop :=
  ∀ parameter, null parameter → (compatibility.samplingLaw.law parameter).real test.reject ≤ bound

/-- A level premise gives the Type I claim, at the level plus the premise's slack. -/
theorem typeI_of_premise {model : Core.Model Parameter Outcome} {design : Core.StudyDesign model}
    (compatibility : Core.Compatibility design) {scope : Scope} {null : Core.Hypothesis Parameter}
    {test : TestInterface Outcome} {level : ℚ} {slack : ℝ}
    (premise : LevelPremise scope model.law null test level slack) :
    typeIClaim compatibility null test (level + slack) := by
  intro parameter holds
  rw [compatibility.agrees]
  exact premise.2 parameter holds

/-- A finite-sample premise gives the Type I claim at the level itself. -/
theorem typeI_of_finite_premise {model : Core.Model Parameter Outcome}
    {design : Core.StudyDesign model} (compatibility : Core.Compatibility design) {scope : Scope}
    (finite : scope = .finiteSample) {null : Core.Hypothesis Parameter}
    {test : TestInterface Outcome} {level : ℚ} {slack : ℝ}
    (premise : LevelPremise scope model.law null test level slack) :
    typeIClaim compatibility null test level := by
  subst finite
  have zero : slack = 0 := premise.1
  have claim := typeI_of_premise compatibility premise
  rwa [zero, add_zero] at claim

end StatClaim.Interface
