module

public import StatClaim.Core.Objects
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
Two-arm models whose outcome law Lean does not fix, for continuous and survival
outcomes. A program's claims about such a model hold for every model of this
shape that meets the program's premises. Binary outcomes keep their concrete law
in `StatClaim.Modules.TwoArmBinomial`.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Interface

open MeasureTheory

/-- A two-arm model with any parameter space, any probability laws, and the
treatment effect each parameter implies, in the units the outcome's null forms
are stated in: a mean difference, or a quantity that is zero exactly when the
survival curves agree at every time. -/
structure TwoArmModel (Parameter : Type) (Outcome : Type) [MeasurableSpace Outcome]
    extends Core.Model Parameter Outcome where
  effect : Parameter → ℝ

/-- The shape of a null form: the effect equals a value, or lies on one side of it. -/
inductive NullShape where
  | equal
  | atMost
  | atLeast
  deriving DecidableEq, Repr

/-- The null as a predicate on the effect. A null form without a value uses zero. -/
def NullShape.holds : NullShape → ℚ → ℝ → Prop
  | .equal, value, effect => effect = value
  | .atMost, value, effect => effect ≤ value
  | .atLeast, value, effect => (value : ℝ) ≤ effect

/-- The parameters at which a null form holds in a model. -/
def TwoArmModel.null {Parameter : Type} {Outcome : Type} [MeasurableSpace Outcome]
    (model : TwoArmModel Parameter Outcome) (shape : NullShape) (value : ℚ) :
    Core.Hypothesis Parameter :=
  fun parameter => shape.holds value (model.effect parameter)

/-- A one-point model with no effect, used only to show that a program's
premises can hold together. It states nothing about any study. -/
noncomputable def TwoArmModel.trivial : TwoArmModel Unit Unit where
  law := fun _ => Measure.dirac ()
  probability := fun _ => inferInstance
  admissible := Set.univ
  admissible_measurable := MeasurableSet.univ
  supported := fun _ => by simp
  effect := fun _ => 0

end StatClaim.Interface
