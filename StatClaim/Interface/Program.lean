module

public import StatClaim.Interface.Premises

/-!
The shape of the theorem a translated program ends in.

A program's abstract parts, such as the laws of its continuous outcomes and the
rejection events of its cited tests, range over a type of instances. Its theorem
says that, for every instance, the premises imply the claims, and that some
instance meets the premises, so the implication is not vacuous.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Interface

universe u

/-- What a translated program establishes. -/
structure ProgramTheorem {Instance : Type u} (premises claims : Instance → Prop) : Prop where
  implies : ∀ point, premises point → claims point
  satisfiable : ∃ point, premises point

/-- With no premises left, a program theorem gives its claims outright. -/
theorem ProgramTheorem.claims_of_trivial {Instance : Type u} {premises claims : Instance → Prop}
    (theorem_ : ProgramTheorem premises claims) (trivial : ∀ point, premises point)
    (point : Instance) : claims point :=
  theorem_.implies point (trivial point)

end StatClaim.Interface
