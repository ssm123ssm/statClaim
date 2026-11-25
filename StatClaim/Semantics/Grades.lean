module

public import StatClaim.Semantics.Meaning

/-!
A claim's grade, from the premises its statement assumes: those of the tests it
involves. The grade cannot depend on how a proof was found.

Trusted. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

inductive Grade where
  | proved
  | conditional
  | cited
  | declared
  deriving DecidableEq, Repr

/-- The grade's name, as Python reports it. -/
def Grade.name : Grade → String
  | .proved => "proved"
  | .conditional => "conditional"
  | .cited => "cited"
  | .declared => "declared"

/-- Whether a premise is a test's level that the author declared. -/
def Premise.declared : Premise → Bool
  | .level _ (.declared ..) .. => true
  | _ => false

/-- A claim resting on its own premise is cited, or declared when the author declared
it; one resting only on its members' premises is conditional; one resting on none is
proved. -/
def Program.grade (p : Program) (r : ℕ) : Grade :=
  match p.requests[r]? with
  | none => .cited
  | some q =>
    match q.premises.find? (fun premise => some premise.name == q.test.map Test.name) with
    | some own => if own.declared then .declared else .cited
    | none => if q.premises.isEmpty then .proved else .conditional

end StatClaim.Semantics
