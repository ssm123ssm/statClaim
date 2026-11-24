module

public import StatClaim.Semantics.Meaning

/-!
A claim's grade, from the premises its statement lists: the grade cannot depend on
how the proof was found.

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
  deriving DecidableEq, Repr

/-- A claim resting on its own premise is cited; one resting only on others' premises
is conditional; one resting on none is proved. -/
def Program.grade (p : Program) (r : ℕ) (uses : List ℕ) : Grade :=
  let used := uses.filterMap fun k => p.premises[k]?
  match p.requests[r]? with
  | none => .cited
  | some q =>
    if used.any (fun premise => premise.name == q.test.name) then .cited
    else if used.isEmpty then .proved
    else .conditional

end StatClaim.Semantics
