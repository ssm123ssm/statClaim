module

public import StatClaim.Semantics.Syntax

/-!
The contract checks of a program, computed from its data. `decide +kernel` evaluates
them; plain `decide` cannot reduce rational arithmetic.

Trusted. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

def Model.outcome : Model → Generated.OutcomeKind
  | .binomial _ => .binary
  | .continuous .. => .continuous

def Model.control : Model → ℕ
  | .binomial sizes => sizes.nControl
  | .continuous control _ => control

def Model.treatment : Model → ℕ
  | .binomial sizes => sizes.nTreatment
  | .continuous _ treatment => treatment

/-- A row of a graph passes nothing to its own test, nothing negative, and at most all. -/
def rowFits (index : ℕ) (row : List ℚ) : Bool :=
  decide (row[index]? = some 0) && row.all (fun t => decide (0 ≤ t)) && decide (row.sum ≤ 1)

mutual
def Test.check : Test → Bool
  | .fisher _ _ null _ => decide (null.key = .equal_proportions)
  | .cited _ method model null alpha =>
    method.nulls.contains null.key && decide (null.key.outcome = method.outcome) &&
    decide (model.outcome = method.outcome) && decide (method.unit = .participant) &&
    decide (method.minPerArm ≤ model.control) && decide (method.minPerArm ≤ model.treatment) &&
    decide (method.minTotal ≤ model.control + model.treatment) &&
    (match method.nullValue with
      | none => true
      | some value => decide (value = null.value)) &&
    decide (0 < alpha.value) && decide (alpha.value < 1)
  | .bonferroni _ members alpha =>
    Test.checkAll members && decide ((members.map Test.alpha).sum ≤ alpha.value)
  | .graphical _ members weights rows alpha =>
    Test.checkAll members && decide (weights.length = members.length) &&
    weights.all (fun w => decide (0 ≤ w)) && decide (weights.sum ≤ 1) &&
    decide (rows.length = members.length) &&
    (List.range rows.length).all (fun index => rowFits index (rows.getD index [])) &&
    members.all (fun t => decide (t.alpha = alpha.value))
  | .sequence _ members alpha =>
    Test.checkAll members && members.all (fun t => decide (t.alpha = alpha.value))
termination_by structural t => t

def Test.checkAll : List Test → Bool
  | [] => true
  | t :: ts => Test.check t && Test.checkAll ts
termination_by structural ts => ts
end

def Program.Contracts (p : Program) : Prop :=
  p.requests.all (fun r => r.test.check) = true

instance (p : Program) : Decidable p.Contracts :=
  inferInstanceAs (Decidable (_ = true))

end StatClaim.Semantics
