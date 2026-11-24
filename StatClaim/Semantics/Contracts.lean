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

/-- Whole clusters were assigned. The model's law is then one the instance gives. -/
def Model.clustered (model : Model) : Bool :=
  model.clusters.isSome

/-- The declared design features a test's assumptions can contradict. -/
def Model.features (model : Model) : List Generated.DesignFeature :=
  (match model.measurements with
    | some count => if 1 < count then [.repeated_measures] else []
    | none => []) ++
  (if model.clusters.isSome then [.clusters] else [])

/-- What a cited test's minimum sizes count, in each arm. -/
def Model.counts (model : Model) (unit : Generated.CountUnit) : ℕ × ℕ :=
  match unit with
  | .cluster => model.clusters.getD (0, 0)
  | .participant => (model.sizes.nControl, model.sizes.nTreatment)

/-- A null fits a test on a design: it is about the design's model, and it has a value
exactly when its form takes one. -/
def Null.fits (null : Null) (design : Design) : Bool :=
  decide (null.model = design.model) && decide (null.value.isSome = null.key.takesValue)

/-- A row of a graph passes nothing to its own test, nothing negative, and at most all. -/
def rowFits (index : ℕ) (row : List ℚ) : Bool :=
  decide (row[index]? = some 0) && row.all (fun t => decide (0 ≤ t)) && decide (row.sum ≤ 1)

/-- A single test, not a combination. -/
def Test.single : Test → Bool
  | .fisher .. => true
  | .assumed .. => true
  | _ => false

mutual
def Test.check : Test → Bool
  | .fisher _ design null _ =>
    null.fits design && decide (design.model.outcome = .binary) &&
    decide (null.key = .equal_proportions) && design.model.features.isEmpty
  | .assumed _ (.declared ..) design null alpha =>
    null.fits design && decide (0 < alpha.value) && decide (alpha.value < 1)
  | .assumed _ (.cited method) design null alpha =>
    let counts := design.model.counts method.unit
    null.fits design && method.nulls.contains null.key &&
    decide (null.key.outcome = method.outcome) &&
    decide (design.model.outcome = method.outcome) &&
    decide (method.unit = if design.model.clustered then .cluster else .participant) &&
    decide (method.minPerArm ≤ counts.1) && decide (method.minPerArm ≤ counts.2) &&
    decide (method.minTotal ≤ counts.1 + counts.2) &&
    design.model.features.all (fun feature =>
      method.assumptions.all fun assumption => !(feature.contradicts.contains assumption)) &&
    (match method.nullValue with
      | none => true
      | some value => decide (null.value = some value)) &&
    decide (0 < alpha.value) && decide (alpha.value < 1)
  | .bonferroni _ members alpha =>
    Test.checkAll members && members.all Test.single &&
    decide ((members.map Test.alpha).sum ≤ alpha.value)
  | .graphical _ members weights rows alpha =>
    Test.checkAll members && members.all Test.single &&
    decide (weights.length = members.length) &&
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

/-- A Type I claim is about a single test, and a familywise claim about a combination. -/
def Request.check : Request → Bool
  | .typeI t => t.single && t.check
  | .familywise t => !t.single && t.check

/-- Every declared test and combination meets its contracts, and every request has its
shape. -/
def Program.Contracts (p : Program) : Prop :=
  (p.declarations.all Test.check && p.requests.all Request.check) = true

instance (p : Program) : Decidable p.Contracts :=
  inferInstanceAs (Decidable (_ = true))

end StatClaim.Semantics
