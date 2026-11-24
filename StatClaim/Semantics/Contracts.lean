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
  | .associated .. => true
  | _ => false

/-- What a cited test of association's minimum total counts: the pairs of a matched
study, nothing for a person-time cohort, otherwise the fixed group sizes or `n`. -/
def Study.total (study : Study) : Option ℕ :=
  match study.design with
  | .matched_case_control => study.pairs
  | .person_time_cohort => none
  | .case_control => some (study.cases.getD 0 + study.controls.getD 0)
  | .cohort =>
    match study.exposed, study.unexposed with
    | some exposed, some unexposed => some (exposed + unexposed)
    | _, _ => study.n
  | .cross_sectional => study.n

/-- A design with looks. -/
def Test.isLooks : Test → Bool
  | .looks .. => true
  | _ => false

/-- The question a look asks: its test, and its null's form and value. -/
def Test.question : Test → Option (String × Generated.NullKey × Option ℚ)
  | .fisher _ _ null _ => some ("fisher", null.key, null.value)
  | .assumed _ (.cited method) _ null _ => some (method.key, null.key, null.value)
  | .assumed _ (.declared method ..) _ null _ => some (method, null.key, null.value)
  | _ => none

/-- The arm sizes a look is taken at. -/
def Test.sizes : Test → Option (ℕ × ℕ)
  | .fisher _ design .. => some (design.model.sizes.nControl, design.model.sizes.nTreatment)
  | .assumed _ _ design .. => some (design.model.sizes.nControl, design.model.sizes.nTreatment)
  | _ => none

/-- Each look is taken at no fewer participants in either arm, and more in all. -/
def growing : List (ℕ × ℕ) → Bool
  | a :: b :: rest =>
    decide (a.1 ≤ b.1 ∧ a.2 ≤ b.2 ∧ a.1 + a.2 < b.1 + b.2) && growing (b :: rest)
  | _ => true

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
  | .associated _ method design null alpha adjusted =>
    let study := design.model
    decide (null.model = study) && method.designs.contains study.design &&
    method.outcomeScales.contains study.outcomeScale &&
    method.exposureScales.contains study.exposureScale && method.surveys.contains study.survey &&
    (match study.total with
      | some total => decide (method.minTotal ≤ total)
      | none => true) &&
    (match method.minClusters with
      | some least => study.survey != .cluster || decide (least ≤ study.clusters.getD 0)
      | none => true) &&
    (adjusted.isEmpty || method.covariates) &&
    decide (0 < alpha.value) && decide (alpha.value < 1)
  | .bonferroni _ members _ _ =>
    Test.checkAll members && members.all (fun t => t.single || t.isLooks)
  | .looks _ members _ =>
    Test.checkAll members && members.all Test.single &&
    (match members with
      | [] => false
      | first :: rest =>
        first.question.isSome && rest.all (fun look => look.question == first.question)) &&
    (match members.mapM Test.sizes with
      | some sizes => growing sizes
      | none => false)
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

/-- A Type I claim is about a single test or a design with looks, and a familywise claim
about another combination. -/
def Request.check : Request → Bool
  | .typeI t => (t.single || t.isLooks) && t.check
  | .familywise t => !t.single && !t.isLooks && t.check

/-- Every declared test and combination meets its contracts, and every request has its
shape. -/
def Program.Contracts (p : Program) : Prop :=
  (p.declarations.all Test.check && p.requests.all Request.check) = true

instance (p : Program) : Decidable p.Contracts :=
  inferInstanceAs (Decidable (_ = true))

end StatClaim.Semantics
