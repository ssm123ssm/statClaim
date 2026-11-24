module

public import StatClaim.Semantics.Syntax
public import StatClaim.Interface.Outcomes
public import StatClaim.Interface.Premises
public import StatClaim.Interface.Families
public import StatClaim.Modules.Fisher
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
What a compiled program means: the abstract parts every program ranges over
(`Instance`), each test as a member of a combination, the premises, and the claims.
Every statement uses the objects of `StatClaim.Interface` and the modules, so the
meaning adds no statistical content of its own.

Mutual definitions are structurally recursive (`termination_by structural`): a
definition by well-founded recursion would not unfold, and statements about concrete
programs could not be compared with what proofs establish.

Trusted. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

noncomputable section

/-- A law Lean does not fix. -/
structure AbstractModel where
  Parameter : Type
  Outcome : Type
  [space : MeasurableSpace Outcome]
  model : TwoArmModel Parameter Outcome

attribute [instance] AbstractModel.space

/-- A model as its tests see it. -/
structure View where
  Parameter : Type
  Outcome : Type
  [space : MeasurableSpace Outcome]
  base : Core.Model Parameter Outcome

attribute [instance] View.space

def Model.view (laws : ℕ → ℕ → AbstractModel) : Model → View
  | .binomial sizes =>
    { Parameter := Modules.TwoArmBinomial.Parameters
      Outcome := Modules.TwoArmBinomial.Counts
      base := Modules.TwoArmBinomial.model sizes }
  | .continuous control treatment =>
    { Parameter := (laws control treatment).Parameter
      Outcome := (laws control treatment).Outcome
      base := (laws control treatment).model.toModel }

/-- One view of a joint study for each listed model. -/
def Views (Θ Ω : Type) [MeasurableSpace Ω] : List View → Type
  | [] => PUnit
  | v :: vs => MemberView Θ Ω v.Parameter v.Outcome × Views Θ Ω vs

/-- Everything a program leaves open: the laws of continuous models, the rejection
events and slacks of cited tests, and the procedures of graphs. -/
structure Instance where
  laws : ℕ → ℕ → AbstractModel
  test : String → (model : Model) → TestInterface (model.view laws).Outcome
  slack : String → ℝ
  graph : String → (vs : List View) → (m : ℕ) → ∀ (Θ Ω : Type) [MeasurableSpace Ω],
    JointStudy Θ Ω → Views Θ Ω vs → Fin m → Set Ω

/-- The parameters at which a null holds. A null form a model has no reading for is read
as `True`, the strongest claim; the contracts refuse such programs. -/
def Null.denote (laws : ℕ → ℕ → AbstractModel) (null : Null) :
    (model : Model) → Core.Hypothesis (model.view laws).Parameter
  | .binomial _ =>
    match null.key with
    | .equal_proportions => Modules.TwoArmBinomial.equalProportions
    | .proportion_difference => Modules.TwoArmBinomial.proportionDifference null.value
    | .proportion_difference_at_most =>
      Modules.TwoArmBinomial.proportionDifferenceAtMost null.value
    | _ => fun _ => True
  | .continuous control treatment =>
    (laws control treatment).model.null null.key.shape null.value

/-- The two-sided Fisher test on a fixed design, as its module defines it. -/
def fisherAnalysis (sizes : FixedSampleDesign) (alpha : SignificanceLevel) :=
  Modules.Fisher.analysis sizes (Core.StudyDesign.fixed (Modules.TwoArmBinomial.model sizes)) alpha

mutual
/-- The models of a test's single tests, in order. -/
def Test.leaves (laws : ℕ → ℕ → AbstractModel) : Test → List View
  | .fisher _ sizes _ _ => [(Model.binomial sizes).view laws]
  | .cited _ _ model _ _ => [model.view laws]
  | .bonferroni _ members _ => Test.leavesOf laws members
  | .graphical _ members _ _ _ => Test.leavesOf laws members
  | .sequence _ members _ => Test.leavesOf laws members
termination_by structural t => t

def Test.leavesOf (laws : ℕ → ℕ → AbstractModel) : List Test → List View
  | [] => []
  | t :: ts => Test.leaves laws t ++ Test.leavesOf laws ts
termination_by structural ts => ts
end

def Views.split {Θ Ω : Type} [MeasurableSpace Ω] :
    (a b : List View) → Views Θ Ω (a ++ b) → Views Θ Ω a × Views Θ Ω b
  | [], _, ws => (PUnit.unit, ws)
  | _ :: a, b, ws => ((ws.1, (Views.split a b ws.2).1), (Views.split a b ws.2).2)

/-- A test as one member of a combination, read off a joint study. -/
structure Outside (Θ Ω : Type) [MeasurableSpace Ω] where
  null : Θ → Prop
  reject : Set Ω
  slack : ℝ

/-- The members of a combination, read off a joint study: one vector for each part. -/
structure Members (Θ Ω : Type) [MeasurableSpace Ω] (n : ℕ) where
  nulls : Fin n → Θ → Prop
  rejects : Fin n → Set Ω
  slacks : Fin n → ℝ

mutual
def Test.outside (i : Instance) {Θ Ω : Type} [MeasurableSpace Ω]
    (σ : JointStudy Θ Ω) : (t : Test) → Views Θ Ω (t.leaves i.laws) → Outside Θ Ω
  | .fisher _ sizes _ alpha, ws =>
    { null := fun θ => (fisherAnalysis sizes alpha).hypothesis (ws.1.parameter θ)
      reject := ws.1.outcome ⁻¹' (fisherAnalysis sizes alpha).procedure.rejectionEvent
      slack := 0 }
  | .cited name _ model null _, ws =>
    { null := fun θ => null.denote i.laws model (ws.1.parameter θ)
      reject := ws.1.outcome ⁻¹' (i.test name model).reject
      slack := i.slack name }
  | .bonferroni _ members _, ws =>
    { null := fun θ => ∃ k, (Test.members i σ members ws).nulls k θ
      reject := ⋂ k, (Test.members i σ members ws).rejects k
      slack := ∑ k, (Test.members i σ members ws).slacks k }
  | .graphical name members _ _ _, ws =>
    { null := fun θ => ∃ k, (Test.members i σ members ws).nulls k θ
      reject := ⋂ k, i.graph name (Test.leavesOf i.laws members) members.length Θ Ω σ ws k
      slack := i.slack name }
  | .sequence _ members _, ws =>
    { null := fun θ => ∃ k, (Test.members i σ members ws).nulls k θ
      reject := ⋂ k, (Test.members i σ members ws).rejects k
      slack := ∑ k, (Test.members i σ members ws).slacks k }
termination_by structural t => t

def Test.members (i : Instance) {Θ Ω : Type} [MeasurableSpace Ω]
    (σ : JointStudy Θ Ω) : (ts : List Test) → Views Θ Ω (Test.leavesOf i.laws ts) →
    Members Θ Ω ts.length
  | [], _ => ⟨![], ![], ![]⟩
  | t :: ts, ws =>
    { nulls := Matrix.vecCons (Test.outside i σ t (Views.split _ _ ws).1).null
        (Test.members i σ ts (Views.split _ _ ws).2).nulls
      rejects := Matrix.vecCons (Test.outside i σ t (Views.split _ _ ws).1).reject
        (Test.members i σ ts (Views.split _ _ ws).2).rejects
      slacks := Matrix.vecCons (Test.outside i σ t (Views.split _ _ ws).1).slack
        (Test.members i σ ts (Views.split _ _ ws).2).slacks }
termination_by structural ts => ts
end

/-- For every view of each listed model. -/
def ForallViews (Θ Ω : Type) [MeasurableSpace Ω] :
    (vs : List View) → (Views Θ Ω vs → Prop) → Prop
  | [], body => body PUnit.unit
  | v :: vs, body => ∀ w : MemberView Θ Ω v.Parameter v.Outcome,
      ForallViews Θ Ω vs (fun ws => body (w, ws))

/-- If each view's marginal is its model's law, then the claim. -/
def Marginals {Θ Ω : Type} [MeasurableSpace Ω] (σ : JointStudy Θ Ω) :
    (vs : List View) → Views Θ Ω vs → Prop → Prop
  | [], _, claim => claim
  | v :: vs, ws, claim => ws.1.Marginal σ v.base.law → Marginals σ vs ws.2 claim

/-- A claim about every joint study whose marginals are the listed models' laws. -/
def Joint (vs : List View)
    (claim : ∀ {Θ Ω : Type} [MeasurableSpace Ω], JointStudy Θ Ω → Views Θ Ω vs → Prop) :
    Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Ω] (σ : JointStudy Θ Ω),
    ForallViews Θ Ω vs fun ws => Marginals σ vs ws (claim σ ws)

/-- The Type I claim of a single test, under its design's sampling law. A cited test
with a large-sample guarantee carries its slack. -/
def Test.typeI (i : Instance) : Test → Prop
  | .fisher _ sizes _ alpha =>
    ((fisherAnalysis sizes alpha).typeIClaim (Core.Compatibility.fixed _)
      (alpha.value : ℝ)).statement
  | .cited name method model null alpha =>
    typeIClaim (Core.Compatibility.fixed (model.view i.laws).base) (null.denote i.laws model)
      (i.test name model)
      (match method.scope with
        | .finiteSample => (alpha.value : ℝ)
        | .largeSample => (alpha.value : ℝ) + i.slack name)
  | _ => False

/-- The familywise claim of a combination, over every joint study whose marginals are
its members' laws. -/
def Test.familywise (i : Instance) : Test → Prop
  | .bonferroni _ members alpha =>
    Joint (Test.leavesOf i.laws members) fun σ ws =>
      familywiseClaim σ.law ((Test.members i σ members ws).nulls)
        ((Test.members i σ members ws).rejects)
        ((alpha.value : ℝ) + ∑ k, (Test.members i σ members ws).slacks k)
  | .graphical name members _ _ alpha =>
    Joint (Test.leavesOf i.laws members) fun σ ws =>
      familywiseClaim σ.law ((Test.members i σ members ws).nulls)
        (i.graph name (Test.leavesOf i.laws members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack name)
  | .sequence _ members alpha =>
    Joint (Test.leavesOf i.laws members) fun σ ws =>
      sequenceClaim σ.law ((Test.members i σ members ws).nulls)
        ((Test.members i σ members ws).rejects)
        ((alpha.value : ℝ) + ∑ k, (Test.members i σ members ws).slacks k)
  | _ => False

def Request.Holds (i : Instance) : Request → Prop
  | .typeI t => t.typeI i
  | .familywise t => t.familywise i

inductive Premise where
  | level (name : String) (method : Generated.TrialMethod) (model : Model) (null : Null)
      (alpha : SignificanceLevel)
  | graph (name : String) (members : List Test) (alpha : SignificanceLevel)

def Premise.name : Premise → String
  | .level name .. => name
  | .graph name .. => name

def Test.finiteSample : Test → Bool
  | .fisher .. => true
  | .cited _ method .. => method.scope == .finiteSample
  | _ => false

/-- What a premise assumes: a cited test's level, or a graph's familywise bound. -/
def Premise.Holds (i : Instance) : Premise → Prop
  | .level name method model null alpha =>
    LevelPremise method.scope (model.view i.laws).base.law (null.denote i.laws model)
      (i.test name model) alpha.value (i.slack name)
  | .graph name members alpha =>
    (match members.all Test.finiteSample with
      | true => Scope.finiteSample
      | false => Scope.largeSample).permits (i.slack name) ∧
    Joint (Test.leavesOf i.laws members) fun σ ws =>
      familywiseClaim σ.law ((Test.members i σ members ws).nulls)
        (i.graph name (Test.leavesOf i.laws members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack name)

mutual
def Test.premises : Test → List Premise
  | .fisher .. => []
  | .cited name method model null alpha => [.level name method model null alpha]
  | .bonferroni _ members _ => Test.premisesOf members
  | .graphical name members _ _ alpha => Test.premisesOf members ++ [.graph name members alpha]
  | .sequence _ members _ => Test.premisesOf members
termination_by structural t => t

def Test.premisesOf : List Test → List Premise
  | [] => []
  | t :: ts => Test.premises t ++ Test.premisesOf ts
termination_by structural ts => ts
end

/-- Each request's premises, in order; claims name them by position. -/
def Program.premises (p : Program) : List Premise :=
  p.requests.flatMap fun r => r.test.premises

def Program.premiseAt (p : Program) (k : ℕ) (i : Instance) : Prop :=
  match p.premises[k]? with
  | some q => q.Holds i
  | none => True

/-- The premises listed by their positions in `p.premises` hold. -/
def Program.Using (p : Program) (i : Instance) : List ℕ → Prop
  | [] => True
  | k :: ks => p.premiseAt k i ∧ p.Using i ks

def Program.claimAt (p : Program) (r : ℕ) (i : Instance) : Prop :=
  match p.requests[r]? with
  | some q => q.Holds i
  | none => False

/-- Request `r` holds for every instance meeting the premises in `uses`. -/
def Program.ClaimFrom (p : Program) (r : ℕ) (uses : List ℕ) : Prop :=
  ∀ i, p.Using i uses → p.claimAt r i

end

end StatClaim.Semantics
