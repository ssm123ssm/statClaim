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

/-- A model as its tests see it: its law, and how it reads a null. -/
structure View where
  Parameter : Type
  Outcome : Type
  [space : MeasurableSpace Outcome]
  base : Core.Model Parameter Outcome
  /-- The parameters at which a null holds. A null form the model has no reading for is
  read as `True`, the strongest claim; the contracts refuse such programs. -/
  null : Null → Core.Hypothesis Parameter

attribute [instance] View.space

def binomialNull (null : Null) : Core.Hypothesis Modules.TwoArmBinomial.Parameters :=
  match null.key with
  | .equal_proportions => Modules.TwoArmBinomial.equalProportions
  | .proportion_difference => Modules.TwoArmBinomial.proportionDifference (null.value.getD 0)
  | .proportion_difference_at_most =>
    Modules.TwoArmBinomial.proportionDifferenceAtMost (null.value.getD 0)
  | _ => fun _ => True

/-- The binomial model Lean defines, at the given arm sizes. -/
def binomialView (sizes : FixedSampleDesign) : View :=
  { Parameter := Modules.TwoArmBinomial.Parameters
    Outcome := Modules.TwoArmBinomial.Counts
    base := Modules.TwoArmBinomial.model sizes
    null := binomialNull }

/-- A model whose law the instance gives: a null is a statement about its effect. -/
def AbstractModel.view (model : AbstractModel) : View :=
  { Parameter := model.Parameter
    Outcome := model.Outcome
    base := model.model.toModel
    null := fun null => model.model.null null.key.shape (null.value.getD 0) }

/-- An observational study whose law Lean does not fix. -/
structure AbstractStudy where
  Parameter : Type
  Outcome : Type
  [space : MeasurableSpace Outcome]
  model : ObservationalModel Parameter Outcome

attribute [instance] AbstractStudy.space

/-- A study as its tests see it: its only null is no association. -/
def AbstractStudy.view (study : AbstractStudy) : View :=
  { Parameter := study.Parameter
    Outcome := study.Outcome
    base := study.model.toModel
    null := fun _ => study.model.noAssociation }

/-- A binary model of independent participants measured once has the binomial law; any
other model has the law the instance gives it, as the translator decides. -/
def Model.view (laws : Model → AbstractModel) : Model → View
  | { outcome := .binary, sizes, clusters := none, measurements := none, .. } =>
    binomialView sizes
  | model => (laws model).view

/-- One view of a joint study for each listed model. -/
def Views (Θ Ω : Type) [MeasurableSpace Ω] : List View → Type
  | [] => PUnit
  | v :: vs => MemberView Θ Ω v.Parameter v.Outcome × Views Θ Ω vs

/-- Everything a program leaves open, the same for every program: a law for each model
Lean does not fix, and a rejection event, slack and procedure for each test name. -/
structure Instance where
  laws : Model → AbstractModel
  studies : Study → AbstractStudy
  test : String → (model : Model) → TestInterface (model.view laws).Outcome
  studyTest : String → (study : Study) → TestInterface (studies study).Outcome
  slack : String → ℝ
  graph : String → (vs : List View) → (m : ℕ) → ∀ (Θ Ω : Type) [MeasurableSpace Ω],
    JointStudy Θ Ω → Views Θ Ω vs → Fin m → Set Ω

/-- The parameters at which a null holds, as the model reads it. -/
def Null.denote (laws : Model → AbstractModel) (null : Null) (model : Model) :
    Core.Hypothesis (model.view laws).Parameter :=
  (model.view laws).null null

/-- The two-sided Fisher test on a fixed design, as its module defines it. -/
def fisherAnalysis (sizes : FixedSampleDesign) (alpha : SignificanceLevel) :=
  Modules.Fisher.analysis sizes (Core.StudyDesign.fixed (Modules.TwoArmBinomial.model sizes)) alpha

mutual
/-- The models of a test's single tests, in order. -/
def Test.leaves (i : Instance) : Test → List View
  | .fisher _ design _ _ => [binomialView design.model.sizes]
  | .assumed _ _ design _ _ => [design.model.view i.laws]
  | .associated _ _ design _ _ _ => [(i.studies design.model).view]
  | .bonferroni _ members _ => Test.leavesOf i members
  | .graphical _ members _ _ _ => Test.leavesOf i members
  | .sequence _ members _ => Test.leavesOf i members
termination_by structural t => t

def Test.leavesOf (i : Instance) : List Test → List View
  | [] => []
  | t :: ts => Test.leaves i t ++ Test.leavesOf i ts
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
    (σ : JointStudy Θ Ω) : (t : Test) → Views Θ Ω (t.leaves i) → Outside Θ Ω
  | .fisher _ design _ alpha, ws =>
    { null := fun θ => (fisherAnalysis design.model.sizes alpha).hypothesis (ws.1.parameter θ)
      reject :=
        ws.1.outcome ⁻¹' (fisherAnalysis design.model.sizes alpha).procedure.rejectionEvent
      slack := 0 }
  | .assumed name _ design null _, ws =>
    { null := fun θ => null.denote i.laws design.model (ws.1.parameter θ)
      reject := ws.1.outcome ⁻¹' (i.test name design.model).reject
      slack := i.slack name }
  | .associated name _ design _ _ _, ws =>
    { null := fun θ => (i.studies design.model).model.noAssociation (ws.1.parameter θ)
      reject := ws.1.outcome ⁻¹' (i.studyTest name design.model).reject
      slack := i.slack name }
  | .bonferroni _ members _, ws =>
    { null := fun θ => ∃ k, (Test.members i σ members ws).nulls k θ
      reject := ⋂ k, (Test.members i σ members ws).rejects k
      slack := ∑ k, (Test.members i σ members ws).slacks k }
  | .graphical name members _ _ _, ws =>
    { null := fun θ => ∃ k, (Test.members i σ members ws).nulls k θ
      reject := ⋂ k, i.graph name (Test.leavesOf i members) members.length Θ Ω σ ws k
      slack := i.slack name }
  | .sequence _ members _, ws =>
    { null := fun θ => ∃ k, (Test.members i σ members ws).nulls k θ
      reject := ⋂ k, (Test.members i σ members ws).rejects k
      slack := ∑ k, (Test.members i σ members ws).slacks k }
termination_by structural t => t

def Test.members (i : Instance) {Θ Ω : Type} [MeasurableSpace Ω]
    (σ : JointStudy Θ Ω) : (ts : List Test) → Views Θ Ω (Test.leavesOf i ts) →
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
  | .fisher _ design _ alpha =>
    ((fisherAnalysis design.model.sizes alpha).typeIClaim (Core.Compatibility.fixed _)
      (alpha.value : ℝ)).statement
  | .assumed name guarantee design null alpha =>
    typeIClaim (Core.Compatibility.fixed (design.model.view i.laws).base)
      (null.denote i.laws design.model) (i.test name design.model)
      (match guarantee.scope with
        | .finiteSample => (alpha.value : ℝ)
        | .largeSample => (alpha.value : ℝ) + i.slack name)
  | .associated name method design _ alpha _ =>
    typeIClaim (Core.Compatibility.fixed (i.studies design.model).view.base)
      (i.studies design.model).model.noAssociation (i.studyTest name design.model)
      (match method.scope with
        | .finiteSample => (alpha.value : ℝ)
        | .largeSample => (alpha.value : ℝ) + i.slack name)
  | _ => False

/-- The familywise claim of a combination, over every joint study whose marginals are
its members' laws. -/
def Test.familywise (i : Instance) : Test → Prop
  | .bonferroni _ members alpha =>
    Joint (Test.leavesOf i members) fun σ ws =>
      familywiseClaim σ.law ((Test.members i σ members ws).nulls)
        ((Test.members i σ members ws).rejects)
        ((alpha.value : ℝ) + ∑ k, (Test.members i σ members ws).slacks k)
  | .graphical name members _ _ alpha =>
    Joint (Test.leavesOf i members) fun σ ws =>
      familywiseClaim σ.law ((Test.members i σ members ws).nulls)
        (i.graph name (Test.leavesOf i members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack name)
  | .sequence _ members alpha =>
    Joint (Test.leavesOf i members) fun σ ws =>
      sequenceClaim σ.law ((Test.members i σ members ws).nulls)
        ((Test.members i σ members ws).rejects)
        ((alpha.value : ℝ) + ∑ k, (Test.members i σ members ws).slacks k)
  | _ => False

mutual
/-- Every single test in a test stops at fixed sizes, so its design supplies the model's
law. -/
def Test.fixed : Test → Bool
  | .fisher _ design .. => design.stopping == .fixed
  | .assumed _ _ design .. => design.stopping == .fixed
  | .associated _ _ design .. => design.stopping == .fixed
  | .bonferroni _ members _ => Test.allFixed members
  | .graphical _ members _ _ _ => Test.allFixed members
  | .sequence _ members _ => Test.allFixed members
termination_by structural t => t

def Test.allFixed : List Test → Bool
  | [] => true
  | t :: ts => Test.fixed t && Test.allFixed ts
termination_by structural ts => ts
end

/-- What a request claims. A design that stops by a rule depending on the data supplies
no sampling law, so no claim about it can be stated: such a request claims `False`. -/
def Request.Holds (i : Instance) (request : Request) : Prop :=
  match request.test.fixed with
  | true =>
    match request with
    | .typeI t => t.typeI i
    | .familywise t => t.familywise i
  | false => False

inductive Premise where
  | level (name : String) (guarantee : Guarantee) (model : Model) (null : Null)
      (alpha : SignificanceLevel)
  | association (name : String) (method : Generated.AssociationMethod) (study : Study)
      (alpha : SignificanceLevel)
  | graph (name : String) (members : List Test) (alpha : SignificanceLevel)

def Premise.name : Premise → String
  | .level name .. => name
  | .association name .. => name
  | .graph name .. => name

def Test.finiteSample : Test → Bool
  | .fisher .. => true
  | .assumed _ guarantee .. => guarantee.scope == .finiteSample
  | .associated _ method .. => method.scope == .finiteSample
  | _ => false

/-- What a premise assumes: an assumed test's level, or a graph's familywise bound. -/
def Premise.Holds (i : Instance) : Premise → Prop
  | .level name guarantee model null alpha =>
    LevelPremise guarantee.scope (model.view i.laws).base.law (null.denote i.laws model)
      (i.test name model) alpha.value (i.slack name)
  | .association name method study alpha =>
    LevelPremise method.scope (i.studies study).model.law (i.studies study).model.noAssociation
      (i.studyTest name study) alpha.value (i.slack name)
  | .graph name members alpha =>
    (match members.all Test.finiteSample with
      | true => Scope.finiteSample
      | false => Scope.largeSample).permits (i.slack name) ∧
    Joint (Test.leavesOf i members) fun σ ws =>
      familywiseClaim σ.law ((Test.members i σ members ws).nulls)
        (i.graph name (Test.leavesOf i members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack name)

mutual
def Test.premises : Test → List Premise
  | .fisher .. => []
  | .assumed name guarantee design null alpha => [.level name guarantee design.model null alpha]
  | .associated name method design _ alpha _ => [.association name method design.model alpha]
  | .bonferroni _ members _ => Test.premisesOf members
  | .graphical name members _ _ alpha => Test.premisesOf members ++ [.graph name members alpha]
  | .sequence _ members _ => Test.premisesOf members
termination_by structural t => t

def Test.premisesOf : List Test → List Premise
  | [] => []
  | t :: ts => Test.premises t ++ Test.premisesOf ts
termination_by structural ts => ts
end

/-- Every listed premise holds. -/
def Premise.AllHold (i : Instance) : List Premise → Prop
  | [] => True
  | q :: qs => q.Holds i ∧ Premise.AllHold i qs

def Program.claimAt (p : Program) (r : ℕ) (i : Instance) : Prop :=
  match p.requests[r]? with
  | some q => q.Holds i
  | none => False

/-- The premises of the tests request `r` involves. -/
def Program.premisesAt (p : Program) (r : ℕ) : List Premise :=
  match p.requests[r]? with
  | some q => q.test.premises
  | none => []

/-- What a certificate proves of request `r`: it holds for every instance meeting the
premises of the tests it involves. -/
def Program.Claim (p : Program) (r : ℕ) : Prop :=
  ∀ i, Premise.AllHold i (p.premisesAt r) → p.claimAt r i

end

end StatClaim.Semantics
