module

public import StatClaim.Design
public import StatClaim.Generated.Methods
public import StatClaim.Interface.Premises

/-!
A compiled program as Lean data: its models, designs, nulls, tests and requested
claims, field for field as in the canonical program a certificate binds. A key the
canonical program writes only when it is declared is an `Option` or a list here, so
two different programs never have the same canonical form (`Encode`).

Tests are identified by name, and models by everything they declare, as the Python
compiler identifies them.

Trusted: with `Meaning`, `Contracts` and `Grades`, this decides what a certificate
says. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

instance : DecidableEq FixedSampleDesign := fun a b =>
  decidable_of_iff (a.nControl = b.nControl ∧ a.nTreatment = b.nTreatment) (by
    cases a; cases b; simp)

/-- A two-arm model as declared: its outcome, its arm sizes, and whatever else the file
declares about the assignment and the outcome. -/
structure Model where
  outcome : Generated.OutcomeKind
  sizes : FixedSampleDesign
  /-- Clusters per arm, when whole clusters were assigned. -/
  clusters : Option (ℕ × ℕ) := none
  randomisation : Option String := none
  /-- Randomised units per arm in each stratum, when strata are declared. -/
  strata : List (ℕ × ℕ) := []
  blockSize : Option ℕ := none
  population : Option String := none
  better : Option String := none
  /-- Measurements per participant, when there is more than one. -/
  measurements : Option ℕ := none
  /-- The outcome's name, when the file gives one. -/
  name : Option String := none
  deriving DecidableEq

/-- How a design stops: at its fixed sizes, or by a rule that depends on the data. -/
inductive Stopping where
  | fixed
  | data_dependent
  deriving DecidableEq, Repr

structure Design where
  model : Model
  stopping : Stopping
  deriving DecidableEq

/-- A null form, the model it is about, and its value when the form takes one. -/
structure Null where
  key : Generated.NullKey
  model : Model
  value : Option ℚ := none
  deriving DecidableEq

/-- Where an assumed test's guarantee comes from: a method in the registry, or the
author's own declaration, with the scope and references the file gives. -/
inductive Guarantee where
  | cited (method : Generated.TrialMethod)
  | declared (method : String) (scope : Interface.Scope) (references : List String)

def Guarantee.scope : Guarantee → Interface.Scope
  | .cited method => method.scope
  | .declared _ scope _ => scope

inductive Test where
  | fisher (name : String) (design : Design) (null : Null) (alpha : SignificanceLevel)
  /-- A test whose level is a premise: cited from the registry or declared by the author. -/
  | assumed (name : String) (guarantee : Guarantee) (design : Design) (null : Null)
      (alpha : SignificanceLevel)
  | bonferroni (name : String) (members : List Test) (alpha : SignificanceLevel)
  | graphical (name : String) (members : List Test) (weights : List ℚ)
      (transitions : List (List ℚ)) (alpha : SignificanceLevel)
  | sequence (name : String) (members : List Test) (alpha : SignificanceLevel)

inductive Request where
  | typeI (test : Test)
  | familywise (test : Test)

/-- A program's `verify` requests, in order. -/
structure Program where
  requests : List Request

def Request.test : Request → Test
  | .typeI t => t
  | .familywise t => t

def Test.name : Test → String
  | .fisher name .. => name
  | .assumed name .. => name
  | .bonferroni name .. => name
  | .graphical name .. => name
  | .sequence name .. => name

def Test.alpha : Test → ℚ
  | .fisher _ _ _ alpha => alpha.value
  | .assumed _ _ _ _ alpha => alpha.value
  | .bonferroni _ _ alpha => alpha.value
  | .graphical _ _ _ _ alpha => alpha.value
  | .sequence _ _ alpha => alpha.value

end StatClaim.Semantics
