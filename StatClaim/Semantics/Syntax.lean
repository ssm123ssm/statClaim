module

public import StatClaim.Design
public import StatClaim.Generated.Methods

/-!
A compiled program as Lean data: its models, nulls, tests and requested claims, as
in the canonical program a certificate binds. Tests are identified by name, and
continuous models by their arm sizes, as the Python translator identifies them.

Trusted: with `Meaning`, `Contracts` and `Grades`, this decides what a certificate
says. See docs/proposals/lean-semantics.md.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface

/-- A two-arm model: binomial, with the law Lean defines, or continuous, with a law the
instance supplies for each pair of arm sizes. -/
inductive Model where
  | binomial (sizes : FixedSampleDesign)
  | continuous (control treatment : ℕ)

/-- A null form and its value; a form without a value uses zero. -/
structure Null where
  key : Generated.NullKey
  value : ℚ

inductive Test where
  | fisher (name : String) (sizes : FixedSampleDesign) (null : Null) (alpha : SignificanceLevel)
  | cited (name : String) (method : Generated.TrialMethod) (model : Model) (null : Null)
      (alpha : SignificanceLevel)
  | bonferroni (name : String) (members : List Test) (alpha : SignificanceLevel)
  | graphical (name : String) (members : List Test) (weights : List ℚ)
      (transitions : List (List ℚ)) (alpha : SignificanceLevel)
  | sequence (name : String) (members : List Test) (alpha : SignificanceLevel)

inductive Request where
  | typeI (test : Test)
  | familywise (test : Test)

structure Program where
  requests : List Request

def Request.test : Request → Test
  | .typeI t => t
  | .familywise t => t

def Test.name : Test → String
  | .fisher name .. => name
  | .cited name .. => name
  | .bonferroni name .. => name
  | .graphical name .. => name
  | .sequence name .. => name

def Test.alpha : Test → ℚ
  | .fisher _ _ _ alpha => alpha.value
  | .cited _ _ _ _ alpha => alpha.value
  | .bonferroni _ _ alpha => alpha.value
  | .graphical _ _ _ _ alpha => alpha.value
  | .sequence _ _ alpha => alpha.value

end StatClaim.Semantics
