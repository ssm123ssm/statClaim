import StatClaim

/-!
The printed form of a program determines it. These examples pin the statement the audit
relies on and show the printer's own checks.
-/

open StatClaim.Semantics

-- Two programs in canonical form that print the same form are the same program.
example : ∀ {p q : Program}, p.Canonical → q.Canonical → p.form = q.form → p = q :=
  Program.form_injective

-- Rationals print as Python's `str(Fraction)` writes them, and never alike.
#guard ratString (-1 / 10) == "-1/10"
#guard ratString 3 == "3"
#guard ratString 0 == "0"
example : Function.Injective ratString := ratString_injective

-- The printer refuses an object whose keys do not increase.
example : (Form.obj [("b", .null), ("a", .null)]).json?.isNone = true := by decide
example : (Form.obj [("a", .null), ("b", .null)]).json?.isSome = true := by decide
example : (Form.obj [("a", .null), ("a", .null)]).json?.isNone = true := by decide

-- An absent entry is left out of an object.
example : Form.object [("a", none), ("b", some .null)] = .obj [("b", .null)] := rfl
