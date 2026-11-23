module

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Aesop

/-!
The `statclaim` tactic, which proves what remains of a translated claim once the
translator has named its composition rule: the obligations about each member,
the arithmetic on levels, and the case split over members.

It first turns statements about every member of a family, written with `![…]`,
into one statement per member, in the goal and in the hypotheses alike, then
searches with Aesop, using the hypotheses in context, `norm_num` for numbers and
`linarith` for sums of slacks.
It never proves anything the kernel does not check, and when it fails the claim
stays unresolved.
-/

@[expose] public section

/-- Prove a translated claim's remaining obligations. -/
macro "statclaim" : tactic => `(tactic| (
  try simp only [Fin.forall_fin_succ, Fin.exists_fin_succ, IsEmpty.forall_iff,
    IsEmpty.exists_iff, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, and_true, or_false] at *
  aesop (add unsafe tactic (by norm_num), unsafe tactic (by linarith))))
