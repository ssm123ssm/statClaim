module

public import StatClaim.Core.Objects
public import StatClaim.Design

/-!
Combining error bounds that are assumed, not proved here.

The union bound needs nothing about the tests except their marginal error
bounds. This lets a family mix proved and cited tests: each bound enters as a
hypothesis and only the combination is proved. The slack terms cover bounds that
hold approximately, so one theorem serves finite-sample and large-sample members.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Composition

open MeasureTheory

variable {m : ℕ} {Outcome : Type} [MeasurableSpace Outcome]

/-- At least one true null is rejected. -/
def falseRejection (trueNull : Fin m → Prop) (reject : Fin m → Set Outcome) : Set Outcome :=
  ⋃ i, {outcome | trueNull i ∧ outcome ∈ reject i}

/-- If every true null is rejected with probability at most its level plus a slack,
some true null is rejected with probability at most the levels' total plus the
slacks' total. Dependence between the tests is unrestricted. -/
theorem familywise_le (law : Measure Outcome) [IsProbabilityMeasure law]
    (trueNull : Fin m → Prop) (reject : Fin m → Set Outcome) (level slack : Fin m → ℝ)
    (level_nonnegative : ∀ i, 0 ≤ level i) (slack_nonnegative : ∀ i, 0 ≤ slack i)
    (marginal : ∀ i, trueNull i → law.real (reject i) ≤ level i + slack i)
    (alpha : ℝ) (allocation : ∑ i, level i ≤ alpha) :
    law.real (falseRejection trueNull reject) ≤ alpha + ∑ i, slack i := by
  classical
  unfold falseRejection
  apply le_trans (measureReal_iUnion_fintype_le _)
  have total : ∑ i, (level i + slack i) ≤ alpha + ∑ i, slack i := by
    rw [Finset.sum_add_distrib]
    linarith
  apply le_trans _ total
  apply Finset.sum_le_sum
  intro i _
  by_cases null : trueNull i
  · simpa only [null, true_and, Set.ofPred_mem_eq] using marginal i null
  · simpa only [null, false_and, Set.ofPred_false, measureReal_empty] using
      add_nonneg (level_nonnegative i) (slack_nonnegative i)

/-- The same with exact rational levels, as a generated certificate states them. -/
theorem familywise_le_of_levels (law : Measure Outcome) [IsProbabilityMeasure law]
    (trueNull : Fin m → Prop) (reject : Fin m → Set Outcome)
    (levels : Fin m → SignificanceLevel) (slack : Fin m → ℝ)
    (slack_nonnegative : ∀ i, 0 ≤ slack i)
    (marginal : ∀ i, trueNull i → law.real (reject i) ≤ ((levels i).value : ℝ) + slack i)
    (alpha : ℚ) (allocation : ∑ i, (levels i).value ≤ alpha) :
    law.real (falseRejection trueNull reject) ≤ (alpha : ℝ) + ∑ i, slack i := by
  apply familywise_le law trueNull reject (fun i => ((levels i).value : ℝ)) slack
    (fun i => by exact_mod_cast (levels i).nonnegative) slack_nonnegative marginal
  exact_mod_cast allocation

end StatClaim.Modules.Composition
