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

/-- In a fixed sequence, a null is rejected only if its own test and every earlier
test reject. This is the event that some true null is rejected. -/
def sequenceFalseRejection (trueNull : Fin m → Prop) (reject : Fin m → Set Outcome) :
    Set Outcome :=
  {outcome | ∃ k, trueNull k ∧ ∀ i, i ≤ k → outcome ∈ reject i}

/-- Testing in a fixed order, each test at the full level and only after every
earlier test rejected, rejects some true null with probability at most that level
plus the slack. A false rejection needs the first true null's own test to reject. -/
theorem fixed_sequence_le (law : Measure Outcome) [IsProbabilityMeasure law]
    (trueNull : Fin m → Prop) (reject : Fin m → Set Outcome) (alpha slack : ℝ)
    (alpha_nonnegative : 0 ≤ alpha) (slack_nonnegative : 0 ≤ slack)
    (marginal : ∀ i, trueNull i → law.real (reject i) ≤ alpha + slack) :
    law.real (sequenceFalseRejection trueNull reject) ≤ alpha + slack := by
  classical
  by_cases some : ∃ k, trueNull k
  · obtain ⟨first, first_true, first_least⟩ : ∃ j, trueNull j ∧ ∀ k, trueNull k → j ≤ k := by
      let trueNulls := Finset.univ.filter (fun k => trueNull k)
      have nonempty : trueNulls.Nonempty := by
        obtain ⟨k, hk⟩ := some
        exact ⟨k, by simp [trueNulls, hk]⟩
      refine ⟨trueNulls.min' nonempty, ?_, ?_⟩
      · have member := Finset.min'_mem trueNulls nonempty
        simpa [trueNulls] using member
      · intro k hk
        exact Finset.min'_le trueNulls k (by simp [trueNulls, hk])
    have subset : sequenceFalseRejection trueNull reject ⊆ reject first := by
      rintro outcome ⟨k, hk, all⟩
      exact all first (first_least k hk)
    exact le_trans (measureReal_mono subset) (marginal first first_true)
  · have empty : sequenceFalseRejection trueNull reject = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro outcome ⟨k, hk, _⟩
      exact some ⟨k, hk⟩
    rw [empty, measureReal_empty]
    exact add_nonneg alpha_nonnegative slack_nonnegative

/-- The same with exact rational levels, all equal to the sequence's level. -/
theorem fixed_sequence_le_of_levels (law : Measure Outcome) [IsProbabilityMeasure law]
    (trueNull : Fin m → Prop) (reject : Fin m → Set Outcome)
    (levels : Fin m → SignificanceLevel) (slack : ℝ) (slack_nonnegative : 0 ≤ slack)
    (marginal : ∀ i, trueNull i → law.real (reject i) ≤ ((levels i).value : ℝ) + slack)
    (alpha : ℚ) (alpha_nonnegative : 0 ≤ alpha) (full_level : ∀ i, (levels i).value = alpha) :
    law.real (sequenceFalseRejection trueNull reject) ≤ (alpha : ℝ) + slack := by
  apply fixed_sequence_le law trueNull reject (alpha : ℝ) slack
    (by exact_mod_cast alpha_nonnegative) slack_nonnegative
  intro i null
  have bound := marginal i null
  rwa [full_level i] at bound

end StatClaim.Modules.Composition
