module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.NormNum

/-!
Probability-ordered p-values on a finite set with nonnegative rational masses.
Normalization is not needed for the bound itself. When the masses sum to one,
the sum of rejected masses is a rejection probability.

This generic theorem does not yet connect binomial sampling, hypergeometric
weights, or the Python implementation to these definitions.
-/

@[expose] public section

namespace StatProof

/-- Sum the masses of all outcomes no more likely than the observed outcome.
Equality is included, so all ties are counted. -/
def probabilityOrderedPValue {ι : Type*} (support : Finset ι) (mass : ι → ℚ)
    (observed : ι) : ℚ :=
  ∑ outcome ∈ support.filter (fun outcome => mass outcome ≤ mass observed), mass outcome

/-- Rejection at a nonnegative threshold has mass at most that threshold.
For a normalized finite probability distribution, this is the Type I error
bound for its probability-ordered p-value, including ties. -/
theorem probabilityOrdered_rejection_mass_le {ι : Type*}
    (support : Finset ι) (mass : ι → ℚ)
    (nonnegative : ∀ outcome ∈ support, 0 ≤ mass outcome)
    (alpha : ℚ) (alpha_nonnegative : 0 ≤ alpha) :
    (∑ outcome ∈ support.filter
      (fun outcome => probabilityOrderedPValue support mass outcome ≤ alpha), mass outcome)
      ≤ alpha := by
  classical
  let rejected := support.filter
    (fun outcome => probabilityOrderedPValue support mass outcome ≤ alpha)
  change (∑ outcome ∈ rejected, mass outcome) ≤ alpha
  by_cases inhabited : rejected.Nonempty
  · obtain ⟨observed, observed_mem, maximal⟩ := rejected.exists_max_image mass inhabited
    have subset : rejected ⊆ support.filter (fun outcome => mass outcome ≤ mass observed) := by
      intro outcome outcome_mem
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp outcome_mem).1, maximal outcome outcome_mem⟩
    calc
      (∑ outcome ∈ rejected, mass outcome)
          ≤ probabilityOrderedPValue support mass observed := by
        unfold probabilityOrderedPValue
        exact Finset.sum_le_sum_of_subset_of_nonneg subset
          (fun outcome outcome_mem _ => nonnegative outcome (Finset.mem_filter.mp outcome_mem).1)
      _ ≤ alpha := (Finset.mem_filter.mp observed_mem).2
  · have empty : rejected = ∅ := Finset.not_nonempty_iff_eq_empty.mp inhabited
    simpa [empty] using alpha_nonnegative

end StatProof
