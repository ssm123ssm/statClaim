module

public import StatProof.Core.Objects

/-!
Strong familywise error control by composing marginal Type I bounds on a common
sampling law. No independence between tests or truth of every null is required.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.Bonferroni

open MeasureTheory

structure Family (m : ℕ) (Parameter Outcome : Type) [MeasurableSpace Outcome] where
  samplingLaw : Core.SamplingLaw Parameter Outcome
  hypothesis : Fin m → Parameter → Prop
  rejectionEvent : Fin m → Set Outcome
  rejection_measurable : ∀ i, MeasurableSet (rejectionEvent i)
  budget : Fin m → ℝ
  budget_nonnegative : ∀ i, 0 ≤ budget i

variable {m : ℕ} {Parameter Outcome : Type} [MeasurableSpace Outcome]

/-- The event of at least one rejection of a true null, at this parameter. -/
def Family.falseRejectionEvent (family : Family m Parameter Outcome) (parameter : Parameter) :
    Set Outcome :=
  ⋃ i, {outcome | family.hypothesis i parameter ∧ outcome ∈ family.rejectionEvent i}

def Family.marginalBounds (family : Family m Parameter Outcome) : Prop :=
  ∀ i parameter, family.hypothesis i parameter →
    (family.samplingLaw.law parameter).real (family.rejectionEvent i) ≤ family.budget i

def Family.familywiseClaim (family : Family m Parameter Outcome) (alpha : ℝ) : Core.Claim :=
  ⟨∀ parameter, (family.samplingLaw.law parameter).real
    (family.falseRejectionEvent parameter) ≤ alpha⟩

structure FamilywiseGuarantee (family : Family m Parameter Outcome) (alpha : ℝ) : Type where
  certificate : Core.Certificate (family.familywiseClaim alpha)

/-- Union bound over the true nulls, valid also when some or all nulls are false. -/
theorem strong_control (family : Family m Parameter Outcome) (bounds : family.marginalBounds)
    (alpha : ℝ) (allocation : ∑ i, family.budget i ≤ alpha) :
    (family.familywiseClaim alpha).statement := by
  classical
  intro parameter
  change (family.samplingLaw.law parameter).real (⋃ i,
    {outcome | family.hypothesis i parameter ∧ outcome ∈ family.rejectionEvent i}) ≤ alpha
  apply le_trans (measureReal_iUnion_fintype_le _)
  apply le_trans _ allocation
  apply Finset.sum_le_sum
  intro i _
  by_cases null : family.hypothesis i parameter
  · simpa only [null, true_and, Set.ofPred_mem_eq] using bounds i parameter null
  · simpa only [null, false_and, Set.ofPred_false, measureReal_empty] using
      family.budget_nonnegative i

/-- The provider requires both marginal proofs and an adequate total budget. -/
noncomputable def module (m : ℕ) (Parameter Outcome : Type) [MeasurableSpace Outcome]
    (alpha : ℝ) : Core.Module (Family m Parameter Outcome) where
  name := "multiplicity.bonferroni"
  version := "0.1.0"
  Requires := fun family => family.marginalBounds ∧ ∑ i, family.budget i ≤ alpha
  Output := fun family => FamilywiseGuarantee family alpha
  provide := fun family requirement => ⟨⟨strong_control family requirement.1 alpha requirement.2⟩⟩

end StatProof.Modules.Bonferroni
