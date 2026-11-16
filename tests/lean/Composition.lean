import StatClaim

namespace StatClaim.Tests.Composition

open Core Modules MeasureTheory

def sizes : FixedSampleDesign := ⟨4, 4, by decide, by decide⟩
def level : SignificanceLevel := ⟨1 / 40, by norm_num, by norm_num⟩

-- All levels in the closed unit interval are supported by the generic theorem.
example (p : unitInterval) :
    (fisherNullLaw 4 4 p).real (fisherRejectionRegionAt 4 4 0) ≤ (0 : ℝ) := by
  simpa only [Rat.cast_zero] using fisher_typeI_error_le_alpha 4 4 p 0 (by norm_num)
example (p : unitInterval) :
    (fisherNullLaw 4 4 p).real (fisherRejectionRegionAt 4 4 1) ≤ (1 : ℝ) := by
  simpa only [Rat.cast_one] using fisher_typeI_error_le_alpha 4 4 p 1 (by norm_num)

example (level : SignificanceLevel) : level.value ≠ 2 := by
  intro equal
  have bound := level.le_one
  rw [equal] at bound
  norm_num at bound

-- The two events here are identical: maximal dependence does not obstruct
-- Bonferroni. This reuses the same Fisher guarantee twice on the same law.
noncomputable def dependentFamily :
    Bonferroni.Family 2 TwoArmBinomial.Parameters TwoArmBinomial.Counts where
  samplingLaw := (Fisher.fixedGuarantee sizes level).compatibility.samplingLaw
  hypothesis := fun _ => TwoArmBinomial.equalProportions
  rejectionEvent := fun _ => (Fisher.procedure sizes level).rejectionEvent
  rejection_measurable := fun _ => (Fisher.procedure sizes level).rejection_measurable
  budget := fun _ => (level.value : ℝ)
  budget_nonnegative := fun _ => by norm_num [level]

theorem dependent_bounds : dependentFamily.marginalBounds := by
  intro _ parameter null
  exact (Fisher.fixedGuarantee sizes level).certificate.establishes parameter null

noncomputable def dependentGuarantee :
    Bonferroni.FamilywiseGuarantee dependentFamily (1 / 20 : ℝ) :=
  (Bonferroni.module 2 TwoArmBinomial.Parameters TwoArmBinomial.Counts (1 / 20 : ℝ)).provide
    dependentFamily ⟨dependent_bounds, by norm_num [Fin.sum_univ_two, dependentFamily, level]⟩

-- A stricter requested bound is not established by this certificate.
example : True := by
  fail_if_success
    have invalid : Bonferroni.FamilywiseGuarantee dependentFamily (1 / 100 : ℝ) :=
      dependentGuarantee
  trivial

-- The budget obligation fails even though both individual tests have guarantees.
example : ¬ ((1 / 20 : ℝ) + 1 / 20 ≤ 1 / 20) := by norm_num

-- With no true nulls, the false-rejection event is empty.
example (family : Bonferroni.Family 2 Unit ℕ) (parameter : Unit)
    (all_false : ∀ i, ¬ family.hypothesis i parameter) :
    family.falseRejectionEvent parameter = ∅ := by
  ext outcome
  simp [Bonferroni.Family.falseRejectionEvent, all_false]

-- With one true null and one false, only the true-null event is counted.
example (family : Bonferroni.Family 2 Unit ℕ) (parameter : Unit)
    (first_true : family.hypothesis 0 parameter)
    (second_false : ¬ family.hypothesis 1 parameter) :
    family.falseRejectionEvent parameter = family.rejectionEvent 0 := by
  ext outcome
  simp [Bonferroni.Family.falseRejectionEvent, Fin.exists_fin_two, first_true, second_false]

end StatClaim.Tests.Composition
