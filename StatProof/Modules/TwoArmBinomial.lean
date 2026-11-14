module

public import StatProof.Core.Objects
public import StatProof.Fisher

/-!
The first reusable model family: independent binomial counts, with distinct
unknown success probabilities. Equality of probabilities is a separate tested
hypothesis. Positive arm sizes reuse the existing fixed-size specification.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.TwoArmBinomial

open MeasureTheory

abbrev Parameters := unitInterval × unitInterval
abbrev Counts := ℕ × ℕ

/-- Full parameter family, not only its equal-proportions null subfamily. -/
noncomputable def jointLaw (sizes : FixedSampleDesign) (parameter : Parameters) : Measure Counts :=
  (ProbabilityTheory.binomial sizes.nControl parameter.1).prod
    (ProbabilityTheory.binomial sizes.nTreatment parameter.2)

instance jointLaw_probability (sizes : FixedSampleDesign) (parameter : Parameters) :
    IsProbabilityMeasure (jointLaw sizes parameter) := by
  unfold jointLaw
  infer_instance

private theorem binomial_supported (n : ℕ) (p : unitInterval) :
    (ProbabilityTheory.binomial n p).real (Set.Iic n) = 1 := by
  have range_eq : (↑(Finset.range (n + 1)) : Set ℕ) = Set.Iic n := by
    ext k
    simp only [Finset.mem_coe, Finset.mem_range, Set.mem_Iic, Nat.lt_succ_iff]
  rw [← range_eq, ← sum_measureReal_singleton]
  simp only [ProbabilityTheory.binomial_real_singleton]
  exact binomialMass_sum_one n (p : ℝ)

noncomputable def model (sizes : FixedSampleDesign) : Core.Model Parameters Counts where
  law := jointLaw sizes
  probability := jointLaw_probability sizes
  admissible := Set.Iic sizes.nControl ×ˢ Set.Iic sizes.nTreatment
  admissible_measurable := .of_discrete
  supported := fun parameter => by
    rw [jointLaw, measureReal_prod_prod, binomial_supported, binomial_supported, one_mul]

/-- A convenient typed constructor: out-of-range counts require an impossible
bound proof rather than silently becoming observations of another design. -/
def observe (sizes : FixedSampleDesign) (control treatment : ℕ)
    (control_le : control ≤ sizes.nControl) (treatment_le : treatment ≤ sizes.nTreatment) :
    Core.Observation (model sizes) :=
  ⟨(control, treatment), control_le, treatment_le⟩

/-- A parameter restriction for an inference claim; not a premise that the
observed data must establish or an assertion that the null is true. -/
def equalProportions : Core.Hypothesis Parameters :=
  fun parameter => (parameter.1 : ℝ) = (parameter.2 : ℝ)

/-- Restrict the full family to the null law used by the existing Fisher theorem. -/
theorem law_under_null (sizes : FixedSampleDesign) (parameter : Parameters)
    (null : equalProportions parameter) :
    (model sizes).law parameter = fisherNullLaw sizes.nControl sizes.nTreatment parameter.1 := by
  have equal : parameter.2 = parameter.1 := (Subtype.ext null).symm
  change jointLaw sizes parameter = _
  simp only [jointLaw, fisherNullLaw, equal]

end StatProof.Modules.TwoArmBinomial
