module

public import StatProof.Core.Policy
public import StatProof.ProductBinomial
public import StatProof.BinomialMonotone

/-!
A single-arm, two-stage binomial design with an interim futility stop. The
potential data are two independent binomial counts with one response rate. The
observed record contains the second count only when the interim rule continues.

Type I error and power are properties of the complete policy. At rational
response rates they are explicit ratios of natural numbers, so a declared
design is checked by kernel arithmetic rather than by a fixed-sample theorem.

Posterior rules use the binomial-sum form of the Beta tail probability for
positive integer prior parameters. That closed form is this module's definition
of the rule; its identity with the Beta integral is standard but not proved here.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.TwoStageBinomial

open MeasureTheory

/-- Stage sizes, the interim continuation rule and the final rejection rule. -/
structure Design where
  nFirst : ℕ
  nSecond : ℕ
  continues : ℕ → Bool
  rejects : ℕ → ℕ → Bool

/-- What is observed: stage two exists only after continuation. -/
inductive Record where
  | stopped (first : ℕ)
  | completed (first second : ℕ)

instance : MeasurableSpace Record := ⊤

/-- Apply the interim rule to the potential counts. -/
def Design.observe (design : Design) (counts : ℕ × ℕ) : Record :=
  if design.continues counts.1 then .completed counts.1 counts.2 else .stopped counts.1

/-- The null is rejected only after a completed second stage. -/
def Design.rejected (design : Design) : Record → Prop
  | .stopped _ => False
  | .completed first second => design.rejects first second = true

/-- The complete policy, parameterized by the common response rate. -/
noncomputable def policy (design : Design) : Core.Policy unitInterval (ℕ × ℕ) Record where
  potentialLaw := fun rate => productBinomial design.nFirst design.nSecond rate rate
  probability := fun _ => inferInstance
  record := design.observe
  record_measurable := .of_discrete

/-- Test a single null response rate against the policy's rejection records. -/
noncomputable def analysis (design : Design) (nullRate : unitInterval) :
    Core.PolicyAnalysis (policy design) where
  hypothesis := fun rate => rate = nullRate
  rejection := {record | design.rejected record}
  rejection_measurable := MeasurableSpace.measurableSet_top

/-- Continue and then reject, as one rule on the potential counts. -/
def Design.rejectRule (design : Design) (first second : ℕ) : Bool :=
  design.continues first && design.rejects first second

theorem rejection_preimage (design : Design) (counts : ℕ × ℕ) :
    counts ∈ design.observe ⁻¹' {record | design.rejected record} ↔
      design.rejectRule counts.1 counts.2 = true := by
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Design.observe, Design.rejectRule,
    Bool.and_eq_true]
  by_cases continued : design.continues counts.1 = true
  · simp [continued, Design.rejected]
  · simp [continued, Design.rejected]

/-- Exact rejection probability of the complete policy at a rational rate. -/
theorem rejection_probability (design : Design) (a d : ℕ) (le : a ≤ d) (positive : 0 < d) :
    ((policy design).law (ratPoint a d le positive)).real {record | design.rejected record} =
      (rejectionNumerator design.nFirst design.nSecond a d a d design.rejectRule : ℝ) /
        (rejectionDenominator design.nFirst design.nSecond d d : ℝ) := by
  rw [Core.Policy.law_real_apply _ _ MeasurableSpace.measurableSet_top,
    rejectionDenominator_cast]
  exact productBinomial_real_ratPoint _ _ a d a d le positive le positive _ _
    (fun first _ second _ => rejection_preimage design (first, second))

/-- Type I error at the declared null rate, from one natural-number check. -/
theorem typeI_of_check (design : Design) (a d : ℕ) (le : a ≤ d) (positive : 0 < d)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : rejectionNumerator design.nFirst design.nSecond a d a d design.rejectRule * boundDen ≤
      boundNum * rejectionDenominator design.nFirst design.nSecond d d) :
    ((analysis design (ratPoint a d le positive)).typeIClaim
      ((boundNum : ℝ) / boundDen)).statement := by
  intro rate null
  rw [show rate = ratPoint a d le positive from null]
  change ((policy design).law _).real {record | design.rejected record} ≤ _
  rw [rejection_probability]
  exact ratio_le_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive positive)
    boundDen_pos check

/-- Power at one declared response rate, from one natural-number check. -/
theorem power_of_check (design : Design) (nullRate : unitInterval) (a d : ℕ) (le : a ≤ d)
    (positive : 0 < d) (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * rejectionDenominator design.nFirst design.nSecond d d ≤
      rejectionNumerator design.nFirst design.nSecond a d a d design.rejectRule * boundDen) :
    ((analysis design nullRate).powerClaim (fun rate => rate = ratPoint a d le positive)
      ((boundNum : ℝ) / boundDen)).statement := by
  intro rate alternative
  rw [show rate = ratPoint a d le positive from alternative]
  change _ ≤ ((policy design).law _).real {record | design.rejected record}
  rw [rejection_probability]
  exact le_ratio_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive positive)
    boundDen_pos check

/-- Count thresholds: continue above `interim`, reject above `final` in total. -/
def thresholdDesign (nFirst nSecond interim final : ℕ) : Design where
  nFirst := nFirst
  nSecond := nSecond
  continues := fun first => decide (interim < first)
  rejects := fun first second => decide (final < first + second)

/-- Null: the response rate is at most the reference rate. -/
noncomputable def analysisAtMost (design : Design) (nullRate : unitInterval) :
    Core.PolicyAnalysis (policy design) where
  hypothesis := fun rate => rate ≤ nullRate
  rejection := {record | design.rejected record}
  rejection_measurable := MeasurableSpace.measurableSet_top

/-- More responses in either stage never turn a rejection into a non-rejection. -/
def Design.Monotone (design : Design) : Prop :=
  ∀ first first' second second', first ≤ first' → second ≤ second' →
    design.rejectRule first second = true → design.rejectRule first' second' = true

/-- For a monotone rule, a check at the reference rate bounds Type I error at
every smaller rate. -/
theorem typeI_atMost_of_check (design : Design) (monotone : design.Monotone) (a d : ℕ)
    (le : a ≤ d) (positive : 0 < d) (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : rejectionNumerator design.nFirst design.nSecond a d a d design.rejectRule * boundDen ≤
      boundNum * rejectionDenominator design.nFirst design.nSecond d d) :
    ((analysisAtMost design (ratPoint a d le positive)).typeIClaim
      ((boundNum : ℝ) / boundDen)).statement := by
  intro rate null
  refine le_trans ?_ (typeI_of_check design a d le positive boundNum boundDen boundDen_pos check
    (ratPoint a d le positive) rfl)
  change ((policy design).law rate).real {record | design.rejected record} ≤
    ((policy design).law _).real {record | design.rejected record}
  rw [Core.Policy.law_real_apply _ _ MeasurableSpace.measurableSet_top,
    Core.Policy.law_real_apply _ _ MeasurableSpace.measurableSet_top]
  refine productBinomial_real_mono _ _ rate _ null _ ?_
  intro lower higher first second member
  exact (rejection_preimage design higher).mpr
    (monotone _ _ _ _ first second ((rejection_preimage design lower).mp member))

/-- Power at one declared rate, for the analysis with the composite null. -/
theorem power_atMost_of_check (design : Design) (nullRate : unitInterval) (a d : ℕ) (le : a ≤ d)
    (positive : 0 < d) (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * rejectionDenominator design.nFirst design.nSecond d d ≤
      rejectionNumerator design.nFirst design.nSecond a d a d design.rejectRule * boundDen) :
    ((analysisAtMost design nullRate).powerClaim (fun rate => rate = ratPoint a d le positive)
      ((boundNum : ℝ) / boundDen)).statement :=
  power_of_check design nullRate a d le positive boundNum boundDen boundDen_pos check

theorem thresholdDesign_monotone (nFirst nSecond interim final : ℕ) :
    (thresholdDesign nFirst nSecond interim final).Monotone := by
  intro first first' second second' first_le second_le
  simp only [Design.rejectRule, thresholdDesign, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Numerator of the posterior probability that the rate exceeds `rateNum/rateDen`
under a Beta(a, b) distribution with positive integer parameters; the
denominator is `rateDen ^ (a + b - 1)`. -/
def betaTailNumerator (a b rateNum rateDen : ℕ) : ℕ :=
  ∑ j ∈ Finset.range a,
    Nat.fast_choose (a + b - 1) j * rateNum ^ j * (rateDen - rateNum) ^ (a + b - 1 - j)

/-- Whether the posterior tail probability after the given data is at least
`levelNum/levelDen`, for a Beta(priorA, priorB) prior. Successes are capped at
the number of trials, which changes nothing for possible data. -/
def posteriorAtLeast (priorA priorB rateNum rateDen levelNum levelDen successes trials : ℕ) :
    Bool :=
  decide (levelNum * rateDen ^ (priorA + priorB + trials - 1) ≤
    betaTailNumerator (priorA + min successes trials)
      (priorB + (trials - min successes trials)) rateNum rateDen * levelDen)

theorem betaTailNumerator_mono (a a' b b' rateNum rateDen : ℕ) (le : a ≤ a')
    (total : a + b = a' + b') :
    betaTailNumerator a b rateNum rateDen ≤ betaTailNumerator a' b' rateNum rateDen := by
  unfold betaTailNumerator
  rw [total]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono le)

/-- More successes in the same number of trials never lower the posterior tail. -/
theorem posteriorAtLeast_mono (priorA priorB rateNum rateDen levelNum levelDen : ℕ)
    (successes successes' trials : ℕ) (le : successes ≤ successes')
    (holds : posteriorAtLeast priorA priorB rateNum rateDen levelNum levelDen successes trials =
      true) :
    posteriorAtLeast priorA priorB rateNum rateDen levelNum levelDen successes' trials = true := by
  simp only [posteriorAtLeast, decide_eq_true_eq] at holds ⊢
  refine holds.trans (Nat.mul_le_mul_right _ (betaTailNumerator_mono _ _ _ _ _ _ ?_ ?_))
  · omega
  · omega

/-- Posterior thresholds at the interim and final analyses. -/
def posteriorDesign (nFirst nSecond priorA priorB rateNum rateDen
    continueNum continueDen successNum successDen : ℕ) : Design where
  nFirst := nFirst
  nSecond := nSecond
  continues := fun first =>
    posteriorAtLeast priorA priorB rateNum rateDen continueNum continueDen first nFirst
  rejects := fun first second =>
    posteriorAtLeast priorA priorB rateNum rateDen successNum successDen
      (first + second) (nFirst + nSecond)

theorem posteriorDesign_monotone (nFirst nSecond priorA priorB rateNum rateDen
    continueNum continueDen successNum successDen : ℕ) :
    (posteriorDesign nFirst nSecond priorA priorB rateNum rateDen
      continueNum continueDen successNum successDen).Monotone := by
  intro first first' second second' first_le second_le holds
  simp only [Design.rejectRule, posteriorDesign, Bool.and_eq_true] at holds ⊢
  exact ⟨posteriorAtLeast_mono _ _ _ _ _ _ _ _ _ first_le holds.1,
    posteriorAtLeast_mono _ _ _ _ _ _ _ _ _ (by omega) holds.2⟩

end StatProof.Modules.TwoStageBinomial
