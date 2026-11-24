set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨100, 100, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def plan :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def plan_compatible :
    StatClaim.Core.Compatibility plan :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.equalProportions

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis study_sizes plan analysis_level

-- Contract facts the Python compiler checks, decided by Lean.

theorem analysis_null :
    ∀ parameter, null parameter ↔ analysis.hypothesis parameter :=
  fun parameter => Iff.rfl

theorem analysis_contract :
    (StatClaim.Modules.Fisher.module study_sizes analysis_level).Requires
      plan :=
  ⟨plan_compatible⟩

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

namespace request_2_claim_checks

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open StatClaim

theorem checked_counts : 0 < 100 ∧ 0 < 100 ∧ 10 ≤ 100 ∧ 25 ≤ 100 := by decide

theorem checked_support (k : ℕ) :
    k ∈ hypergeometricSupport 100 100 35 ↔
      0 ≤ k ∧ k ≤ 35 := by
  simpa only [show 35 - 100 = 0 from by decide,
    show min 100 35 = 35 from by decide] using
    mem_hypergeometricSupport_iff 100 100 35 k

theorem checked_p_value : hypergeometricPValue 100 100 35 10 =
    (19912805355158606332329 : ℚ) / 2341699062001756564467919 := by
  apply hypergeometricPValue_eq_of_cross_product 100 100 35 10
    19912805355158606332329 2341699062001756564467919 (by decide) (by decide)
  decide +kernel

theorem checked_table_probability : hypergeometricMass 100 100 35 10 =
    (537397138428741731448 : ℚ) / 180130697077058197266763 := by
  apply hypergeometricMass_eq_of_cross_product 100 100 35 10
    537397138428741731448 180130697077058197266763 (by decide) (by decide)
  decide +kernel

theorem checked_decision :
    ((10, 25) ∈ fisherRejectionRegionAt 100 100 ((1 : ℚ) / 20)) ↔ True := by
  simp only [fisherRejectionRegionAt, Finset.mem_filter, binomialCountSupport,
    Finset.mem_product, Finset.mem_range]
  rw [checked_p_value]
  norm_num

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw 100 100 p).real (fisherRejectionRegionAt 100 100 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20) :=
  by
    have bound := fisher_typeI_error_le_alpha 100 100 p ((1 : ℚ) / 20) (by norm_num)
    convert bound using 1 <;> norm_num

end request_2_claim_checks

set_option maxRecDepth 100000 in
theorem request_2_claim (i : Instance) (premises : Premises i) :
    (0 < 100 ∧ 0 < 100 ∧ 10 ≤ 100 ∧ 25 ≤ 100) ∧
    (∀ (k : ℕ),
      k ∈ StatClaim.hypergeometricSupport 100 100 35 ↔
      0 ≤ k ∧ k ≤ 35) ∧
    (StatClaim.hypergeometricPValue 100 100 35 10 =
    (19912805355158606332329 : ℚ) / 2341699062001756564467919) ∧
    (StatClaim.hypergeometricMass 100 100 35 10 =
    (537397138428741731448 : ℚ) / 180130697077058197266763) ∧
    (((10, 25) ∈ StatClaim.fisherRejectionRegionAt 100 100 ((1 : ℚ) / 20)) ↔ True) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 100 100 p).real (StatClaim.fisherRejectionRegionAt 100 100 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20)) :=
  ⟨request_2_claim_checks.checked_counts, request_2_claim_checks.checked_support, request_2_claim_checks.checked_p_value, request_2_claim_checks.checked_table_probability, request_2_claim_checks.checked_decision, request_2_claim_checks.checked_typeI⟩

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (0 < 100 ∧ 0 < 100 ∧ 10 ≤ 100 ∧ 25 ≤ 100) ∧
    (∀ (k : ℕ),
      k ∈ StatClaim.hypergeometricSupport 100 100 35 ↔
      0 ≤ k ∧ k ≤ 35) ∧
    (StatClaim.hypergeometricPValue 100 100 35 10 =
    (19912805355158606332329 : ℚ) / 2341699062001756564467919) ∧
    (StatClaim.hypergeometricMass 100 100 35 10 =
    (537397138428741731448 : ℚ) / 180130697077058197266763) ∧
    (((10, 25) ∈ StatClaim.fisherRejectionRegionAt 100 100 ((1 : ℚ) / 20)) ↔ True) ∧
    (∀ (p : unitInterval),
      (StatClaim.fisherNullLaw 100 100 p).real (StatClaim.fisherRejectionRegionAt 100 100 (( 1 : ℚ) / 20)) ≤
      ((1 : ℝ) / 20))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance := ⟨⟩

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => request_2_claim i premises
  satisfiable := ⟨witness, ⟨⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("request_2_claim", ``request_2_claim)] do
    let found ← IO.mkRef ({} : NameSet)
    let mut seen : NameSet := {}
    let mut stack := [claim]
    while !stack.isEmpty do
      let current := stack.head!
      stack := stack.tail!
      if seen.contains current then continue
      seen := seen.insert current
      let some info := env.find? current | continue
      let value := match info with
        | .thmInfo theorem_ => some theorem_.value
        | .defnInfo definition => some definition.value
        | _ => none
      for e in info.type :: value.toList do
        discard <| liftCoreM <| Core.transform e (pre := fun e => do
          if let .proj name index _ := e then
            if name == structureName then
              if let some field := fields[index]? then found.modify (·.insert field)
          return .continue)
        for constant in e.getUsedConstants do
          if claim.getPrefix.isPrefixOf constant && !seen.contains constant then
            stack := constant :: stack
    let used := (← found.get).toList.map toString |>.mergeSort (· < ·)
    logInfo m!"STATCLAIM_PREMISES examples/fisher_result.stat {short}: {String.intercalate "," used}"
