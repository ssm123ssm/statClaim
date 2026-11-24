set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨36, 36, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

noncomputable def design :=
  StatClaim.Core.StudyDesign.fixed study

noncomputable def design_compatible :
    StatClaim.Core.Compatibility design :=
  StatClaim.Core.Compatibility.fixed _

def null : StatClaim.Core.Hypothesis StatClaim.Modules.TwoArmBinomial.Parameters :=
  StatClaim.Modules.TwoArmBinomial.proportionDifferenceAtMost (0 : ℚ)

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 40), by norm_num, by norm_num⟩

noncomputable def analysis :=
  StatClaim.Modules.FisherOneSided.analysis study_sizes analysis_level

-- Contract facts the Python compiler checks, decided by Lean.

theorem analysis_null :
    ∀ parameter, null parameter ↔ analysis.hypothesis parameter :=
  fun parameter => Iff.rfl

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

namespace guarantee_claim_checks

def bounds : List ℕ := [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 20, 20, 21, 21, 22, 22, 23, 23, 24, 25, 25, 26, 26, 27, 28, 28, 29, 29, 30, 31, 31, 32, 33, 34, 35, 36]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem region : StatClaim.Modules.FisherOneSided.HintsValid study_sizes.nControl
    study_sizes.nTreatment 1 40 bounds := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem sections : StatClaim.Modules.FisherOneSided.HintSections study_sizes.nControl
    study_sizes.nTreatment bounds := by
  decide +kernel

end guarantee_claim_checks

theorem guarantee_claim (i : Instance) (premises : Premises i) :
    (analysis.typeIClaim (analysis_level.value : ℝ)).statement :=
  StatClaim.Modules.FisherOneSided.typeI_of_hints study_sizes analysis_level 1 40
    (by decide) (by norm_num [analysis_level]) guarantee_claim_checks.bounds guarantee_claim_checks.region guarantee_claim_checks.sections

namespace outcome_claim_checks

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
open StatClaim StatClaim.Modules

def declaredSizes : FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def declaredLevel : SignificanceLevel :=
  ⟨(1 : ℚ) / 40, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := FisherOneSided.analysis declaredSizes declaredLevel
def bounds : List ℕ := [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 16, 16, 17, 17, 18, 18, 19, 20, 20, 21, 21, 22, 22, 23, 23, 24, 25, 25, 26, 26, 27, 28, 28, 29, 29, 30, 31, 31, 32, 33, 34, 35, 36]

theorem checked_region : FisherOneSided.HintsValid declaredSizes.nControl
    declaredSizes.nTreatment 1 40 bounds := by
  decide +kernel

theorem checked_sections : FisherOneSided.HintSections declaredSizes.nControl
    declaredSizes.nTreatment bounds := by
  decide +kernel

theorem checked_typeI :
    (declaredAnalysis.typeIClaim (declaredLevel.value : ℝ)).statement :=
  FisherOneSided.typeI_of_hints declaredSizes declaredLevel 1 40 (by decide)
    (by norm_num [declaredLevel]) bounds checked_region checked_sections

theorem checked_counts : 0 < 36 ∧ 0 < 36 ∧ 4 ≤ 36 ∧ 14 ≤ 36 := by decide

theorem checked_p_value : FisherOneSided.lowerPValue 36 36 18 4 =
    (4212885 : ℚ) / 650576834 := by
  apply FisherOneSided.lowerPValue_eq_of_cross_product 36 36 18 4
    4212885 650576834 (by decide) (by decide)
  decide +kernel

theorem checked_decision :
    (FisherOneSided.lowerPValue 36 36 18 4 ≤ (1 : ℚ) / 40) ↔ True := by
  rw [checked_p_value]
  norm_num

end outcome_claim_checks

set_option maxRecDepth 100000 in
theorem outcome_claim (i : Instance) (premises : Premises i) :
    (0 < 36 ∧ 0 < 36 ∧ 4 ≤ 36 ∧ 14 ≤ 36) ∧
    (StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 = (4212885 : ℚ) / 650576834) ∧
    ((StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 ≤ (1 : ℚ) / 40) ↔ True) ∧
    ((analysis.typeIClaim (analysis_level.value : ℝ)).statement) :=
  ⟨outcome_claim_checks.checked_counts, outcome_claim_checks.checked_p_value, outcome_claim_checks.checked_decision, outcome_claim_checks.checked_typeI⟩

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  ((analysis.typeIClaim (analysis_level.value : ℝ)).statement) ∧
  ((0 < 36 ∧ 0 < 36 ∧ 4 ≤ 36 ∧ 14 ≤ 36) ∧
    (StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 = (4212885 : ℚ) / 650576834) ∧
    ((StatClaim.Modules.FisherOneSided.lowerPValue 36 36 18 4 ≤ (1 : ℚ) / 40) ↔ True) ∧
    ((analysis.typeIClaim (analysis_level.value : ℝ)).statement))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance := ⟨⟩

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨guarantee_claim i premises, outcome_claim i premises⟩
  satisfiable := ⟨witness, ⟨⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("guarantee_claim", ``guarantee_claim), ("outcome_claim", ``outcome_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/one_sided.stat {short}: {String.intercalate "," used}"
