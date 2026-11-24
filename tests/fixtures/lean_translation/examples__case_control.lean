set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  study_Parameter : Type
  study_Outcome : Type
  [study_space : MeasurableSpace study_Outcome]
  study : StatClaim.Interface.ObservationalModel study_Parameter study_Outcome
attribute [instance] Instance.study_space

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Fixed groups make the table two independent binomial counts, and no
-- association makes their probabilities equal: the model of Fisher's test
-- (StatClaim.Modules.Association).
def analysis_groups : StatClaim.FixedSampleDesign :=
  ⟨240, 120, by decide, by decide⟩

noncomputable def analysis_study := StatClaim.Modules.TwoArmBinomial.model analysis_groups

noncomputable def analysis_design :=
  StatClaim.Core.StudyDesign.fixed analysis_study

noncomputable def analysis_compatible :
    StatClaim.Core.Compatibility analysis_design :=
  StatClaim.Core.Compatibility.fixed _

noncomputable def analysis :=
  StatClaim.Modules.Fisher.analysis analysis_groups analysis_design analysis_level

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

theorem checked_claim (i : Instance) (premises : Premises i) :
    (analysis.typeIClaim analysis_compatible (analysis_level.value : ℝ)).statement :=
  StatClaim.Modules.Fisher.typeI_statement analysis_groups analysis_design analysis_compatible analysis_level

namespace odds_claim_checks

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open StatClaim StatClaim.Modules

theorem checked_coverage (pc pt : unitInterval) :
    (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (productBinomial 240 120 pc pt).real
      ({a | pc ∈ BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b}) := by
  have joint := BinomialInterval.joint_coverage 240 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) (by positivity)
    (by norm_num) pc pt
  exact le_trans (by norm_num) joint

theorem checked_interval (pc pt : unitInterval)
    (control : pc ∈ BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 112)
    (treatment : pt ∈ BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 64)
    (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1) :
    Association.odds (((1069 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ)) / Association.odds (((5409 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ Association.odds pt / Association.odds pc ∧
      Association.odds pt / Association.odds pc ≤ Association.odds (((637 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) / Association.odds (((787 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ)) := by
  have bound := Association.odds_ratio_contains 240 120 112 64 253 20000 (by decide)
    787 2000 (by decide) (by decide) 5409 10000 (by decide) (by decide) 1069 2500 (by decide) (by decide) 637 1000 (by decide) (by decide)
    (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel)) pc pt control treatment positive below treatedBelow
  exact ⟨bound.2.1 (by decide), bound.2.2 (by decide) (by decide)⟩

end odds_claim_checks

set_option maxRecDepth 100000 in
theorem odds_claim (i : Instance) (premises : Premises i) :
    (∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 240 120 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 112)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 64)
      (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1),
      StatClaim.Modules.Association.odds (((1069 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((5409 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ∧
      StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ≤ StatClaim.Modules.Association.odds (((637 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((787 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ))) :=
  ⟨odds_claim_checks.checked_coverage, odds_claim_checks.checked_interval⟩

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  ((analysis.typeIClaim analysis_compatible (analysis_level.value : ℝ)).statement) ∧
  ((∀ (pc pt : unitInterval),
      (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 240 120 pc pt).real
      ({a | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) a} ×ˢ
        {b | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) b})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 240 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 112)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 120 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 64)
      (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1),
      StatClaim.Modules.Association.odds (((1069 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((5409 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) ≤ StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ∧
      StatClaim.Modules.Association.odds pt / StatClaim.Modules.Association.odds pc ≤ StatClaim.Modules.Association.odds (((637 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ)) / StatClaim.Modules.Association.odds (((787 : ℕ) : ℝ) / ((2000 : ℕ) : ℝ))))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  study_Parameter := Unit
  study_Outcome := Unit
  study := StatClaim.Interface.ObservationalModel.trivial

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨checked_claim i premises, odds_claim i premises⟩
  satisfiable := ⟨witness, ⟨⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("checked_claim", ``checked_claim), ("odds_claim", ``odds_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/case_control.stat {short}: {String.intercalate "," used}"
