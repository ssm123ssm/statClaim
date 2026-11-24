set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where

namespace checked_claim_plan

def declaredDesign : StatClaim.Modules.TwoStageBinomial.Design :=
  StatClaim.Modules.TwoStageBinomial.thresholdDesign 9 15 0 2
noncomputable def nullRate : unitInterval := StatClaim.ratPoint 1 20 (by decide) (by decide)
noncomputable def declaredAnalysis := StatClaim.Modules.TwoStageBinomial.analysisAtMost declaredDesign nullRate

end checked_claim_plan

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

namespace checked_claim_checks

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open StatClaim StatClaim.Modules

def declaredDesign : TwoStageBinomial.Design :=
  TwoStageBinomial.thresholdDesign 9 15 0 2
noncomputable def nullRate : unitInterval := ratPoint 1 20 (by decide) (by decide)
noncomputable def declaredAnalysis := TwoStageBinomial.analysisAtMost declaredDesign nullRate

theorem checked_stages : declaredDesign.nFirst = 9 ∧ declaredDesign.nSecond = 15 := ⟨rfl, rfl⟩

theorem checked_typeI :
    (declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement :=
  TwoStageBinomial.typeI_atMost_of_check declaredDesign
    (TwoStageBinomial.thresholdDesign_monotone 9 15 0 2) 1 20 (by decide) (by decide)
    1 10 (by decide) (by decide +kernel)

theorem checked_power :
    (declaredAnalysis.powerClaim (fun rate => rate = ratPoint 1 4 (by decide) (by decide))
      (((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement :=
  TwoStageBinomial.power_atMost_of_check declaredDesign nullRate 1 4 (by decide) (by decide)
    9 10 (by decide) (by decide +kernel)

end checked_claim_checks

set_option maxRecDepth 100000 in
theorem checked_claim (i : Instance) (premises : Premises i) :
    (checked_claim_plan.declaredDesign.nFirst = 9 ∧ checked_claim_plan.declaredDesign.nSecond = 15) ∧
    ((checked_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) ∧
    ((checked_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 1 4 (by decide) (by decide))
      (((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) :=
  ⟨checked_claim_checks.checked_stages, checked_claim_checks.checked_typeI, checked_claim_checks.checked_power⟩

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (checked_claim_plan.declaredDesign.nFirst = 9 ∧ checked_claim_plan.declaredDesign.nSecond = 15) ∧
    ((checked_claim_plan.declaredAnalysis.typeIClaim (((1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement) ∧
    ((checked_claim_plan.declaredAnalysis.powerClaim (fun rate => rate = StatClaim.ratPoint 1 4 (by decide) (by decide))
      (((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ))).statement)

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance := ⟨⟩

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => checked_claim i premises
  satisfiable := ⟨witness, ⟨⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("checked_claim", ``checked_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/paper/simon_design.stat {short}: {String.intercalate "," used}"
