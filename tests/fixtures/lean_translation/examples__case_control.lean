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

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (analysis.typeIClaim analysis_compatible (analysis_level.value : ℝ)).statement

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  study_Parameter := Unit
  study_Outcome := Unit
  study := StatClaim.Interface.ObservationalModel.trivial

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
    logInfo m!"STATCLAIM_PREMISES examples/case_control.stat {short}: {String.intercalate "," used}"
