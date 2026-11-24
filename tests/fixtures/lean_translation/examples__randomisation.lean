set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where
  pain_Parameter : Type
  pain_Outcome : Type
  [pain_space : MeasurableSpace pain_Outcome]
  pain : StatClaim.Interface.TwoArmModel pain_Parameter pain_Outcome
  practice_Parameter : Type
  practice_Outcome : Type
  [practice_space : MeasurableSpace practice_Outcome]
  practice : StatClaim.Interface.TwoArmModel practice_Parameter practice_Outcome
attribute [instance] Instance.pain_space
attribute [instance] Instance.practice_space

def analysis_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

def clustered_level : StatClaim.SignificanceLevel :=
  ⟨((1 : ℚ) / 20), by norm_num, by norm_num⟩

-- Contract facts the Python compiler checks, decided by Lean.

theorem analysis_sizes :
    0 < 20 ∧
    20 < 40 :=
  by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem analysis_splits :
    (StatClaim.Modules.Randomisation.splits 40 20).card = 137846528820 :=
  by
    rw [StatClaim.Modules.Randomisation.splits_card,
      Nat.choose_eq_factorial_div_factorial (by decide)]
    decide +kernel

theorem analysis_attainable :
    (1 : ℚ) / 10000 ≤ ((1 : ℚ) / 20) :=
  by norm_num

theorem clustered_sizes :
    0 < 6 ∧
    6 < 12 :=
  by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem clustered_splits :
    (StatClaim.Modules.Randomisation.splits 12 6).card = 924 :=
  by
    rw [StatClaim.Modules.Randomisation.splits_card,
      Nat.choose_eq_factorial_div_factorial (by decide)]
    decide +kernel

theorem clustered_attainable :
    (1 : ℚ) / 924 ≤ ((1 : ℚ) / 20) :=
  by norm_num

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

theorem individual_claim (i : Instance) (premises : Premises i) :
    ∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 40 → (Fin 40 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 40 Value),
      (StatClaim.Modules.Randomisation.SharpNull outcomes) →
      (MeasureTheory.Measure.pi (fun _ : Fin (9999 + 1) => StatClaim.Modules.Randomisation.law 40 20)).real
        (StatClaim.Modules.Randomisation.drawnRejection 9999 statistic outcomes (analysis_level.value : ℚ)) ≤ (analysis_level.value : ℝ) :=
  fun statistic outcomes sharp =>
    StatClaim.Modules.Randomisation.drawnRejection_le_of_level (StatClaim.Modules.Randomisation.splits 40 20) 9999 statistic outcomes sharp _ analysis_level.nonnegative

theorem by_clinic_claim (i : Instance) (premises : Premises i) :
    ∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 12 → (Fin 12 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 12 Value),
      (StatClaim.Modules.Randomisation.SharpNull outcomes) →
      (StatClaim.Modules.Randomisation.law 12 6).real
        (StatClaim.Modules.Randomisation.rejection 12 6 statistic outcomes (clustered_level.value : ℚ)) ≤ (clustered_level.value : ℝ) :=
  fun statistic outcomes sharp =>
    StatClaim.Modules.Randomisation.typeI_of_level 12 6 statistic outcomes sharp _ clustered_level.nonnegative

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 40 → (Fin 40 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 40 Value),
      (StatClaim.Modules.Randomisation.SharpNull outcomes) →
      (MeasureTheory.Measure.pi (fun _ : Fin (9999 + 1) => StatClaim.Modules.Randomisation.law 40 20)).real
        (StatClaim.Modules.Randomisation.drawnRejection 9999 statistic outcomes (analysis_level.value : ℚ)) ≤ (analysis_level.value : ℝ)) ∧
  (∀ {Value : Type} {Statistic : Type} [LinearOrder Statistic]
      (statistic : StatClaim.Modules.Randomisation.Assignment 12 → (Fin 12 → Value) → Statistic)
      (outcomes : StatClaim.Modules.Randomisation.PotentialOutcomes 12 Value),
      (StatClaim.Modules.Randomisation.SharpNull outcomes) →
      (StatClaim.Modules.Randomisation.law 12 6).real
        (StatClaim.Modules.Randomisation.rejection 12 6 statistic outcomes (clustered_level.value : ℚ)) ≤ (clustered_level.value : ℝ))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance where
  pain_Parameter := Unit
  pain_Outcome := Unit
  pain := StatClaim.Interface.TwoArmModel.trivial
  practice_Parameter := Unit
  practice_Outcome := Unit
  practice := StatClaim.Interface.TwoArmModel.trivial

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => ⟨individual_claim i premises, by_clinic_claim i premises⟩
  satisfiable := ⟨witness, ⟨⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("individual_claim", ``individual_claim), ("by_clinic_claim", ``by_clinic_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/randomisation.stat {short}: {String.intercalate "," used}"
