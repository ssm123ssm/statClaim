set_option linter.unusedVariables false

/-- The program's abstract parts: laws Lean does not fix, and the tests seen
from outside. -/
structure Instance where

def study_sizes : StatClaim.FixedSampleDesign :=
  ⟨50, 50, by decide, by decide⟩

noncomputable def study := StatClaim.Modules.TwoArmBinomial.model study_sizes

/-- The premises the claims rest on: cited and declared guarantees. -/
structure Premises (i : Instance) : Prop where

namespace verification_claim_checks

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open StatClaim StatClaim.Modules

theorem checked_coverage (pc pt : unitInterval) :
    (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (productBinomial 50 50 pc pt).real
      ({x | pc ∈ BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) x} ×ˢ
        {y | pt ∈ BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) y}) := by
  have joint := BinomialInterval.joint_coverage 50 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) (by positivity) (by norm_num)
    pc pt
  exact le_trans (by norm_num) joint

theorem checked_interval (pc pt : unitInterval)
    (control : pc ∈ BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 12)
    (treatment : pt ∈ BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 24) :
    ((797 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ) - ((4013 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) ≤
        (pt : ℝ) - (pc : ℝ) ∧
      (pt : ℝ) - (pc : ℝ) ≤
        ((6443 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - ((1189 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) :=
  BinomialInterval.difference_contains 50 50 12 24 253 20000 (by decide)
    1189 10000 (by decide) (by decide) 4013 10000 (by decide) (by decide) 797 2500 (by decide) (by decide) 6443 10000 (by decide) (by decide)
    (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel)) (Or.inr (by decide +kernel)) pc pt control treatment

end verification_claim_checks

set_option maxRecDepth 100000 in
theorem verification_claim (i : Instance) (premises : Premises i) :
    (∀ (pc pt : unitInterval), (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 50 50 pc pt).real
      ({x | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) x} ×ˢ
        {y | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) y})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 12)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 24),
      ((797 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ) - ((4013 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) ≤
        (pt : ℝ) - (pc : ℝ) ∧
      (pt : ℝ) - (pc : ℝ) ≤
        ((6443 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - ((1189 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ)) :=
  ⟨verification_claim_checks.checked_coverage, verification_claim_checks.checked_interval⟩

/-- What the program claims. -/
def Claims (i : Instance) : Prop :=
  (∀ (pc pt : unitInterval), (((19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) ≤ (StatClaim.productBinomial 50 50 pc pt).real
      ({x | pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) x} ×ˢ
        {y | pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) y})) ∧
    (∀ (pc pt : unitInterval)
      (control : pc ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 12)
      (treatment : pt ∈ StatClaim.Modules.BinomialInterval.confidenceSet 50 (((253 : ℕ) : ℝ) / ((20000 : ℕ) : ℝ)) 24),
      ((797 : ℕ) : ℝ) / ((2500 : ℕ) : ℝ) - ((4013 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) ≤
        (pt : ℝ) - (pc : ℝ) ∧
      (pt : ℝ) - (pc : ℝ) ≤
        ((6443 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - ((1189 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ))

/-- One instance meeting every premise, so the claims are not vacuous. -/
noncomputable def witness : Instance := ⟨⟩

theorem program : StatClaim.Interface.ProgramTheorem Premises Claims where
  implies := fun i premises => verification_claim i premises
  satisfiable := ⟨witness, ⟨⟩⟩

-- The premises each claim's proof uses, following this program's own constants.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let structureName := ``Premises
  let fields := getStructureFields env structureName
  for (short, claim) in [("verification_claim", ``verification_claim)] do
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
    logInfo m!"STATCLAIM_PREMISES examples/difference_interval.stat {short}: {String.intercalate "," used}"
