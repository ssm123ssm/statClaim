import StatClaim

open StatClaim StatClaim.Semantics StatClaim.Modules StatClaim.Interface MeasureTheory

namespace SemanticsReference

variable (i : StatClaim.Semantics.Instance) (alpha : SignificanceLevel)
variable (model : Model) (study : Study)

def fixed (m : Model) : Design := ⟨m, .fixed⟩

example :
    (Request.typeI (.fisher "f" (fixed model) ⟨.equal_proportions, model, none⟩ alpha)).Holds i ↔
    ((Fisher.analysis model.sizes (Core.StudyDesign.fixed (TwoArmBinomial.model model.sizes))
      alpha).typeIClaim (Core.Compatibility.fixed _) (alpha.value : ℝ)).statement := Iff.rfl

example :
    (Request.typeI (.exact "f" .fisherOneSided (fixed model)
      ⟨.proportion_difference_at_most, model, some 0⟩ alpha)).Holds i ↔
    ((FisherOneSided.analysis model.sizes alpha).typeIClaim (alpha.value : ℝ)).statement := Iff.rfl

example :
    (Request.typeI (.exactStudy "a" .fisherGroups ⟨study, .fixed⟩ ⟨study⟩ alpha)).Holds i ↔
    ((Fisher.analysis study.groupSizes
      (Core.StudyDesign.fixed (TwoArmBinomial.model study.groupSizes)) alpha).typeIClaim
        (Core.Compatibility.fixed _) (alpha.value : ℝ)).statement := Iff.rfl

def random (m : Model) (a : SignificanceLevel) : Randomised :=
  ⟨fixed { m with randomisation := some "complete" }, m, a, none⟩

open Randomisation in
example :
    (Request.typeI (.randomised "r" (random model alpha))).Holds i ↔
    let k := (random model alpha).sizes.2
    let n := (random model alpha).sizes.1 + k
    ∀ {V S : Type} [LinearOrder S] (statistic : Assignment n → (Fin n → V) → S)
      (outcomes : PotentialOutcomes n V), SharpNull outcomes →
        (law n k).real (rejection n k statistic outcomes alpha.value) ≤ (alpha.value : ℝ) :=
  Iff.rfl

example (null : Null) :
    (Request.typeI (.assumed "a" (.declared "custom" .finiteSample []) (fixed model)
      null alpha)).Holds i ↔
    typeIClaim (Core.Compatibility.fixed (model.view i.laws).base)
      ((model.view i.laws).null null) (i.test "a" model) (alpha.value : ℝ) := Iff.rfl

example :
    (Request.typeI (.associated "a" Generated.Methods.survey_linear ⟨study, .fixed⟩
      ⟨study⟩ alpha [])).Holds i ↔
    typeIClaim (Core.Compatibility.fixed (i.studies study).model.toModel)
      (i.studies study).model.noAssociation (i.studyTest "a" study)
        ((alpha.value : ℝ) + i.slack "a") := Iff.rfl

example :
    Premise.AllHold i (Test.member (.randomised "r" (random model alpha))).premises ↔
    LevelPremise .finiteSample (i.member "r").law.model.law
      (i.member "r").null (i.member "r").procedure alpha.value (i.slack "r") ∧ True := Iff.rfl

def union (i : StatClaim.Semantics.Instance) (members : List Test) (a : SignificanceLevel) :
    Prop :=
  Joint (Test.leavesOf i members) fun σ ws =>
    familywiseClaim σ.law (Test.members i σ members ws).nulls
      (Test.members i σ members ws).rejects ((a.value : ℝ) + ∑ k, (Test.members i σ members ws).slacks k)

example (members : List Test) :
    (Test.bonferroni "f" members alpha none).familywise i ↔ union i members alpha := Iff.rfl

example (members : List Test) :
    (Test.looks "l" members alpha).typeI i ↔ union i members alpha := Iff.rfl

-- Spending boundaries: the design's rejection is its procedure's, and its level is the
-- cited rule's premise, with a large-sample slack.
example (members : List Test) :
    (Test.procedure "d" .spending_obrien_fleming members alpha [] []).typeI i ↔
    Joint (Test.leavesOf i members) fun σ ws =>
      familywiseClaim σ.law (Test.members i σ members ws).nulls
        (i.graph "d" (Test.leavesOf i members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack "d") := Iff.rfl

example (members : List Test) :
    Premise.AllHold i (Test.procedure "d" .spending_pocock members alpha [] []).premises ↔
    Premise.AllHold i (Test.premisesOf members ++ [.procedure "d" .spending_pocock members alpha]) :=
  Iff.rfl

example (members : List Test) :
    (Premise.procedure "d" .spending_pocock members alpha).Holds i ↔
    Scope.largeSample.permits (i.slack "d") ∧
    Joint (Test.leavesOf i members) fun σ ws =>
      familywiseClaim σ.law (Test.members i σ members ws).nulls
        (i.graph "d" (Test.leavesOf i members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack "d") := Iff.rfl

-- A graph's guarantee is finite-sample when every member's is.
example :
    (Premise.procedure "g" .graphical [] alpha).Holds i ↔
    Scope.finiteSample.permits (i.slack "g") ∧
    Joint [] fun σ ws =>
      familywiseClaim σ.law (Test.members i σ [] ws).nulls
        (i.graph "g" [] 0 _ _ σ ws) ((alpha.value : ℝ) + i.slack "g") := Iff.rfl

example (members : List Test) :
    (Test.sequence "s" members alpha).familywise i ↔
    Joint (Test.leavesOf i members) fun σ ws =>
      sequenceClaim σ.law (Test.members i σ members ws).nulls (Test.members i σ members ws).rejects
        ((alpha.value : ℝ) + ∑ k, (Test.members i σ members ws).slacks k) := Iff.rfl

example (members : List Test) :
    (Test.procedure "g" .graphical members alpha [] []).familywise i ↔
    Joint (Test.leavesOf i members) fun σ ws =>
      familywiseClaim σ.law (Test.members i σ members ws).nulls
        (i.graph "g" (Test.leavesOf i members) members.length _ _ σ ws)
        ((alpha.value : ℝ) + i.slack "g") := Iff.rfl

example :
    (Request.familywise (.bonferroni "f" [] alpha none)).Holds i ↔
    union i [] alpha := Iff.rfl

example (o : ObservedCounts) (r : ReportedResult) :
    (Request.result "answer" (.exact "f" .fisherOneSided (fixed model)
      ⟨.proportion_difference_at_most, model, some 0⟩ alpha) o r).Holds i ↔
    (0 < model.sizes.nControl ∧ 0 < model.sizes.nTreatment ∧
      o.control ≤ model.sizes.nControl ∧ o.treatment ≤ model.sizes.nTreatment) ∧
    FisherOneSided.lowerPValue model.sizes.nControl model.sizes.nTreatment
      (o.control + o.treatment) o.control = r.pValue.value ∧
    (FisherOneSided.lowerPValue model.sizes.nControl model.sizes.nTreatment
      (o.control + o.treatment) o.control ≤ alpha.value ↔ OneSided.verdict r.reject) ∧
    ((FisherOneSided.analysis model.sizes alpha).typeIClaim (alpha.value : ℝ)).statement :=
  Iff.rfl

noncomputable def asReal (f : ProbabilityFraction) : ℝ := (f.num : ℝ) / f.den

example (n count critical : ℕ) (reference level : ProbabilityFraction) (r : ReportedResult) :
    (Request.checkedResult "answer" (.oneSample "a" n reference level)
      (.oneSample count critical r)).Holds i ↔
    ((OneSampleBinomial.policy ⟨n, count⟩).law reference.point).real {x | count ≤ x} =
      asReal r.pValue ∧
    OneSampleBinomial.criticalValue n reference.num reference.den level.num level.den = critical ∧
    (if r.reject then critical ≤ count else ¬ critical ≤ count) ∧
    ((OneSampleBinomial.analysis ⟨n, critical⟩ reference.point).typeIClaim
      (asReal level)).statement := Iff.rfl

example (sizes : Stages) (reference bound : ProbabilityFraction) (first a b : ℕ) (reject : Bool) :
    (Request.checkedResult "answer" (.twoStage "a" sizes (.threshold a b) reference)
      (.twoStage first none false reject bound)).Holds i ↔
    let design : TwoStageBinomial.Design :=
      ⟨sizes.first, sizes.second, fun x => decide (a < x), fun x y => decide (b < x + y)⟩
    design.continues first = false ∧
      ((TwoStageBinomial.analysisAtMost design reference.point).typeIClaim
        (asReal bound)).statement := Iff.rfl

example (n x : ℕ) (confidence tail : ProbabilityFraction) (ends : Endpoints) :
    (Request.interval "interval" (.binomial n x confidence tail ends)).Holds i ↔
    (∀ p : unitInterval, 1 - 2 * asReal tail ≤ (ProbabilityTheory.binomial n p).real
      {count | p ∈ BinomialInterval.confidenceSet n (asReal tail) count}) ∧
    (∀ p : unitInterval, p ∈ BinomialInterval.confidenceSet n (asReal tail) x →
      ends.lower.point ≤ p ∧ p ≤ ends.upper.point) := Iff.rfl

example (n c : ℕ) (reference level rate power error : ProbabilityFraction) :
    (Request.planned "plan" (.meets (.oneSample "a" n reference level))
      ⟨.response rate, power, error⟩ (some (.oneSample n c))).Holds i ↔
    let design : OneSampleBinomial.Design := ⟨n, c⟩
    let analysis := OneSampleBinomial.analysis design reference.point
    (design.n = n ∧ design.critical = c) ∧
    (analysis.typeIClaim (asReal error)).statement ∧
    (analysis.powerClaim (fun p => p = rate.point) (asReal power)).statement := Iff.rfl

def trial : Model := { outcome := .binary, sizes := ⟨10, 10, by decide, by decide⟩ }

def level : SignificanceLevel := ⟨1 / 20, by norm_num, by norm_num⟩

def exactMember : Test :=
  .exact "f" .fisherOneSided (fixed trial) ⟨.proportion_difference_at_most, trial, some 0⟩ level

def conditionalFamily (member : Test) : Program :=
  ⟨[.familywise (.bonferroni "family" [member] level none)], []⟩

example :
    (conditionalFamily (.member exactMember)).encode = (conditionalFamily exactMember).encode :=
  rfl

example : (conditionalFamily (.member exactMember)).Contracts := by decide +kernel

example : ¬ (conditionalFamily exactMember).Contracts := by decide +kernel

end SemanticsReference
