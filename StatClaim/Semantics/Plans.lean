module

public import StatClaim.Semantics.Intervals
public import StatClaim.Modules.AssociationPower

/-! Exact power at declared planning points and checks over smaller candidates. -/

@[expose] public section
set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Modules

noncomputable section

def Checked.require {Input : Type} (checked : Checked Input) (guard : Input → Bool) :
    Checked Input where
  Statement := checked.Statement
  Hint := checked.Hint
  empty := checked.empty
  check := fun x h => guard x && checked.check x h
  sound := fun x h valid => checked.sound x h (Bool.and_eq_true_iff.mp valid).2

def SearchRange.fits (range : SearchRange) (selected : ℕ) : Bool :=
  decide (0 < range.low ∧ range.low ≤ selected ∧ selected ≤ range.high)

def OptionSearch.minimal (range : Option SearchRange) : Bool :=
  range.any SearchRange.minimal

def OptionSearch.low (range : Option SearchRange) : ℕ :=
  (range.map SearchRange.low).getD 0

structure PolicyPlan where
  reference : ProbabilityFraction
  alternative : ProbabilityFraction
  error : ProbabilityFraction
  power : ProbabilityFraction

def PolicyPlan.separated (p : PolicyPlan) : Bool := decide (p.reference.value < p.alternative.value)

structure OneSamplePlan where
  n : ℕ
  critical : ℕ
  alpha : ProbabilityFraction
  target : PolicyPlan
  search : Option SearchRange

def OneSamplePlan.minimalStatement (p : OneSamplePlan) : Prop :=
  let r := p.target.reference
  let a := p.alpha
  ∀ n, OptionSearch.low p.search ≤ n → n < p.n →
    let design := OneSampleBinomial.levelDesign n r.num r.den a.num a.den
    p.target.error.real < ((OneSampleBinomial.policy design).law r.point).real
      {count | design.critical ≤ count} ∨
    ((OneSampleBinomial.policy design).law p.target.alternative.point).real
      {count | design.critical ≤ count} < p.target.power.real

def OneSamplePlan.minimalCheck (p : OneSamplePlan) : Prop :=
  let r := p.target.reference
  let b := p.target.alternative
  let e := p.target.error
  let w := p.target.power
  let a := p.alpha
  OneSampleBinomial.criticalValue p.n r.num r.den a.num a.den = p.critical ∧
  OneSampleBinomial.SmallerFail (OptionSearch.low p.search) p.n r.num r.den a.num a.den
    e.num e.den b.num b.den w.num w.den

instance (p : OneSamplePlan) : Decidable p.minimalCheck := inferInstanceAs (Decidable (_ ∧ _))

def oneSamplePlan : Checked OneSamplePlan where
  Statement := fun p =>
    let design : OneSampleBinomial.Design := ⟨p.n, p.critical⟩
    let analysis := OneSampleBinomial.analysis design p.target.reference.point
    let power := (analysis.powerClaim (fun x => x = p.target.alternative.point) p.target.power.real).statement
    (design.n = p.n ∧ design.critical = p.critical) ∧
    (analysis.typeIClaim p.target.error.real).statement ∧
    if OptionSearch.minimal p.search then
      power ∧ OneSampleBinomial.criticalValue p.n p.target.reference.num p.target.reference.den
        p.alpha.num p.alpha.den = p.critical ∧ p.minimalStatement
    else power
  Hint := PUnit
  empty := PUnit.unit
  check := fun p _ =>
    let r := p.target.reference
    let b := p.target.alternative
    let e := p.target.error
    let w := p.target.power
    p.target.separated && p.search.all (fun search => search.fits p.n) &&
    decide (0 < p.n ∧
      OneSampleBinomial.criticalValue p.n r.num r.den p.alpha.num p.alpha.den = p.critical ∧
      OneSampleBinomial.tailNumerator p.n r.num r.den p.critical * e.den ≤ e.num * r.den ^ p.n ∧
      w.num * b.den ^ p.n ≤ OneSampleBinomial.tailNumerator p.n b.num b.den p.critical * w.den) &&
    (!OptionSearch.minimal p.search || decide p.minimalCheck)
  sound := by
    intro p _ checked
    obtain ⟨⟨⟨_, _⟩, values⟩, minimal⟩ := Bool.and_eq_true_iff.mp checked |>.imp
      (fun h => (Bool.and_eq_true_iff.mp h).imp Bool.and_eq_true_iff.mp id) id
    obtain ⟨_, critical, error, power⟩ := of_decide_eq_true values
    have typeI := OneSampleBinomial.typeI_of_check ⟨p.n, p.critical⟩ _ _
      p.target.reference.bounded p.target.reference.positive _ _ p.target.error.positive error
    have powered := OneSampleBinomial.power_of_check ⟨p.n, p.critical⟩ p.target.reference.point
      _ _ p.target.alternative.bounded p.target.alternative.positive _ _ p.target.power.positive power
    refine ⟨⟨rfl, rfl⟩, typeI, ?_⟩
    split
    · next needed =>
      have h : p.minimalCheck := by
        rw [needed, Bool.not_true, Bool.false_or] at minimal
        exact of_decide_eq_true minimal
      exact ⟨powered, critical, OneSampleBinomial.fails_of_smallerFail _ _
        p.target.reference.bounded p.target.reference.positive p.alpha.num p.alpha.den
        _ _ p.target.error.positive _ _ p.target.alternative.bounded p.target.alternative.positive
        _ _ p.target.power.positive _ _ h.2⟩
    · exact powered

structure StagedPlan where
  sizes : Stages
  rule : StageRule
  target : PolicyPlan

def stagedPlan : Checked StagedPlan where
  Statement := fun p =>
    let design := p.rule.design p.sizes
    let analysis := TwoStageBinomial.analysisAtMost design p.target.reference.point
    (design.nFirst = p.sizes.first ∧ design.nSecond = p.sizes.second) ∧
    (analysis.typeIClaim p.target.error.real).statement ∧
    (analysis.powerClaim (fun x => x = p.target.alternative.point) p.target.power.real).statement
  Hint := PUnit
  empty := PUnit.unit
  check := fun p _ =>
    let design := p.rule.design p.sizes
    let b := p.target.alternative
    let w := p.target.power
    p.target.separated && p.rule.check p.sizes &&
    decide (0 < p.sizes.first ∧ 0 < p.sizes.second ∧
      stageTypeI design p.target.reference p.target.error ∧
      w.num * rejectionDenominator design.nFirst design.nSecond b.den b.den ≤
        rejectionNumerator design.nFirst design.nSecond b.num b.den b.num b.den design.rejectRule * w.den)
  sound := by
    intro p _ checked
    obtain ⟨_, values⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨_, _, error, power⟩ := of_decide_eq_true values
    refine ⟨?_, TwoStageBinomial.typeI_atMost_of_check _ (p.rule.monotone p.sizes)
      _ _ p.target.reference.bounded p.target.reference.positive _ _ p.target.error.positive error,
      TwoStageBinomial.power_atMost_of_check _ _ _ _ p.target.alternative.bounded
        p.target.alternative.positive _ _ p.target.power.positive power⟩
    cases p.rule <;> exact ⟨rfl, rfl⟩

inductive ArmMethod where
  | twoSided
  | oneSided
  deriving DecidableEq

def ArmMethod.analysis (method : ArmMethod) (sizes : FixedSampleDesign) (alpha : SignificanceLevel) :
    Core.PolicyAnalysis (Core.Policy.fixed (TwoArmBinomial.model sizes)) :=
  match method with
  | .twoSided => FisherPower.analysis sizes alpha
  | .oneSided => FisherOneSided.analysis sizes alpha

structure ArmPlan where
  method : ArmMethod
  sizes : FixedSampleDesign
  alpha : SignificanceLevel
  point : BinomialPoint
  error : ProbabilityFraction
  power : ProbabilityFraction
  range : Option SearchRange

def ArmPlan.levelNum (p : ArmPlan) : ℕ := OneSided.levelNum (p.sizes, p.alpha)
def ArmPlan.ratio (p : ArmPlan) : ℕ := (p.range.map SearchRange.ratio).getD 1

theorem ArmPlan.ratio_pos (p : ArmPlan) : 0 < p.ratio := by
  unfold ArmPlan.ratio
  cases p.range with
  | none => decide
  | some range => exact range.positive

structure FisherHint where
  cuts : List ℕ
  nexts : List ℕ
  deriving Inhabited

structure ArmPlanHints where
  selected : FisherHint
  smaller : List FisherHint
  deriving Inhabited

def ArmPlan.formalPower (p : ArmPlan) : Prop :=
  ((p.method.analysis p.sizes p.alpha).powerClaim
    (fun θ => θ = OneSided.BinomialPoint.parameter p.point) p.power.real).statement

def ArmPlan.smallerClaim (p : ArmPlan) : Prop :=
  ∀ (n : ℕ) (positive : 0 < n), OptionSearch.low p.range ≤ n → n < p.sizes.nControl →
    let sizes : FixedSampleDesign := ⟨n, p.ratio * n, positive, Nat.mul_pos p.ratio_pos positive⟩
    ((Core.Policy.fixed (TwoArmBinomial.model sizes)).law
      (OneSided.BinomialPoint.parameter p.point)).real (p.method.analysis sizes p.alpha).rejection <
      p.power.real

def ArmPlan.checkSelected (p : ArmPlan) (hint : FisherHint) : Prop :=
  let n := p.sizes.nControl
  let m := p.sizes.nTreatment
  let a := p.point.control
  let b := p.point.treatment
  let level := p.levelNum
  let den := p.alpha.value.den
  let bound := p.power
  let (valid, reject) := match p.method with
    | .twoSided => (FisherPower.HintsValid n m level den hint.cuts hint.nexts,
        FisherPower.hintReject n m hint.cuts)
    | .oneSided => (OneSided.levelCheck (p.sizes, p.alpha) hint.cuts,
        FisherOneSided.hintReject hint.cuts)
  valid ∧ bound.num * rejectionDenominator n m a.den b.den ≤
    rejectionNumerator n m a.num a.den b.num b.den reject * bound.den

instance (p : ArmPlan) (hint : FisherHint) : Decidable (p.checkSelected hint) := by
  unfold ArmPlan.checkSelected
  split <;> infer_instance

def ArmPlan.checkSmaller (p : ArmPlan) (smaller : List FisherHint) : Prop :=
  let a := p.point.control
  let b := p.point.treatment
  let w := p.power
  let low := OptionSearch.low p.range
  let n := p.sizes.nControl
  match p.method with
  | .twoSided => FisherPower.SmallerFailHinted p.ratio low n p.levelNum p.alpha.value.den
      a.num a.den b.num b.den w.num w.den (smaller.map FisherHint.cuts) (smaller.map FisherHint.nexts)
  | .oneSided => FisherOneSided.SmallerFailHinted p.ratio low n p.levelNum p.alpha.value.den
      a.num a.den b.num b.den w.num w.den (smaller.map FisherHint.cuts)

instance (p : ArmPlan) (smaller : List FisherHint) : Decidable (p.checkSmaller smaller) := by
  unfold ArmPlan.checkSmaller
  split <;> infer_instance

theorem ArmPlan.selected_sound (p : ArmPlan) (h : FisherHint) (checked : p.checkSelected h) :
    ((p.method.analysis p.sizes p.alpha).typeIClaim (p.alpha.value : ℝ)).statement ∧ p.formalPower := by
  let a := p.point.control
  let b := p.point.treatment
  have equal := OneSided.level_eq (p.sizes, p.alpha)
  cases found : p.method with
  | twoSided =>
    unfold ArmPlan.checkSelected at checked
    rw [found] at checked
    refine ⟨FisherPower.typeI_statement _ _, ?_⟩
    simp only [ArmPlan.formalPower, ArmMethod.analysis, found, OneSided.BinomialPoint.parameter,
      ProbabilityFraction.real]
    apply FisherPower.power_of_check p.sizes p.alpha _ _ p.alpha.value.den_pos equal
      _ _ _ _ a.bounded a.positive b.bounded b.positive _ _ p.power.positive
    change _ ≤ rejectionNumerator _ _ a.num a.den b.num b.den
      (FisherPower.checkedReject _ _ p.levelNum p.alpha.value.den) * p.power.den
    rw [FisherPower.rejectionNumerator_hint _ _ _ _ _ _ _ _ _ _ checked.1]
    exact checked.2
  | oneSided =>
    unfold ArmPlan.checkSelected at checked
    rw [found] at checked
    refine ⟨OneSided.typeI.sound (p.sizes, p.alpha) h.cuts (decide_eq_true checked.1), ?_⟩
    simpa only [ArmPlan.formalPower, ArmMethod.analysis, found, ProbabilityFraction.real] using
      OneSided.power_sound (p.sizes, p.alpha) p.point p.power h.cuts checked.1.1 checked.2

theorem ArmPlan.smaller_sound (p : ArmPlan) (h : List FisherHint)
    (checked : p.checkSmaller h) : p.smallerClaim := by
  let a := p.point.control
  let b := p.point.treatment
  have equal := OneSided.level_eq (p.sizes, p.alpha)
  unfold ArmPlan.smallerClaim
  cases found : p.method with
  | twoSided =>
    unfold ArmPlan.checkSmaller at checked
    rw [found] at checked
    simpa only [ArmMethod.analysis, found, OneSided.BinomialPoint.parameter, ProbabilityFraction.real,
      a, b] using FisherPower.power_lt_of_smallerFail p.alpha _ _
      p.alpha.value.den_pos equal _ _ _ _ a.bounded a.positive b.bounded b.positive
      _ _ p.power.positive p.ratio p.ratio_pos _ _
      (FisherPower.smallerFail_of_hinted _ _ _ _ _ _ _ _ _ _ _ _ _ checked)
  | oneSided =>
    unfold ArmPlan.checkSmaller at checked
    rw [found] at checked
    simpa only [ArmMethod.analysis, found, OneSided.BinomialPoint.parameter, ProbabilityFraction.real,
      a, b] using FisherOneSided.power_lt_of_smallerFail p.alpha _ _
      p.alpha.value.den_pos equal _ _ _ _ a.bounded a.positive b.bounded b.positive
      _ _ p.power.positive p.ratio p.ratio_pos _ _ _ checked

def armPlan : Checked ArmPlan where
  Statement := fun p =>
    (p.sizes.nControl = p.sizes.nControl ∧ p.sizes.nTreatment = p.sizes.nTreatment ∧
      0 < p.sizes.nControl ∧ 0 < p.sizes.nTreatment) ∧
    ((p.method.analysis p.sizes p.alpha).typeIClaim p.error.real).statement ∧
    if OptionSearch.minimal p.range then p.formalPower ∧ p.smallerClaim else p.formalPower
  Hint := ArmPlanHints
  empty := default
  check := fun p h =>
    p.range.all (fun r => r.fits p.sizes.nControl &&
      decide (p.sizes.nTreatment = p.ratio * p.sizes.nControl)) &&
    decide (p.alpha.value ≤ p.error.value ∧ p.checkSelected h.selected) &&
    (!OptionSearch.minimal p.range || decide (p.checkSmaller h.smaller))
  sound := by
    intro p h checked
    obtain ⟨first, minimal⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨_, selected⟩ := Bool.and_eq_true_iff.mp first
    obtain ⟨error, hSelected⟩ := of_decide_eq_true selected
    have result := p.selected_sound h.selected hSelected
    have bound : (p.alpha.value : ℝ) ≤ p.error.real := by
      rw [← p.error.real_cast]
      exact_mod_cast error
    refine ⟨⟨rfl, rfl, p.sizes.controlPositive, p.sizes.treatmentPositive⟩,
      fun θ null => (result.1 θ null).trans bound, ?_⟩
    split
    · next needed =>
      rw [needed, Bool.not_true, Bool.false_or] at minimal
      exact ⟨result.2, p.smaller_sound h.smaller (of_decide_eq_true minimal)⟩
    · exact result.2

def _root_.StatClaim.SignificanceLevel.numerator (a : SignificanceLevel) : ℕ := a.value.num.toNat

theorem _root_.StatClaim.SignificanceLevel.eq_ratio (a : SignificanceLevel) :
    a.value = (a.numerator : ℚ) / a.value.den := by
  unfold SignificanceLevel.numerator
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr a.nonnegative)]
  exact (Rat.num_div_den _).symm

theorem _root_.StatClaim.SignificanceLevel.real_eq_ratio (a : SignificanceLevel) :
    (a.value : ℝ) = (a.numerator : ℝ) / a.value.den := by
  have cast := congrArg (fun r : ℚ => (r : ℝ)) a.eq_ratio
  push_cast at cast
  exact cast

theorem _root_.StatClaim.SignificanceLevel.le_bound (a : SignificanceLevel) (target : ProbabilityFraction)
    (h : a.value ≤ target.value) : (a.value : ℝ) ≤ target.real := by
  rw [← target.real_cast]
  exact_mod_cast h

structure GroupPlan where
  sizes : FixedSampleDesign
  alpha : SignificanceLevel
  point : BinomialPoint
  target : PlanningTarget
  range : Option SearchRange

def GroupPlan.ratio (p : GroupPlan) : ℕ := (p.range.map SearchRange.ratio).getD 1

def GroupPlan.fitsPower (p : GroupPlan) (n m : ℕ) : ℝ :=
  (productBinomial n m p.point.control.point p.point.treatment.point).real
    (fisherRejectionRegionAt n m p.alpha.value)

def GroupPlan.valid (p : GroupPlan) (h : FisherHint) : Prop :=
  let n := p.sizes.nControl
  let m := p.sizes.nTreatment
  let a := p.point.control
  let b := p.point.treatment
  let w := p.target.power
  FisherPower.HintsValid n m p.alpha.numerator p.alpha.value.den h.cuts h.nexts ∧
  w.num * rejectionDenominator n m a.den b.den ≤
    rejectionNumerator n m a.num a.den b.num b.den (FisherPower.hintReject n m h.cuts) * w.den

instance (p : GroupPlan) (h : FisherHint) : Decidable (p.valid h) :=
  inferInstanceAs (Decidable (_ ∧ _))

def GroupPlan.smaller (p : GroupPlan) (hs : List FisherHint) : Prop :=
  let a := p.point.control
  let b := p.point.treatment
  let w := p.target.power
  ∀ n, n < p.sizes.nTreatment → OptionSearch.low p.range ≤ n →
    let h := hs.getD (n - OptionSearch.low p.range) default
    AssociationPower.FailsHinted (p.ratio * n) n p.alpha.numerator p.alpha.value.den
      a.num a.den b.num b.den w.num w.den h.cuts h.nexts

instance (p : GroupPlan) (hs : List FisherHint) : Decidable (p.smaller hs) := by
  unfold GroupPlan.smaller
  infer_instance

def groupPlan : Checked GroupPlan where
  Statement := fun p =>
    (p.sizes.nControl = p.sizes.nControl ∧ p.sizes.nTreatment = p.sizes.nTreatment ∧
      0 < p.sizes.nControl ∧ 0 < p.sizes.nTreatment) ∧
    (∀ q, (fisherNullLaw p.sizes.nControl p.sizes.nTreatment q).real
      (fisherRejectionRegionAt p.sizes.nControl p.sizes.nTreatment p.alpha.value) ≤ p.target.error.real) ∧
    let power := p.target.power.real ≤ p.fitsPower p.sizes.nControl p.sizes.nTreatment
    if OptionSearch.minimal p.range then
      power ∧ (∀ n, OptionSearch.low p.range ≤ n → n < p.sizes.nTreatment →
        p.fitsPower (p.ratio * n) n < p.target.power.real)
    else power
  Hint := ArmPlanHints
  empty := default
  check := fun p h =>
    p.range.all (fun r => r.fits p.sizes.nTreatment &&
      decide (p.sizes.nControl = p.ratio * p.sizes.nTreatment)) &&
    decide (p.point.control.value ≠ p.point.treatment.value ∧
      p.alpha.value ≤ p.target.error.value ∧ p.valid h.selected) &&
    (!OptionSearch.minimal p.range || decide (p.smaller h.smaller))
  sound := by
    intro p h checked
    obtain ⟨first, minimal⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨_, selected⟩ := Bool.and_eq_true_iff.mp first
    obtain ⟨_, error, valid, hSelected⟩ := of_decide_eq_true selected
    let a := p.point.control
    let b := p.point.treatment
    let w := p.target.power
    have powered : w.real ≤ p.fitsPower p.sizes.nControl p.sizes.nTreatment := by
      apply AssociationPower.power_of_check _ _ _ _ p.alpha.value.den_pos _ p.alpha.eq_ratio
        _ _ _ _ a.bounded a.positive b.bounded b.positive _ _ w.positive
      rw [FisherPower.rejectionNumerator_hint _ _ _ _ _ _ _ _ _ _ valid]
      exact hSelected
    refine ⟨⟨rfl, rfl, p.sizes.controlPositive, p.sizes.treatmentPositive⟩,
      fun q => (Association.groups_typeI_le_alpha _ _ q _ p.alpha.nonnegative).trans
        (p.alpha.le_bound _ error), ?_⟩
    split
    · next needed =>
      rw [needed, Bool.not_true, Bool.false_or] at minimal
      have checks : p.smaller h.smaller := of_decide_eq_true minimal
      refine ⟨powered, fun n low high => ?_⟩
      exact AssociationPower.power_lt_of_fails _ _ _ _ p.alpha.value.den_pos _ p.alpha.eq_ratio
        _ _ _ _ a.bounded a.positive b.bounded b.positive _ _ w.positive _ _ (checks n high low)
    · exact powered

structure TailHint where
  lows : List ℕ
  highs : List ℕ
  deriving Inhabited

structure CountPlanHints where
  selected : TailHint
  smaller : List TailHint
  deriving Inhabited

structure MatchedPlan where
  n : ℕ
  alpha : SignificanceLevel
  discordant : ProbabilityFraction
  caseShare : ProbabilityFraction
  odds : ℚ
  target : PlanningTarget
  range : Option SearchRange

def MatchedPlan.rejection (p : MatchedPlan) (n : ℕ) : ℝ :=
  (Matched.pairsLaw n p.discordant.point p.caseShare.point).real (Matched.pairsRejection n p.alpha.value)

def MatchedPlan.num (p : MatchedPlan) (n : ℕ) (h : TailHint) : ℕ :=
  BinomialPower.pairsNumerator n p.discordant.num p.discordant.den
    p.caseShare.num p.caseShare.den h.lows h.highs

def MatchedPlan.den (p : MatchedPlan) (n : ℕ) : ℕ := p.discordant.den ^ n * p.caseShare.den ^ n

def MatchedPlan.valid (p : MatchedPlan) (n : ℕ) (h : TailHint) : Prop :=
  BinomialPower.PairsValid n p.alpha.numerator p.alpha.value.den h.lows h.highs

instance (p : MatchedPlan) (n : ℕ) (h : TailHint) : Decidable (p.valid n h) :=
  inferInstanceAs (Decidable (BinomialPower.PairsValid ..))

def MatchedPlan.smaller (p : MatchedPlan) (hs : List TailHint) : Prop :=
  ∀ n, n < p.n → OptionSearch.low p.range ≤ n →
    let h := hs.getD (n - OptionSearch.low p.range) default
    p.valid n h ∧ p.num n h * p.target.power.den < p.target.power.num * p.den n

instance (p : MatchedPlan) (hs : List TailHint) : Decidable (p.smaller hs) := by
  unfold MatchedPlan.smaller
  infer_instance

def matchedPlan : Checked MatchedPlan where
  Statement := fun p =>
    (∀ δ, (Matched.pairsLaw p.n δ Matched.half).real (Matched.pairsRejection p.n p.alpha.value) ≤
      p.target.error.real) ∧
    let power := p.target.power.real ≤ p.rejection p.n
    if OptionSearch.minimal p.range then
      power ∧ (∀ n, OptionSearch.low p.range ≤ n → n < p.n → p.rejection n < p.target.power.real)
    else power
  Hint := CountPlanHints
  empty := default
  check := fun p h =>
    p.range.all (fun r => r.fits p.n) &&
    decide (0 < p.n ∧ 0 < p.odds ∧ p.odds ≠ 1 ∧ p.caseShare.value = p.odds / (1 + p.odds) ∧
      p.alpha.value ≤ p.target.error.value ∧ p.valid p.n h.selected ∧
      p.target.power.num * p.den p.n ≤ p.num p.n h.selected * p.target.power.den) &&
    (!OptionSearch.minimal p.range || decide (p.smaller h.smaller))
  sound := by
    intro p h checked
    obtain ⟨first, minimal⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨_, selected⟩ := Bool.and_eq_true_iff.mp first
    obtain ⟨_, _, _, _, error, valid, powered⟩ := of_decide_eq_true selected
    let a := p.discordant
    let b := p.caseShare
    let w := p.target.power
    have power : w.real ≤ p.rejection p.n :=
      BinomialPower.pairs_power_of_check _ _ _ _ _ _ _ a.bounded a.positive b.bounded
        b.positive p.alpha.value.den_pos _ p.alpha.real_eq_ratio _ _ valid _ _ w.positive powered
    refine ⟨fun δ => (Matched.typeI p.n δ _ (by exact_mod_cast p.alpha.nonnegative)).trans
      (p.alpha.le_bound _ error), ?_⟩
    split
    · next needed =>
      rw [needed, Bool.not_true, Bool.false_or] at minimal
      have every : p.smaller h.smaller := of_decide_eq_true minimal
      refine ⟨power, fun n low high => ?_⟩
      obtain ⟨valid, below⟩ := every n high low
      exact BinomialPower.pairs_power_lt_of_check _ _ _ _ _ _ _ a.bounded a.positive b.bounded
        b.positive p.alpha.value.den_pos _ p.alpha.real_eq_ratio _ _ valid _ _ w.positive below
    · exact power

structure RatePlan where
  n : ℕ
  alpha : SignificanceLevel
  ratio : ℚ
  exposed : ℚ
  unexposed : ℚ
  nullShare : ProbabilityFraction
  alternative : ProbabilityFraction
  target : PlanningTarget
  range : Option SearchRange

def RatePlan.rejection (p : RatePlan) (n : ℕ) : ℝ :=
  (ProbabilityTheory.binomial n p.alternative.point).real (Incidence.rejectionAt p.nullShare.point n p.alpha.value)

def RatePlan.valid (p : RatePlan) (n low high : ℕ) : Prop :=
  BinomialPower.RegionValid n p.nullShare.num p.nullShare.den
    p.alpha.numerator p.alpha.value.den low high

instance (p : RatePlan) (n low high : ℕ) : Decidable (p.valid n low high) :=
  inferInstanceAs (Decidable (BinomialPower.RegionValid ..))

def RatePlan.smaller (p : RatePlan) (h : TailHint) : Prop :=
  ∀ n, n < p.n → OptionSearch.low p.range ≤ n →
    let k := n - OptionSearch.low p.range
    let low := h.lows.getD k 0
    let high := h.highs.getD k 0
    p.valid n low high ∧ BinomialPower.regionNumerator n p.alternative.num p.alternative.den low high *
      p.target.power.den < p.target.power.num * p.alternative.den ^ n

instance (p : RatePlan) (h : TailHint) : Decidable (p.smaller h) := by
  unfold RatePlan.smaller
  infer_instance

structure RatePlanHints where
  low : ℕ
  high : ℕ
  smaller : TailHint
  deriving Inhabited

def ratePlan : Checked RatePlan where
  Statement := fun p =>
    (∀ total share, (Incidence.ratesLaw total share).real
      (Incidence.given (fun n => Incidence.rejectionAt share n p.alpha.value)) ≤ p.target.error.real) ∧
    let power := p.target.power.real ≤ p.rejection p.n
    if OptionSearch.minimal p.range then
      power ∧ (∀ n, OptionSearch.low p.range ≤ n → n < p.n → p.rejection n < p.target.power.real)
    else power
  Hint := RatePlanHints
  empty := default
  check := fun p h =>
    p.range.all (fun r => r.fits p.n) &&
    decide (0 < p.n ∧ 0 < p.exposed ∧ 0 < p.unexposed ∧ 0 < p.ratio ∧ p.ratio ≠ 1 ∧
      p.nullShare.value = p.exposed / (p.exposed + p.unexposed) ∧
      p.alternative.value = (p.ratio * p.exposed) / (p.ratio * p.exposed + p.unexposed) ∧
      p.alpha.value ≤ p.target.error.value ∧ p.valid p.n h.low h.high ∧
      p.target.power.num * p.alternative.den ^ p.n ≤
        BinomialPower.regionNumerator p.n p.alternative.num p.alternative.den h.low h.high *
          p.target.power.den) &&
    (!OptionSearch.minimal p.range || decide (p.smaller h.smaller))
  sound := by
    intro p h checked
    obtain ⟨first, minimal⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨_, selected⟩ := Bool.and_eq_true_iff.mp first
    obtain ⟨_, _, _, _, _, _, _, error, valid, powered⟩ := of_decide_eq_true selected
    let a := p.alternative
    let c := p.nullShare
    let w := p.target.power
    have power : w.real ≤ p.rejection p.n :=
      BinomialPower.power_of_check _ _ _ _ _ _ _ _ _ a.bounded a.positive c.bounded c.positive
        p.alpha.value.den_pos _ p.alpha.real_eq_ratio valid _ _ w.positive powered
    refine ⟨fun total share => (Incidence.typeI total share _ (by exact_mod_cast p.alpha.nonnegative)).trans
      (p.alpha.le_bound _ error), ?_⟩
    split
    · next needed =>
      rw [needed, Bool.not_true, Bool.false_or] at minimal
      have every : p.smaller h.smaller := of_decide_eq_true minimal
      refine ⟨power, fun n low high => ?_⟩
      obtain ⟨valid, below⟩ := every n high low
      exact BinomialPower.power_lt_of_check _ _ _ _ _ _ _ _ _ a.bounded a.positive c.bounded c.positive
        p.alpha.value.den_pos _ p.alpha.real_eq_ratio valid _ _ w.positive below
    · exact power

structure TotalPlan where
  n : ℕ
  alpha : SignificanceLevel
  exposed : ProbabilityFraction
  point : BinomialPoint
  target : PlanningTarget
  range : Option SearchRange

structure TotalPlanHints where
  cuts : List (List ℕ)
  nexts : List (List ℕ)
  numerators : List ℕ
  deriving Inhabited

def TotalPlan.valid (p : TotalPlan) (h : TotalPlanHints) : Prop :=
  ∀ k, k < p.n + 1 →
    AssociationPower.PartValid p.n k p.alpha.numerator p.alpha.value.den
      p.point.control.num p.point.control.den p.point.treatment.num p.point.treatment.den
      (h.cuts.getD k []) (h.nexts.getD k []) (h.numerators.getD k 0)

instance (p : TotalPlan) (h : TotalPlanHints) : Decidable (p.valid h) := by
  unfold TotalPlan.valid
  infer_instance

def totalPlan : Checked TotalPlan where
  Statement := fun p =>
    (p.n = p.n ∧ 0 < p.n) ∧
    (∀ q r, (Association.mixtureLaw p.n q r).real (Association.mixtureRejection p.n p.alpha.value) ≤
      p.target.error.real) ∧
    p.target.power.real ≤ (Association.mixture p.n p.exposed.point (fun k =>
      productBinomial (p.n - k) k p.point.control.point p.point.treatment.point)).real
      (Association.mixtureRejection p.n p.alpha.value)
  Hint := TotalPlanHints
  empty := default
  check := fun p h =>
    let q := p.exposed
    let a := p.point.control
    let b := p.point.treatment
    let w := p.target.power
    p.range.all (fun r => r.fits p.n && !r.minimal) &&
    decide (0 < p.n ∧ a.value ≠ b.value ∧ p.alpha.value ≤ p.target.error.value ∧ p.valid h ∧
      w.num * (q.den ^ p.n * (a.den ^ p.n * b.den ^ p.n)) ≤
        AssociationPower.totalNumerator p.n q.num q.den a.den b.den h.numerators * w.den)
  sound := by
    intro p h checked
    obtain ⟨_, cert⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨positive, _, error, valid, powered⟩ := of_decide_eq_true cert
    let q := p.exposed
    let a := p.point.control
    let b := p.point.treatment
    let w := p.target.power
    exact ⟨⟨rfl, positive⟩, fun q r =>
      (Association.mixture_typeI_le_alpha p.n q r _ p.alpha.nonnegative).trans
        (p.alpha.le_bound _ error),
      AssociationPower.total_power_of_check _ _ _ _ _ _ _ _ _ q.bounded q.positive
        a.bounded a.positive b.bounded b.positive p.alpha.value.den_pos _ p.alpha.eq_ratio
        _ _ _ valid _ _ w.positive powered⟩

def Test.armPlan (t : Test) (range : Option SearchRange) (p : BinomialPoint)
    (w e : ProbabilityFraction) (sizes : FixedSampleDesign) : Checked Unit :=
  let spec (method : ArmMethod) (design : Design) (level : SignificanceLevel) :=
    let checked := (StatClaim.Semantics.armPlan.atInput ⟨method, sizes, level, p, e, w, range⟩)
    checked.require (fun _ => range.isSome || decide (sizes = design.model.sizes))
  match t with
  | .fisher _ design _ alpha => spec .twoSided design alpha
  | .exact _ .fisherOneSided design _ alpha => spec .oneSided design alpha
  | _ => Checked.unsupported

def Test.plan (t : Test) (range : Option SearchRange) (target : PlanningTarget)
    (selected : PlanSelection) : Checked Unit :=
  let w := target.power
  let e := target.error
  match target.point, selected, t with
  | .arms p, .arms sizes, t => t.armPlan range p w e sizes
  | .response rate, .oneSample n critical, .oneSample _ original reference alpha =>
    let spec := oneSamplePlan.atInput ⟨n, critical, alpha, ⟨reference, rate, e, w⟩, range⟩
    spec.require (fun _ => range.isSome || decide (n = original))
  | .response rate, .stages sizes rule, .twoStage _ original originalRule reference =>
    if range.isSome then Checked.unsupported
    else
      -- The declared rule, rather than a selected replacement, defines a feasibility claim.
      let spec := stagedPlan.atInput ⟨original, originalRule, ⟨reference, rate, e, w⟩⟩
      spec.require (fun _ => decide (sizes = original ∧ rule = originalRule))
  | .association _ _ p none, .arms sizes, .exactStudy _ .fisherGroups d _ alpha =>
    let spec := groupPlan.atInput ⟨sizes, alpha, p, target, range⟩
    spec.require (fun _ => range.isSome || decide (sizes = d.model.groupSizes))
  | .association _ _ p (some exposed), .count n, .exactStudy _ .fisherMixture d _ alpha =>
    let spec := totalPlan.atInput ⟨n, alpha, exposed, p, target, range⟩
    spec.require (fun _ => range.isSome || decide (d.model.n = some n))
  | .matched discordant odds share, .count n, .exactStudy _ .matched d _ alpha =>
    let spec := matchedPlan.atInput ⟨n, alpha, discordant, share, odds, target, range⟩
    spec.require (fun _ => range.isSome || decide (d.model.pairs = some n))
  | .rate ratio exposed unexposed events reference rate, .count n, .exactStudy _ .incidence _ _ alpha =>
    let spec := ratePlan.atInput ⟨n, alpha, ratio, exposed, unexposed, reference, rate, target, range⟩
    spec.require (fun _ => range.isSome || decide (events = some n))
  | _, _, _ => Checked.unsupported

def PlanQuery.checked (query : PlanQuery) (target : PlanningTarget)
    (selection : Option PlanSelection) : Checked Unit :=
  match query, selection with
  | .meets t, some chosen => t.plan none target chosen
  | .search t _ range, some chosen => t.plan (some range) target chosen
  | .stageSearch reference maxTotal criterion, some (.stages sizes (.threshold interim final)) =>
    match target.point with
    | .response rate =>
      let spec := stagedPlan.atInput ⟨sizes, .threshold interim final,
        ⟨reference, rate, target.error, target.power⟩⟩
      spec.require (fun _ => decide (sizes.first + sizes.second ≤ maxTotal) &&
        (criterion == "optimal" || criterion == "minimax"))
    | _ => Checked.unsupported
  | _, _ => Checked.unsupported

end

end StatClaim.Semantics
