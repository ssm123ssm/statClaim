module

public import StatClaim.Semantics.Syntax
public import StatClaim.Modules.FisherOneSided
public import StatClaim.Modules.Fisher
public import StatClaim.Modules.Association
public import StatClaim.Modules.Matched
public import StatClaim.Modules.Incidence
public import StatClaim.Modules.DifferenceTest
public import StatClaim.Modules.Randomisation
public import StatClaim.Modules.Wald
public import StatClaim.Modules.McNemarAsymptotic
public import StatClaim.Modules.FarringtonManning

/-!
Exact claims state a proposition about data and certify it with a kernel check.
This module connects one-sided Fisher's existing theorems to that interface.

Trusted: the statement of each checked claim, what a certificate proves. Each check and its
soundness proof are not: Lean checks them.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Interface StatClaim.Modules

structure Checked (Input : Type) where
  Statement : Input → Prop
  Hint : Type
  empty : Hint
  check : Input → Hint → Bool
  sound : ∀ x h, check x h = true → Statement x

/-- A module's sampling law and test, and the claims it can check about them. -/
structure ExactModule where
  Input : Type
  Parameter : Type
  Outcome : Type
  [space : MeasurableSpace Outcome]
  law : Input → Core.Model Parameter Outcome
  null : Input → Core.Hypothesis Parameter
  procedure : Input → TestInterface Outcome
  level : Input → ℚ
  typeI : Checked Input
  bound : ∀ x, typeI.Statement x →
    ∀ θ, null x θ → ((law x).law θ).real (procedure x).reject ≤ level x
  Observation : Type
  Report : Type
  Point : Type
  Target : Type
  Endpoints : Type
  result : Option (Checked (Input × Observation × Report))
  interval : Option (Checked (Input × Observation × Endpoints))
  power : Option (Checked (Input × Point × Target))

attribute [instance] ExactModule.space

/-- An unsupported claim slot cannot be certified. -/
def Checked.unsupported {Input : Type} : Checked Input where
  Statement := fun _ => False
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ => false
  sound := fun _ _ h => Bool.noConfusion h

def Checked.established {Input : Type} (statement : Input → Prop)
    (proved : ∀ x, statement x) : Checked Input where
  Statement := statement
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ => true
  sound := fun x _ _ => proved x

def Checked.atInput {α : Type} (checked : Checked α) (x : α) : Checked Unit where
  Statement := fun _ => checked.Statement x
  Hint := checked.Hint
  empty := checked.empty
  check := fun _ h => checked.check x h
  sound := fun _ => checked.sound x

def Checked.and {Input : Type} (a b : Checked Input) : Checked Input where
  Statement := fun x => a.Statement x ∧ b.Statement x
  Hint := a.Hint × b.Hint
  empty := (a.empty, b.empty)
  check := fun x h => a.check x h.1 && b.check x h.2
  sound := fun x h checked =>
    let parts := Bool.and_eq_true_iff.mp checked
    ⟨a.sound x h.1 parts.1, b.sound x h.2 parts.2⟩

noncomputable section

open Randomisation in
def Randomised.completeClaim (r : Randomised) : Prop :=
  let k := r.sizes.2
  let n := r.sizes.1 + k
  ∀ {Value Statistic : Type} [LinearOrder Statistic]
    (statistic : Assignment n → (Fin n → Value) → Statistic)
    (outcomes : PotentialOutcomes n Value), SharpNull outcomes →
    match r.draws with
    | none => (law n k).real (rejection n k statistic outcomes r.alpha.value) ≤ (r.alpha.value : ℝ)
    | some b => (Measure.pi (fun _ : Fin (b + 1) => law n k)).real
        (drawnRejection b statistic outcomes r.alpha.value) ≤ (r.alpha.value : ℝ)

open Randomisation in
def Randomised.groupedClaim (r : Randomised) : Prop :=
  let groups := r.groups
  ∀ {Record Statistic : Type} [LinearOrder Statistic]
    (statistic : GroupedAssignment groups → Record → Statistic)
    (outcomes : GroupedAssignment groups → Record), (∀ a b, outcomes a = outcomes b) →
    match r.draws with
    | none => (groupedLaw groups).real
        (uniformRejection (groupedSplits groups) statistic outcomes r.alpha.value) ≤ (r.alpha.value : ℝ)
    | some b => (Measure.pi (fun _ : Fin (b + 1) => groupedLaw groups)).real
        (drawnRejection b statistic outcomes r.alpha.value) ≤ (r.alpha.value : ℝ)

open Randomisation in
def Randomised.typeI : Checked Randomised :=
  Checked.established
    (fun r => if r.design.model.randomisation = some "complete" then r.completeClaim else r.groupedClaim)
    (by
      intro r
      split
      · intro Value Statistic order statistic outcomes sharp
        cases found : r.draws with
        | none => exact typeI_of_level _ _ statistic outcomes sharp _ r.alpha.nonnegative
        | some b => exact drawnRejection_le_of_level _ b statistic outcomes sharp _ r.alpha.nonnegative
      · intro Record Statistic order statistic outcomes sharp
        cases found : r.draws with
        | none => exact groupedTypeI_of_level _ statistic outcomes sharp _ r.alpha.nonnegative
        | some b => exact drawnRejection_le_of_level _ b statistic outcomes sharp _ r.alpha.nonnegative)

/-- The fixed binomial analysis used for trials and for observational studies with fixed groups. -/
def twoSidedAnalysis (x : FixedSampleDesign × SignificanceLevel) :=
  Fisher.analysis x.1 (Core.StudyDesign.fixed (TwoArmBinomial.model x.1)) x.2

def fisherGroupsModule : ExactModule where
  Input := FixedSampleDesign × SignificanceLevel
  Parameter := TwoArmBinomial.Parameters
  Outcome := TwoArmBinomial.Counts
  law := fun x => TwoArmBinomial.model x.1
  null := fun x => (twoSidedAnalysis x).hypothesis
  procedure := fun x =>
    ⟨(twoSidedAnalysis x).procedure.rejectionEvent, (twoSidedAnalysis x).procedure.rejection_measurable⟩
  level := fun x => x.2.value
  typeI := Checked.established
    (fun x => ((twoSidedAnalysis x).typeIClaim (Core.Compatibility.fixed _) (x.2.value : ℝ)).statement)
    (fun x => Fisher.typeI_statement x.1 _ (Core.Compatibility.fixed _) x.2)
  bound := fun _ h => h
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

def modelOfLaw {Θ Ω : Type} [MeasurableSpace Ω] (law : Θ → Measure Ω)
    (probability : ∀ θ, IsProbabilityMeasure (law θ)) : Core.Model Θ Ω where
  law := law
  probability := probability
  admissible := Set.univ
  admissible_measurable := MeasurableSet.univ
  supported := fun θ => by
    have := probability θ
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one]

abbrev StudyLevel := ℕ × SignificanceLevel

def mixtureModule : ExactModule where
  Input := StudyLevel
  Parameter := unitInterval × unitInterval × unitInterval
  Outcome := Association.Table
  law := fun x => modelOfLaw
    (fun θ => Association.mixture x.1 θ.1 (fun k => productBinomial (x.1 - k) k θ.2.1 θ.2.2))
    (fun _ => inferInstance)
  null := fun _ θ => θ.2.1 = θ.2.2
  procedure := fun x => ⟨Association.mixtureRejection x.1 x.2.value,
    (Set.to_countable _).measurableSet⟩
  level := fun x => x.2.value
  typeI := Checked.established
    (fun x => ∀ q p, (Association.mixtureLaw x.1 q p).real
      (Association.mixtureRejection x.1 x.2.value) ≤ (x.2.value : ℝ))
    (fun x q p => Association.mixture_typeI_le_alpha x.1 q p x.2.value x.2.nonnegative)
  bound := by
    intro x h θ null
    obtain ⟨q, pc, pt⟩ := θ
    change pc = pt at null
    subst pt
    change (Association.mixture x.1 q (fun k => productBinomial (x.1 - k) k pc pc)).real _ ≤ _
    exact h q pc
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

def matchedModule : ExactModule where
  Input := StudyLevel
  Parameter := unitInterval × unitInterval
  Outcome := ℕ × ℕ
  law := fun x => modelOfLaw (fun θ => Matched.pairsLaw x.1 θ.1 θ.2)
    (fun θ => ⟨Matched.pairsLaw_univ x.1 θ.1 θ.2⟩)
  null := fun _ θ => θ.2 = Matched.half
  procedure := fun x => ⟨Matched.pairsRejection x.1 x.2.value, (Set.to_countable _).measurableSet⟩
  level := fun x => x.2.value
  typeI := Checked.established
    (fun x => ∀ δ, (Matched.pairsLaw x.1 δ Matched.half).real
      (Matched.pairsRejection x.1 x.2.value) ≤ (x.2.value : ℝ))
    (fun x δ => Matched.typeI x.1 δ x.2.value (by exact_mod_cast x.2.nonnegative))
  bound := by
    intro x h θ null
    change θ.2 = Matched.half at null
    change (Matched.pairsLaw x.1 θ.1 θ.2).real _ ≤ _
    rw [null]
    exact h θ.1
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

structure RateRecord where
  share : unitInterval
  counts : ℕ × ℕ

instance : MeasurableSpace RateRecord := ⊤

def rateRejection (level : SignificanceLevel) : Set RateRecord :=
  {r | r.counts ∈ Incidence.given (fun n => Incidence.rejectionAt r.share n level.value)}

/-- The test conditions on the known exposure share. Include it in the record so
the rejection event can be read from the record alone. -/
def incidenceModule : ExactModule where
  Input := SignificanceLevel
  Parameter := NNReal × unitInterval × unitInterval
  Outcome := RateRecord
  law := fun _ => modelOfLaw
    (fun θ => (Incidence.ratesLaw θ.1 θ.2.2).map (RateRecord.mk θ.2.1))
    (fun θ => (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr
      ⟨Incidence.compound_univ _ _⟩)
  null := fun _ θ => θ.2.1 = θ.2.2
  procedure := fun x => ⟨rateRejection x, trivial⟩
  level := SignificanceLevel.value
  typeI := Checked.established
    (fun x => ∀ total share, (Incidence.ratesLaw total share).real
      (Incidence.given (fun n => Incidence.rejectionAt share n x.value)) ≤ (x.value : ℝ))
    (fun x total share => Incidence.typeI total share x.value (by exact_mod_cast x.nonnegative))
  bound := by
    intro x h θ null
    obtain ⟨total, share, alternative⟩ := θ
    change share = alternative at null
    subst alternative
    change ((Incidence.ratesLaw total share).map (RateRecord.mk share)).real (rateRejection x) ≤ _
    rw [measureReal_def, Measure.map_apply (measurable_of_countable _)
      (show MeasurableSet (rateRejection x) from trivial)]
    exact h total share
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

namespace AsymptoticMcNemar

structure Input where
  n : ℕ
  alpha : SignificanceLevel
  cutoff : ℚ

def region (x : Input) : Set (ℕ × ℕ) :=
  Modules.McNemarAsymptotic.rejection x.n x.cutoff.num.toNat x.cutoff.den

private theorem alpha_eq (alpha : SignificanceLevel) :
    (alpha.value : ℝ) = (alpha.value.num.toNat : ℝ) / alpha.value.den := by
  have nonnegative : 0 ≤ alpha.value.num := Rat.num_nonneg.mpr alpha.nonnegative
  have cast : (alpha.value.num.toNat : ℝ) = (alpha.value.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg nonnegative
  rw [cast, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]

def typeI : Checked Input where
  Statement := fun x => ∀ q, (Matched.pairsLaw x.n q Matched.half).real (region x) ≤ (x.alpha.value : ℝ)
  Hint := List ℕ
  empty := []
  check := fun x h => Modules.McNemarAsymptotic.check x.n x.cutoff.num.toNat x.cutoff.den
    x.alpha.value.num.toNat x.alpha.value.den h
  sound := by
    intro x h checked q
    rw [alpha_eq]
    exact Modules.McNemarAsymptotic.typeI_of_check _ _ _ _ _ _ x.alpha.value.den_pos checked q

def checkCounterexample (x : Input) (rate reported : ℚ) : Bool :=
  decide (0 ≤ rate ∧ rate ≤ 1 ∧ reported =
    (Modules.McNemarAsymptotic.numerator x.n x.cutoff.num.toNat x.cutoff.den
      rate.num.toNat (rate.den - rate.num.toNat) : ℚ) /
      (Modules.McNemarAsymptotic.denominator x.n rate.den : ℚ)) &&
    Modules.McNemarAsymptotic.checkCounterexample x.n x.cutoff.num.toNat x.cutoff.den
      x.alpha.value.num.toNat x.alpha.value.den rate.num.toNat rate.den

theorem counterexample (x : Input) (rate reported : ℚ)
    (checked : checkCounterexample x rate reported = true) : ¬ typeI.Statement x := by
  obtain ⟨_, point⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨q, excess⟩ := Modules.McNemarAsymptotic.counterexample _ _ _ _ _ _ _
    x.alpha.value.den_pos point
  intro claim
  exact (not_le_of_gt excess) ((claim q).trans_eq (alpha_eq x.alpha))

def moduleSpec : ExactModule where
  Input := Input
  Parameter := unitInterval × unitInterval
  Outcome := ℕ × ℕ
  law := fun x => modelOfLaw (fun θ => Matched.pairsLaw x.n θ.1 θ.2)
    (fun θ => ⟨Matched.pairsLaw_univ x.n θ.1 θ.2⟩)
  null := fun _ θ => θ.2 = Matched.half
  procedure := fun x => ⟨region x, .of_discrete⟩
  level := fun x => x.alpha.value
  typeI := typeI
  bound := by
    intro x h θ null
    change θ.2 = Matched.half at null
    change (Matched.pairsLaw x.n θ.1 θ.2).real _ ≤ _
    rw [null]
    exact h θ.1
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

end AsymptoticMcNemar

def ExactStudyKind.moduleSpec : ExactStudyKind → ExactModule
  | .fisherGroups => fisherGroupsModule
  | .fisherMixture => mixtureModule
  | .matched => matchedModule
  | .matchedAsymptotic _ => AsymptoticMcNemar.moduleSpec
  | .incidence => incidenceModule

def ExactStudyKind.input (kind : ExactStudyKind) (study : Study) (alpha : SignificanceLevel) :
    kind.moduleSpec.Input :=
  match kind with
  | .fisherGroups => (study.groupSizes, alpha)
  | .fisherMixture => (study.n.getD 0, alpha)
  | .matched => (study.pairs.getD 0, alpha)
  | .matchedAsymptotic cutoff => ⟨study.pairs.getD 0, alpha, cutoff⟩
  | .incidence => alpha

theorem ExactStudyKind.input_level (kind : ExactStudyKind) (study : Study)
    (alpha : SignificanceLevel) : kind.moduleSpec.level (kind.input study alpha) = alpha.value := by
  cases kind <;> rfl

namespace OneSided

open FisherOneSided

abbrev Input := FixedSampleDesign × SignificanceLevel

def levelNum (x : Input) : ℕ := x.2.value.num.toNat

theorem level_eq (x : Input) : x.2.value = (levelNum x : ℚ) / x.2.value.den := by
  unfold levelNum
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr x.2.nonnegative)]
  exact (Rat.num_div_den _).symm

def regionCheck (x : Input) (bounds : List ℕ) : Prop :=
  HintsValid x.1.nControl x.1.nTreatment (levelNum x) x.2.value.den bounds

instance (x : Input) (bounds : List ℕ) : Decidable (regionCheck x bounds) :=
  inferInstanceAs (Decidable (HintsValid ..))

def levelCheck (x : Input) (bounds : List ℕ) : Prop :=
  regionCheck x bounds ∧ HintSections x.1.nControl x.1.nTreatment bounds

instance (x : Input) (bounds : List ℕ) : Decidable (levelCheck x bounds) :=
  inferInstanceAs (Decidable (_ ∧ _))

def typeI : Checked Input where
  Statement := fun x => ((analysis x.1 x.2).typeIClaim (x.2.value : ℝ)).statement
  Hint := List ℕ
  empty := []
  check := fun x bounds => decide (levelCheck x bounds)
  sound := by
    intro x bounds checked
    have h := of_decide_eq_true checked
    exact typeI_of_hints x.1 x.2 _ _ x.2.value.den_pos (level_eq x) bounds h.1 h.2

def pValue (x : Input) (observed : ObservedCounts) : ℚ :=
  lowerPValue x.1.nControl x.1.nTreatment (observed.control + observed.treatment) observed.control

def verdict : Bool → Prop
  | true => True
  | false => False

instance (reject : Bool) : Decidable (verdict reject) :=
  match reject with
  | true => isTrue trivial
  | false => isFalse id

def result : Checked (Input × ObservedCounts × ReportedResult) where
  Statement := fun (x, observed, found) =>
    (0 < x.1.nControl ∧ 0 < x.1.nTreatment ∧
      observed.control ≤ x.1.nControl ∧ observed.treatment ≤ x.1.nTreatment) ∧
    pValue x observed = found.pValue.value ∧
    (pValue x observed ≤ x.2.value ↔ verdict found.reject) ∧ typeI.Statement x
  Hint := List ℕ
  empty := []
  check := fun (x, observed, found) bounds =>
    decide (observed.control ≤ x.1.nControl ∧ observed.treatment ≤ x.1.nTreatment ∧
      lowerWeight x.1.nControl x.1.nTreatment (observed.control + observed.treatment)
        observed.control * found.pValue.den = found.pValue.num *
          Nat.fast_choose (x.1.nControl + x.1.nTreatment) (observed.control + observed.treatment) ∧
      (found.pValue.value ≤ x.2.value ↔ verdict found.reject) ∧ levelCheck x bounds)
  sound := by
    rintro ⟨x, observed, found⟩ bounds checked
    have h := of_decide_eq_true checked
    have pv : pValue x observed = found.pValue.value :=
      lowerPValue_eq_of_cross_product _ _ _ _ _ _ (Nat.add_le_add h.1 h.2.1)
        found.pValue.positive h.2.2.1
    exact ⟨⟨x.1.controlPositive, x.1.treatmentPositive, h.1, h.2.1⟩, pv,
      pv ▸ h.2.2.2.1, typeI.sound x bounds (decide_eq_true h.2.2.2.2)⟩

def BinomialPoint.parameter (point : BinomialPoint) : TwoArmBinomial.Parameters :=
  FisherPower.ratePoint point.control.num point.control.den point.treatment.num point.treatment.den
    point.control.bounded point.control.positive point.treatment.bounded point.treatment.positive

def powerNumerator (x : Input) (point : BinomialPoint) (bounds : List ℕ) : ℕ :=
  rejectionNumerator x.1.nControl x.1.nTreatment point.control.num point.control.den
    point.treatment.num point.treatment.den (hintReject bounds)

def powerCheck (x : Input) (point : BinomialPoint) (target : ProbabilityFraction)
    (bounds : List ℕ) : Prop :=
  target.num * rejectionDenominator x.1.nControl x.1.nTreatment
    point.control.den point.treatment.den ≤ powerNumerator x point bounds * target.den

instance (x : Input) (point : BinomialPoint) (target : ProbabilityFraction) (bounds : List ℕ) :
    Decidable (powerCheck x point target bounds) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem power_sound (x : Input) (point : BinomialPoint) (target : ProbabilityFraction)
    (bounds : List ℕ) (region : regionCheck x bounds) (checked : powerCheck x point target bounds) :
    ((analysis x.1 x.2).powerClaim (fun θ => θ = BinomialPoint.parameter point)
      ((target.num : ℝ) / target.den)).statement := by
  apply power_of_check x.1 x.2 _ _ x.2.value.den_pos (level_eq x)
    _ _ _ _ point.control.bounded point.control.positive point.treatment.bounded
    point.treatment.positive _ _ target.positive
  rw [rejectionNumerator_hint _ _ _ _ _ _ _ _ bounds region]
  exact checked

def power : Checked (Input × BinomialPoint × ProbabilityFraction) where
  Statement := fun (x, point, target) =>
    ((analysis x.1 x.2).powerClaim (fun θ => θ = BinomialPoint.parameter point)
      ((target.num : ℝ) / target.den)).statement
  Hint := List ℕ
  empty := []
  check := fun (x, point, target) bounds =>
    decide (regionCheck x bounds ∧ powerCheck x point target bounds)
  sound := by
    rintro ⟨x, point, target⟩ bounds checked
    have h := of_decide_eq_true checked
    exact power_sound x point target bounds h.1 h.2

def moduleSpec : ExactModule where
  Input := Input
  Parameter := TwoArmBinomial.Parameters
  Outcome := TwoArmBinomial.Counts
  law := fun x => TwoArmBinomial.model x.1
  null := fun x => (analysis x.1 x.2).hypothesis
  procedure := fun x => ⟨(analysis x.1 x.2).rejection, (analysis x.1 x.2).rejection_measurable⟩
  level := fun x => x.2.value
  typeI := typeI
  bound := by
    intro x h θ holds
    rw [← Core.Policy.fixed_law]
    exact h θ holds
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := some result
  interval := none
  power := some power

end OneSided

namespace Margin

open DifferenceTest

structure Input where
  sizes : FixedSampleDesign
  alpha : SignificanceLevel
  margin : ℚ
  thresholds : List ℕ

structure Hints where
  grid : ℕ
  up : ℕ
  down : ℕ
  cells : List ℕ

def Hints.value (h : Hints) : ℚ := ((h.up : ℚ) - h.down) / h.grid

def typeI : Checked Input where
  Statement := fun x =>
    ((analysis x.sizes x.thresholds x.margin).typeIClaim (x.alpha.value : ℝ)).statement
  Hint := Hints
  empty := ⟨0, 0, 0, []⟩
  check := fun x h =>
    decide (Increasing x.sizes.nControl x.sizes.nTreatment x.thresholds ∧
      0 < h.grid ∧ (h.up = 0 ∨ h.down = 0) ∧ x.margin = h.value ∧ h.cells ≠ [] ∧
      lastOf h.down h.cells = h.grid) &&
    cellsOk (cellCheck x.sizes.nControl x.sizes.nTreatment x.thresholds h.grid h.up h.down
      (OneSided.levelNum (x.sizes, x.alpha)) x.alpha.value.den) h.down h.cells
  sound := by
    intro x h checked
    obtain ⟨structural, cells⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨increasing, grid, one, eq, nonempty, complete⟩ := of_decide_eq_true structural
    have level := typeI_of_cells x.sizes x.thresholds increasing h.grid grid h.up h.down one
      (OneSided.levelNum (x.sizes, x.alpha)) x.alpha.value.den x.alpha.value.den_pos
      h.cells nonempty cells complete
    change ((analysis x.sizes x.thresholds x.margin).typeIClaim (x.alpha.value : ℝ)).statement
    rw [eq]
    intro θ holds
    apply le_trans (level θ holds)
    have same := OneSided.level_eq (x.sizes, x.alpha)
    have cast := congrArg (fun q : ℚ => (q : ℝ)) same
    push_cast at cast
    exact cast.ge

def moduleSpec : ExactModule where
  Input := Input
  Parameter := TwoArmBinomial.Parameters
  Outcome := TwoArmBinomial.Counts
  law := fun x => TwoArmBinomial.model x.sizes
  null := fun x => (analysis x.sizes x.thresholds x.margin).hypothesis
  procedure := fun x => ⟨(analysis x.sizes x.thresholds x.margin).rejection,
    (analysis x.sizes x.thresholds x.margin).rejection_measurable⟩
  level := fun x => x.alpha.value
  typeI := typeI
  bound := by
    intro x h θ holds
    rw [← Core.Policy.fixed_law]
    exact h θ holds
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

end Margin

namespace ProportionZExact

structure Input where
  sizes : FixedSampleDesign
  alpha : SignificanceLevel
  squaredCutoff : ℚ

def region (pooled : Bool) (x : Input) : Set TwoArmBinomial.Counts :=
  Modules.Wald.region x.sizes.nControl x.squaredCutoff.num.toNat x.squaredCutoff.den
    (Modules.Wald.varianceAdjustment pooled x.squaredCutoff.num.toNat)

def typeI (pooled : Bool) : Checked Input where
  Statement := fun x => ∀ θ, TwoArmBinomial.equalProportions θ →
    ((TwoArmBinomial.model x.sizes).law θ).real (region pooled x) ≤ (x.alpha.value : ℝ)
  Hint := Modules.Wald.Certificate
  empty := ⟨[], []⟩
  check := fun x h => decide (x.sizes.nTreatment = x.sizes.nControl) &&
    Modules.Wald.check x.sizes.nControl x.squaredCutoff.num.toNat x.squaredCutoff.den
      x.alpha.value.num.toNat x.alpha.value.den h
      (Modules.Wald.varianceAdjustment pooled x.squaredCutoff.num.toNat)
  sound := by
    intro x h ok θ null
    obtain ⟨balanced, cells⟩ := Bool.and_eq_true_iff.mp ok
    have level := Modules.Wald.level x.sizes (of_decide_eq_true balanced) _ _
      x.alpha.value.num.toNat x.alpha.value.den x.squaredCutoff.den_pos x.alpha.value.den_pos
      h (Modules.Wald.varianceAdjustment pooled x.squaredCutoff.num.toNat) cells θ null
    have alpha := congrArg (fun q : ℚ => (q : ℝ)) (OneSided.level_eq (x.sizes, x.alpha))
    simp only [OneSided.levelNum, Rat.cast_div, Rat.cast_natCast] at alpha
    exact level.trans alpha.ge

def moduleSpec (pooled : Bool) : ExactModule where
  Input := Input
  Parameter := TwoArmBinomial.Parameters
  Outcome := TwoArmBinomial.Counts
  law := fun x => TwoArmBinomial.model x.sizes
  null := fun _ => TwoArmBinomial.equalProportions
  procedure := fun x => ⟨region pooled x, .of_discrete⟩
  level := fun x => x.alpha.value
  typeI := typeI pooled
  bound := fun _ h => h
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

end ProportionZExact

namespace FarringtonManningExact

open Modules.FarringtonManning

structure Input where
  sizes : FixedSampleDesign
  alpha : SignificanceLevel
  margin : ℚ
  cutoff : ℚ

structure Hint where
  region : RegionHint
  grid : ℕ
  shift : ℕ
  cells : List ℕ

def typeI : Checked Input where
  Statement := fun x => ((analysis x.sizes (-x.margin) x.cutoff).typeIClaim (x.alpha.value : ℝ)).statement
  Hint := Hint
  empty := ⟨⟨[], []⟩, 0, 0, []⟩
  check := fun x h => regionCheck x.sizes (-x.margin) x.cutoff h.region true &&
    Margin.typeI.check ⟨x.sizes, x.alpha, -(-x.margin), h.region.thresholds⟩
      ⟨h.grid, 0, h.shift, h.cells⟩
  sound := by
    intro x h ok
    obtain ⟨region, cells⟩ := Bool.and_eq_true_iff.mp ok
    exact typeI_of_region _ _ _ _ region _ (Margin.typeI.sound _ _ cells)

def witnessValue (x : Input) (h : RegionHint) (rate : ℚ) : ℚ :=
  let treatment := rate + x.margin
  let nc := x.sizes.nControl
  let nt := x.sizes.nTreatment
  (DifferenceTest.thresholdNumerator nc nt rate.num.toNat rate.den
    treatment.num.toNat treatment.den h.thresholds : ℚ) /
    (rejectionDenominator nc nt rate.den treatment.den : ℚ)

def checkCounterexample (x : Input) (h : RegionHint) (rate reported : ℚ) : Bool :=
  decide (0 ≤ rate ∧ rate ≤ 1 ∧ 0 ≤ rate + x.margin ∧ rate + x.margin ≤ 1 ∧
    reported = witnessValue x h rate ∧ x.alpha.value < reported) &&
    regionCheck x.sizes (-x.margin) x.cutoff h false

private theorem rational_rate (p : ℚ) (h0 : 0 ≤ p) :
    (p.num.toNat : ℚ) / p.den = p := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr h0), Rat.num_div_den]

private theorem point (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : p.num.toNat ≤ p.den := by
  have h : (p.num.toNat : ℚ) / p.den ≤ 1 := (rational_rate p h0).trans_le h1
  rw [div_le_one (by exact_mod_cast p.den_pos : (0 : ℚ) < p.den)] at h
  exact_mod_cast h

theorem counterexample (x : Input) (h : RegionHint) (rate reported : ℚ)
    (checked : checkCounterexample x h rate reported = true) : ¬ typeI.Statement x := by
  obtain ⟨info, region⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨h0, h1, t0, t1, reported_eq, above⟩ := of_decide_eq_true info
  let t := rate + x.margin
  let pc := ratPoint rate.num.toNat rate.den (point rate h0 h1) rate.den_pos
  let pt := ratPoint t.num.toNat t.den (point t t0 t1) t.den_pos
  have cp : (pc : ℝ) = (rate : ℝ) := by
    simpa [pc, ratPoint] using congrArg (fun q : ℚ => (q : ℝ)) (rational_rate rate h0)
  have tp : (pt : ℝ) = (t : ℝ) := by
    simpa [pt, ratPoint] using congrArg (fun q : ℚ => (q : ℝ)) (rational_rate t t0)
  have null : (analysis x.sizes (-x.margin) x.cutoff).hypothesis (pc, pt) := by
    change (pt : ℝ) - (pc : ℝ) ≤ ((-(-x.margin) : ℚ) : ℝ)
    rw [cp, tp]
    simp [t]
  intro claim
  have cap := claim (pc, pt) null
  rw [Core.Policy.fixed_law] at cap
  have lower := probability_ge_of_region x.sizes (-x.margin) x.cutoff h region pc pt
  have eq : (productBinomial x.sizes.nControl x.sizes.nTreatment pc pt).real
      (DifferenceTest.region x.sizes.nTreatment h.thresholds) = (reported : ℝ) := by
    rw [reported_eq]
    rw [DifferenceTest.rejection_probability]
    simp only [witnessValue, DifferenceTest.thresholdNumerator_eq, Rat.cast_div, Rat.cast_natCast]
    rfl
  rw [eq] at lower
  exact (not_le_of_gt (show (x.alpha.value : ℝ) < (reported : ℝ) by exact_mod_cast above))
    (lower.trans cap)

def moduleSpec : ExactModule where
  Input := Input
  Parameter := TwoArmBinomial.Parameters
  Outcome := TwoArmBinomial.Counts
  law := fun x => TwoArmBinomial.model x.sizes
  null := fun x => (analysis x.sizes (-x.margin) x.cutoff).hypothesis
  procedure := fun x => ⟨rejection x.sizes (-x.margin) x.cutoff, .of_discrete⟩
  level := fun x => x.alpha.value
  typeI := typeI
  bound := by
    intro x h θ holds
    rw [← Core.Policy.fixed_law]
    exact h θ holds
  Observation := ObservedCounts
  Report := ReportedResult
  Point := BinomialPoint
  Target := ProbabilityFraction
  Endpoints := PUnit
  result := none
  interval := none
  power := none

end FarringtonManningExact

def ExactKind.moduleSpec : ExactKind → ExactModule
  | .fisherOneSided => OneSided.moduleSpec
  | .margin .. => Margin.moduleSpec
  | .proportionZ pooled _ => ProportionZExact.moduleSpec pooled
  | .farringtonManning .. => FarringtonManningExact.moduleSpec

def ExactKind.input (kind : ExactKind) (sizes : FixedSampleDesign) (alpha : SignificanceLevel) :
    kind.moduleSpec.Input :=
  match kind with
  | .fisherOneSided => (sizes, alpha)
  | .margin value thresholds => ⟨sizes, alpha, value, thresholds⟩
  | .proportionZ _ cutoff => ⟨sizes, alpha, cutoff⟩
  | .farringtonManning value cutoff => ⟨sizes, alpha, value, cutoff⟩

theorem ExactKind.input_level (kind : ExactKind) (sizes : FixedSampleDesign)
    (alpha : SignificanceLevel) : kind.moduleSpec.level (kind.input sizes alpha) = alpha.value := by
  cases kind <;> rfl

end

end StatClaim.Semantics
