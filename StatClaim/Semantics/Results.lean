module

public import StatClaim.Semantics.Exact
public import StatClaim.Modules.OneSampleBinomial
public import StatClaim.Modules.TwoStageBinomial
public import StatClaim.Computation

/-! Kernel checks for the values and decisions reported for exact observations. -/

@[expose] public section
set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Modules

noncomputable section

def ProbabilityFraction.point (p : ProbabilityFraction) : unitInterval :=
  ratPoint p.num p.den p.bounded p.positive

def ProbabilityFraction.real (p : ProbabilityFraction) : ℝ := (p.num : ℝ) / p.den

theorem ProbabilityFraction.real_cast (p : ProbabilityFraction) : (p.value : ℝ) = p.real := by
  simp [ProbabilityFraction.value, ProbabilityFraction.real]

def StageRule.design (rule : StageRule) (sizes : Stages) : TwoStageBinomial.Design :=
  match rule with
  | .threshold r1 r2 => TwoStageBinomial.thresholdDesign sizes.first sizes.second r1 r2
  | .posterior a b reference interim final =>
    TwoStageBinomial.posteriorDesign sizes.first sizes.second a b reference.num reference.den
      interim.num interim.den final.num final.den

theorem StageRule.monotone (rule : StageRule) (sizes : Stages) : (rule.design sizes).Monotone := by
  cases rule with
  | threshold => exact TwoStageBinomial.thresholdDesign_monotone _ _ _ _
  | posterior => exact TwoStageBinomial.posteriorDesign_monotone _ _ _ _ _ _ _ _ _ _

def countsFit (n m : ℕ) (o : ObservedCounts) : Prop := o.control ≤ n ∧ o.treatment ≤ m

instance (n m : ℕ) (o : ObservedCounts) : Decidable (countsFit n m o) :=
  inferInstanceAs (Decidable (_ ∧ _))

def tablePValue (n m : ℕ) (o : ObservedCounts) : ℚ :=
  hypergeometricPValue n m (o.control + o.treatment) o.control

def tableMass (n m : ℕ) (o : ObservedCounts) : ℚ :=
  hypergeometricMass n m (o.control + o.treatment) o.control

def tableCheck (n m : ℕ) (o : ObservedCounts) (r : ReportedTable) : Prop :=
  let total := o.control + o.treatment
  let den := Nat.fast_choose (n + m) total
  checkedExtremeWeight n m total o.control * r.pValue.den = r.pValue.num * den ∧
  checkedWeight n m total o.control * r.mass.den = r.mass.num * den

instance (n m : ℕ) (o : ObservedCounts) (r : ReportedTable) : Decidable (tableCheck n m o r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem table_sound (n m : ℕ) (o : ObservedCounts) (r : ReportedTable)
    (fits : countsFit n m o) (checked : tableCheck n m o r) :
    tablePValue n m o = r.pValue.value ∧ tableMass n m o = r.mass.value := by
  have total := Nat.add_le_add fits.1 fits.2
  exact ⟨hypergeometricPValue_eq_of_cross_product _ _ _ _ _ _ total r.pValue.positive checked.1,
    hypergeometricMass_eq_of_cross_product _ _ _ _ _ _ total r.mass.positive checked.2⟩

theorem table_decision (n m : ℕ) (o : ObservedCounts) (r : ReportedTable) (alpha : ℚ)
    (fits : countsFit n m o) (value : tablePValue n m o = r.pValue.value)
    (decision : r.pValue.value ≤ alpha ↔ OneSided.verdict r.reject) :
    (o.control, o.treatment) ∈ fisherRejectionRegionAt n m alpha ↔ OneSided.verdict r.reject := by
  simp only [fisherRejectionRegionAt, Finset.mem_filter, binomialCountSupport, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff, fits.1, fits.2, and_self, true_and]
  change tablePValue n m o ≤ alpha ↔ _
  exact value ▸ decision

structure FisherResultInput where
  sizes : FixedSampleDesign
  alpha : SignificanceLevel
  observed : ObservedCounts
  reported : ReportedTable
  low : ℕ
  high : ℕ
  bound : ProbabilityFraction

def fisherResult : Checked FisherResultInput where
  Statement := fun x =>
    let n := x.sizes.nControl
    let m := x.sizes.nTreatment
    let o := x.observed
    let total := o.control + o.treatment
    let r := x.reported
    (0 < n ∧ 0 < m ∧ countsFit n m o) ∧
    (∀ k, k ∈ hypergeometricSupport n m total ↔ x.low ≤ k ∧ k ≤ x.high) ∧
    tablePValue n m o = r.pValue.value ∧ tableMass n m o = r.mass.value ∧
    ((o.control, o.treatment) ∈ fisherRejectionRegionAt n m x.alpha.value ↔
      OneSided.verdict r.reject) ∧
    (∀ p, (fisherNullLaw n m p).real (fisherRejectionRegionAt n m x.alpha.value) ≤
      x.bound.real)
  Hint := PUnit
  empty := PUnit.unit
  check := fun x _ =>
    let n := x.sizes.nControl
    let m := x.sizes.nTreatment
    let o := x.observed
    let total := o.control + o.treatment
    let r := x.reported
    decide (countsFit n m o ∧ x.low = total - m ∧ x.high = min n total ∧
      x.alpha.value = x.bound.value ∧
      tableCheck n m o r ∧ (r.pValue.value ≤ x.alpha.value ↔ OneSided.verdict r.reject))
  sound := by
    intro x _ checked
    obtain ⟨fits, low, high, equal, table, decision⟩ := of_decide_eq_true checked
    have values := table_sound _ _ _ _ fits table
    refine ⟨⟨x.sizes.controlPositive, x.sizes.treatmentPositive, fits⟩, ?_, values.1, values.2,
      table_decision _ _ _ _ _ fits values.1 decision, ?_⟩
    · intro k
      simp only [hypergeometricSupport, Finset.mem_filter, Finset.mem_range]
      omega
    · intro p
      rw [← x.bound.real_cast, ← equal]
      exact fisher_typeI_error_le_alpha _ _ p _ x.alpha.nonnegative

def marginResult : Checked (Margin.Input × ObservedCounts × Bool × ProbabilityFraction) where
  Statement := fun (x, o, r, bound) =>
    (x.sizes.nControl = x.sizes.nControl ∧ x.sizes.nTreatment = x.sizes.nTreatment ∧
      0 < x.sizes.nControl ∧ 0 < x.sizes.nTreatment) ∧
    ((DifferenceTest.analysis x.sizes x.thresholds x.margin).typeIClaim
      bound.real).statement ∧
    DifferenceTest.rejects x.sizes.nTreatment x.thresholds o.control o.treatment = r
  Hint := Margin.Hints
  empty := Margin.typeI.empty
  check := fun (x, o, r, bound) h => Margin.typeI.check x h &&
    decide (x.alpha.value = bound.value ∧ countsFit x.sizes.nControl x.sizes.nTreatment o ∧
      DifferenceTest.rejects x.sizes.nTreatment x.thresholds o.control o.treatment = r)
  sound := by
    rintro ⟨x, o, r, bound⟩ h checked
    obtain ⟨level, decision⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨same, _, result⟩ := of_decide_eq_true decision
    have cast : (x.alpha.value : ℝ) = bound.real := by rw [← bound.real_cast, same]
    exact ⟨⟨rfl, rfl, x.sizes.controlPositive, x.sizes.treatmentPositive⟩,
      cast ▸ Margin.typeI.sound x h level, result⟩

def groupsResult : Checked (Study × SignificanceLevel × AssociationTable × ReportedTable) where
  Statement := fun (study, alpha, table, r) =>
    let sizes := study.groupSizes
    let (n, m, o) := table.sides
    (sizes.nControl = n ∧ sizes.nTreatment = m ∧ 0 < sizes.nControl ∧ 0 < sizes.nTreatment) ∧
    (∀ p, (fisherNullLaw sizes.nControl sizes.nTreatment p).real
      (fisherRejectionRegionAt sizes.nControl sizes.nTreatment alpha.value) ≤ (alpha.value : ℝ)) ∧
    tablePValue n m o = r.pValue.value ∧ tableMass n m o = r.mass.value ∧
    ((o.control, o.treatment) ∈ fisherRejectionRegionAt n m alpha.value ↔ OneSided.verdict r.reject)
  Hint := PUnit
  empty := PUnit.unit
  check := fun (study, alpha, table, r) _ =>
    let sizes := study.groupSizes
    let (n, m, o) := table.sides
    decide (study = table.model ∧ sizes.nControl = n ∧ sizes.nTreatment = m ∧ countsFit n m o ∧
      tableCheck n m o r ∧ (r.pValue.value ≤ alpha.value ↔ OneSided.verdict r.reject))
  sound := by
    rintro ⟨study, alpha, table, r⟩ _ checked
    obtain ⟨_, n, m, fits, weights, decision⟩ := of_decide_eq_true checked
    have values := table_sound _ _ _ _ fits weights
    exact ⟨⟨n, m, study.groupSizes.controlPositive, study.groupSizes.treatmentPositive⟩,
      fun p => Association.groups_typeI_le_alpha _ _ p _ alpha.nonnegative, values.1, values.2,
      table_decision _ _ _ _ _ fits values.1 decision⟩

def mixtureResult : Checked (Study × SignificanceLevel × AssociationTable × ReportedTable) where
  Statement := fun (study, alpha, table, r) =>
    let total := study.n.getD 0
    let (n, m, o) := table.sides
    (total = table.total ∧ 0 < total) ∧
    (∀ q p, Association.mixtureLaw total q p Set.univ = 1) ∧
    (∀ q p, (Association.mixtureLaw total q p).real
      (Association.mixtureRejection total alpha.value) ≤ (alpha.value : ℝ)) ∧
    tablePValue n m o = r.pValue.value ∧ tableMass n m o = r.mass.value ∧
    ((table.exposed, o.control, o.treatment) ∈ Association.mixtureRejection total alpha.value ↔
      OneSided.verdict r.reject)
  Hint := PUnit
  empty := PUnit.unit
  check := fun (study, alpha, table, r) _ =>
    let total := study.n.getD 0
    let (n, m, o) := table.sides
    decide (study = table.model ∧ total = table.total ∧ 0 < total ∧
      n = total - table.exposed ∧ m = table.exposed ∧ table.exposed ≤ total ∧ countsFit n m o ∧
      tableCheck n m o r ∧ (r.pValue.value ≤ alpha.value ↔ OneSided.verdict r.reject))
  sound := by
    rintro ⟨study, alpha, table, r⟩ _ checked
    obtain ⟨_, total, positive, n, m, exposed, fits, weights, decision⟩ := of_decide_eq_true checked
    have values := table_sound _ _ _ _ fits weights
    refine ⟨⟨total, positive⟩, Association.mixtureLaw_univ _, fun q p =>
      Association.mixture_typeI_le_alpha _ q p _ alpha.nonnegative, values.1, values.2, ?_⟩
    change (_ ∧ _) ↔ _
    have conclusion := table_decision _ _ _ _ _ fits values.1 decision
    rw [n, m] at conclusion
    exact (and_iff_right exposed).trans conclusion

def tailCheck (n count : ℕ) (p : ProbabilityFraction) (alpha : ℚ) (r : ReportedTails) : Prop :=
  OneSampleBinomial.tailNumerator n p.num p.den count = r.upper ∧
  BinomialInterval.lowerNumerator n p.num p.den count = r.lower ∧
  r.pValue.value = min 1 (((2 * min r.upper r.lower : ℕ) : ℚ) / (p.den ^ n : ℕ)) ∧
  (((2 * min r.upper r.lower : ℕ) : ℚ) / (p.den ^ n : ℕ) ≤ alpha ↔ OneSided.verdict r.reject)

instance (n count : ℕ) (p : ProbabilityFraction) (alpha : ℚ) (r : ReportedTails) :
    Decidable (tailCheck n count p alpha r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem tail_decision (n count : ℕ) (p : ProbabilityFraction) (alpha : ℚ) (r : ReportedTails)
    (checked : tailCheck n count p alpha r) :
    count ∈ Incidence.rejectionAt p.point n (alpha : ℝ) ↔ OneSided.verdict r.reject := by
  simp only [Incidence.rejectionAt, Set.mem_ofPred_eq, ProbabilityFraction.point,
    BinomialInterval.upper_tail_ratPoint, BinomialInterval.lower_tail_ratPoint,
    checked.1, checked.2.1]
  have denominator : (0 : ℝ) ≤ (p.den ^ n : ℕ) := by positivity
  rw [min_div_div_right denominator, ← mul_div_assoc]
  have bound : (↑((((2 * min r.upper r.lower : ℕ) : ℚ) / (p.den ^ n : ℕ)) : ℚ) : ℝ) ≤
      (alpha : ℝ) ↔ OneSided.verdict r.reject := by
    rw [Rat.cast_le]
    exact checked.2.2.2
  push_cast at bound
  simpa only [Nat.cast_pow] using bound

def halfFraction : ProbabilityFraction := ⟨1, 2, by decide, by decide⟩

def matchedResult : Checked (Study × SignificanceLevel × PairCounts × ReportedTails) where
  Statement := fun (study, alpha, counts, r) =>
    let pairs := study.pairs.getD 0
    let d := counts.discordant
    let x := counts.caseOnly
    (pairs = counts.total ∧ 0 < pairs) ∧
    (∀ δ π, Matched.pairsLaw pairs δ π Set.univ = 1) ∧
    (∀ δ, (Matched.pairsLaw pairs δ Matched.half).real
      (Matched.pairsRejection pairs alpha.value) ≤ (alpha.value : ℝ)) ∧
    (OneSampleBinomial.tailNumerator d 1 2 x = r.upper ∧
      BinomialInterval.lowerNumerator d 1 2 x = r.lower) ∧
    ((d, x) ∈ Matched.pairsRejection pairs alpha.value ↔ OneSided.verdict r.reject)
  Hint := PUnit
  empty := PUnit.unit
  check := fun (study, alpha, counts, r) _ =>
    let pairs := study.pairs.getD 0
    decide (study = counts.model ∧ pairs = counts.total ∧ 0 < pairs ∧
      tailCheck counts.discordant counts.caseOnly halfFraction alpha.value r)
  sound := by
    rintro ⟨study, alpha, counts, r⟩ _ checked
    obtain ⟨_, pairs, positive, tails⟩ := of_decide_eq_true checked
    refine ⟨⟨pairs, positive⟩, Matched.pairsLaw_univ _, fun δ =>
      Matched.typeI _ δ _ (by exact_mod_cast alpha.nonnegative), ⟨tails.1, tails.2.1⟩, ?_⟩
    change (_ ∧ _) ↔ _
    have fits : counts.discordant ≤ study.pairs.getD 0 := by rw [pairs]; unfold PairCounts.total; omega
    exact (and_iff_right fits).trans (tail_decision _ _ halfFraction _ _ tails)

def rateResult : Checked (Study × SignificanceLevel × EventCounts × ProbabilityFraction × ReportedTails) where
  Statement := fun (_, alpha, events, share, r) =>
    incidenceModule.typeI.Statement alpha ∧
    (OneSampleBinomial.tailNumerator events.total share.num share.den events.exposed = r.upper ∧
      BinomialInterval.lowerNumerator events.total share.num share.den events.exposed = r.lower) ∧
    ((events.total, events.exposed) ∈ Incidence.given (fun n =>
      Incidence.rejectionAt share.point n alpha.value) ↔ OneSided.verdict r.reject)
  Hint := PUnit
  empty := PUnit.unit
  check := fun (study, alpha, events, share, r) _ =>
    decide (study = events.model ∧ 0 < events.exposedTime ∧ 0 < events.unexposedTime ∧
      share.value = events.share ∧ tailCheck events.total events.exposed share alpha.value r)
  sound := by
    rintro ⟨study, alpha, events, share, r⟩ _ checked
    obtain ⟨_, _, _, _, tails⟩ := of_decide_eq_true checked
    exact ⟨incidenceModule.typeI.sound alpha PUnit.unit rfl, ⟨tails.1, tails.2.1⟩,
      tail_decision _ _ share _ _ tails⟩

structure OneSampleResultInput where
  n : ℕ
  reference : ProbabilityFraction
  alpha : ProbabilityFraction
  count : ℕ
  critical : ℕ
  reported : ReportedResult

def oneSampleResult : Checked OneSampleResultInput where
  Statement := fun x =>
    let r := x.reference
    let a := x.alpha
    let o := x.reported
    ((OneSampleBinomial.policy ⟨x.n, x.count⟩).law r.point).real {count | x.count ≤ count} =
      o.pValue.real ∧
    OneSampleBinomial.criticalValue x.n r.num r.den a.num a.den = x.critical ∧
    (if o.reject then x.critical ≤ x.count else ¬ x.critical ≤ x.count) ∧
    ((OneSampleBinomial.analysis ⟨x.n, x.critical⟩ r.point).typeIClaim a.real).statement
  Hint := PUnit
  empty := PUnit.unit
  check := fun x _ =>
    let r := x.reference
    let a := x.alpha
    let v := x.reported.pValue
    decide (x.count ≤ x.n ∧
      OneSampleBinomial.tailNumerator x.n r.num r.den x.count * v.den = v.num * r.den ^ x.n ∧
      OneSampleBinomial.criticalValue x.n r.num r.den a.num a.den = x.critical ∧
      (if x.reported.reject then x.critical ≤ x.count else ¬ x.critical ≤ x.count) ∧
      OneSampleBinomial.tailNumerator x.n r.num r.den x.critical * a.den ≤ a.num * r.den ^ x.n)
  sound := by
    intro x _ checked
    obtain ⟨_, value, critical, decision, bound⟩ := of_decide_eq_true checked
    exact ⟨OneSampleBinomial.pValue_eq_of_cross_product _ _ _ _ x.reference.bounded
      x.reference.positive _ _ x.reported.pValue.positive value, critical, decision,
      OneSampleBinomial.typeI_of_check _ _ _ x.reference.bounded x.reference.positive
        _ _ x.alpha.positive bound⟩

def stageTypeI (design : TwoStageBinomial.Design) (r a : ProbabilityFraction) : Prop :=
  rejectionNumerator design.nFirst design.nSecond r.num r.den r.num r.den design.rejectRule * a.den ≤
    a.num * rejectionDenominator design.nFirst design.nSecond r.den r.den

instance (design : TwoStageBinomial.Design) (r a : ProbabilityFraction) :
    Decidable (stageTypeI design r a) := inferInstanceAs (Decidable (_ ≤ _))

structure StageResultInput where
  sizes : Stages
  rule : StageRule
  reference : ProbabilityFraction
  first : ℕ
  second : Option ℕ
  continued : Bool
  rejected : Bool
  bound : ProbabilityFraction

def StageResultInput.finalFits (x : StageResultInput) : Prop :=
  match x.second with
  | some y => y ≤ x.sizes.second ∧ (x.rule.design x.sizes).rejects x.first y = x.rejected
  | none => x.rejected = false

instance (x : StageResultInput) : Decidable x.finalFits := by
  unfold StageResultInput.finalFits
  split <;> infer_instance

def stageResult : Checked StageResultInput where
  Statement := fun x =>
    let design := x.rule.design x.sizes
    design.continues x.first = x.continued ∧
    match x.second with
    | some y => design.rejects x.first y = x.rejected ∧
        ((TwoStageBinomial.analysisAtMost design x.reference.point).typeIClaim x.bound.real).statement
    | none =>
        ((TwoStageBinomial.analysisAtMost design x.reference.point).typeIClaim x.bound.real).statement
  Hint := PUnit
  empty := PUnit.unit
  check := fun x _ =>
    let design := x.rule.design x.sizes
    decide (x.first ≤ x.sizes.first ∧ x.continued = x.second.isSome ∧
      design.continues x.first = x.continued ∧ x.finalFits ∧ stageTypeI design x.reference x.bound)
  sound := by
    intro x _ checked
    obtain ⟨_, _, continued, decision, bound⟩ := of_decide_eq_true checked
    have level := TwoStageBinomial.typeI_atMost_of_check _ (x.rule.monotone x.sizes)
      _ _ x.reference.bounded x.reference.positive _ _ x.bound.positive bound
    refine ⟨continued, ?_⟩
    unfold StageResultInput.finalFits at decision
    cases found : x.second
    · exact level
    · rw [found] at decision
      exact ⟨decision.2, level⟩

def Test.checkedResult : Test → ResultData → Checked Unit
  | .fisher _ design _ alpha, .fisher observed reported low high bound =>
    fisherResult.atInput ⟨design.model.sizes, alpha, observed, reported, low, high, bound⟩
  | .exact _ (.margin value thresholds) design _ alpha, .margin observed rejected bound gridded =>
    let spec := marginResult.atInput (⟨design.model.sizes, alpha, gridded, thresholds⟩, observed, rejected, bound)
    { spec with check := fun x h => decide (gridded = value) && spec.check x h,
                sound := fun x h checked => spec.sound x h (Bool.and_eq_true_iff.mp checked).2 }
  | .exactStudy _ .fisherGroups design _ alpha, .association observed reported =>
    groupsResult.atInput (design.model, alpha, observed, reported)
  | .exactStudy _ .fisherMixture design _ alpha, .association observed reported =>
    mixtureResult.atInput (design.model, alpha, observed, reported)
  | .exactStudy _ .matched design _ alpha, .matched observed reported =>
    matchedResult.atInput (design.model, alpha, observed, reported)
  | .exactStudy _ .incidence design _ alpha, .rate observed share reported =>
    rateResult.atInput (design.model, alpha, observed, share, reported)
  | .oneSample _ n reference alpha, .oneSample count critical reported =>
    oneSampleResult.atInput ⟨n, reference, alpha, count, critical, reported⟩
  | .twoStage _ sizes rule reference, .twoStage first second continued rejected bound =>
    stageResult.atInput ⟨sizes, rule, reference, first, second, continued, rejected, bound⟩
  | _, _ => Checked.unsupported

end

end StatClaim.Semantics
