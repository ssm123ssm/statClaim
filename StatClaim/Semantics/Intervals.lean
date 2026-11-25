module

public import StatClaim.Semantics.Results
public import StatClaim.Semantics.Contracts

/-! Coverage and checked endpoints of exact confidence intervals. -/

@[expose] public section
set_option autoImplicit false

namespace StatClaim.Semantics

open MeasureTheory StatClaim.Modules

noncomputable section

theorem ProbabilityFraction.real_nonneg (p : ProbabilityFraction) : 0 ≤ p.real :=
  div_nonneg (by positivity) (by positivity)

theorem ProbabilityFraction.real_pos {p : ProbabilityFraction} (positive : 0 < p.num) :
    0 < p.real := div_pos (by exact_mod_cast positive) (by exact_mod_cast p.positive)

theorem ProbabilityFraction.real_lt_one {p : ProbabilityFraction} (small : p.num < p.den) :
    p.real < 1 := (div_lt_one (by exact_mod_cast p.positive)).mpr (by exact_mod_cast small)

def Endpoints.check (i : Endpoints) (n x : ℕ) (a : ProbabilityFraction) : Prop :=
  (i.lower.num = 0 ∨
    OneSampleBinomial.tailNumerator n i.lower.num i.lower.den x * a.den ≤ a.num * i.lower.den ^ n) ∧
  (i.upper.num = i.upper.den ∨
    BinomialInterval.lowerNumerator n i.upper.num i.upper.den x * a.den ≤ a.num * i.upper.den ^ n)

instance (i : Endpoints) (n x : ℕ) (a : ProbabilityFraction) : Decidable (i.check n x a) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Endpoints.contains (i : Endpoints) (n x : ℕ) (a : ProbabilityFraction)
    (checked : i.check n x a) (p : unitInterval)
    (member : p ∈ BinomialInterval.confidenceSet n a.real x) :
    i.lower.point ≤ p ∧ p ≤ i.upper.point :=
  BinomialInterval.interval_contains _ _ _ _ a.positive
    _ _ i.lower.bounded i.lower.positive _ _ i.upper.bounded i.upper.positive
    checked.1 checked.2 p member

theorem Endpoints.contains_real (i : Endpoints) (n x : ℕ) (a : ProbabilityFraction)
    (checked : i.check n x a) (p : unitInterval)
    (member : p ∈ BinomialInterval.confidenceSet n a.real x) :
    i.lower.real ≤ (p : ℝ) ∧ (p : ℝ) ≤ i.upper.real :=
  i.contains n x a checked p member

def binomialInterval (n x : ℕ) (confidence tail : ProbabilityFraction)
    (ends : Endpoints) : Checked Unit where
  Statement := fun _ =>
    (∀ p : unitInterval, 1 - 2 * tail.real ≤ (ProbabilityTheory.binomial n p).real
      {count | p ∈ BinomialInterval.confidenceSet n tail.real count}) ∧
    (∀ p : unitInterval, p ∈ BinomialInterval.confidenceSet n tail.real x →
      ends.lower.point ≤ p ∧ p ≤ ends.upper.point)
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ => decide (0 < n ∧ x ≤ n ∧ confidence.value ≤ 1 - 2 * tail.value ∧
    ends.check n x tail)
  sound := by
    intro _ _ checked
    exact ⟨BinomialInterval.coverage n tail.real tail.real_nonneg,
      ends.contains n x tail (of_decide_eq_true checked).2.2.2⟩

structure JointInterval where
  n : ℕ
  m : ℕ
  observed : ObservedCounts
  level : ProbabilityFraction
  tail : ProbabilityFraction
  control : Endpoints
  treatment : Endpoints

def JointInterval.check (j : JointInterval) : Prop :=
  2 * j.tail.value ≤ 1 ∧ j.level.value ≤ (1 - 2 * j.tail.value) ^ 2 ∧
  countsFit j.n j.m j.observed ∧
  j.control.check j.n j.observed.control j.tail ∧ j.treatment.check j.m j.observed.treatment j.tail

instance (j : JointInterval) : Decidable j.check := inferInstanceAs (Decidable (_ ∧ _))

theorem JointInterval.budget (j : JointInterval) (h : j.check) :
    2 * j.tail.real ≤ 1 ∧ j.level.real ≤ (1 - 2 * j.tail.real) ^ 2 := by
  rw [← j.level.real_cast, ← j.tail.real_cast]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1⟩

def JointInterval.coverage (j : JointInterval) : Prop :=
  ∀ (pc pt : unitInterval), j.level.real ≤ (productBinomial j.n j.m pc pt).real
    ({x | pc ∈ BinomialInterval.confidenceSet j.n j.tail.real x} ×ˢ
     {y | pt ∈ BinomialInterval.confidenceSet j.m j.tail.real y})

theorem JointInterval.covered (j : JointInterval) (h : j.check) : j.coverage :=
  fun pc pt => le_trans (j.budget h).2
    (BinomialInterval.joint_coverage _ _ _ j.tail.real_nonneg (j.budget h).1 pc pt)

def JointInterval.difference (j : JointInterval) : Prop :=
  ∀ (pc pt : unitInterval),
    pc ∈ BinomialInterval.confidenceSet j.n j.tail.real j.observed.control →
    pt ∈ BinomialInterval.confidenceSet j.m j.tail.real j.observed.treatment →
    j.treatment.lower.real - j.control.upper.real ≤ (pt : ℝ) - pc ∧
      (pt : ℝ) - pc ≤ j.treatment.upper.real - j.control.lower.real

theorem JointInterval.difference_sound (j : JointInterval) (h : j.check) : j.difference := by
  intro pc pt hc ht
  have c := j.control.contains_real _ _ _ h.2.2.2.1 pc hc
  have t := j.treatment.contains_real _ _ _ h.2.2.2.2 pt ht
  exact ⟨sub_le_sub t.1 c.2, sub_le_sub t.2 c.1⟩

def differenceInterval (model : Model) (j : JointInterval) : Checked Unit where
  Statement := fun _ => j.coverage ∧ j.difference
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ => decide (model.outcome = .binary ∧ model.clusters.isNone ∧
    model.measurements.isNone ∧ j.check)
  sound := fun _ _ h =>
    let checked : j.check := (of_decide_eq_true h).2.2.2
    ⟨j.covered checked, j.difference_sound checked⟩

def JointInterval.ratio (j : JointInterval) : Prop :=
  ∀ (pc pt : unitInterval),
    pc ∈ BinomialInterval.confidenceSet j.n j.tail.real j.observed.control →
    pt ∈ BinomialInterval.confidenceSet j.m j.tail.real j.observed.treatment →
    0 < (pc : ℝ) →
    let lower := j.treatment.lower.real / j.control.upper.real ≤ (pt : ℝ) / pc
    if j.control.lower.num > 0 then
      lower ∧ (pt : ℝ) / pc ≤ j.treatment.upper.real / j.control.lower.real
    else lower

theorem JointInterval.ratio_sound (j : JointInterval) (h : j.check) : j.ratio := by
  intro pc pt hc ht positive
  have c := j.control.contains_real _ _ _ h.2.2.2.1 pc hc
  have t := j.treatment.contains_real _ _ _ h.2.2.2.2 pt ht
  have bounds := Association.ratio_bounds c t j.treatment.lower.real_nonneg positive
  split
  · next condition => exact ⟨bounds.1, bounds.2 (ProbabilityFraction.real_pos condition)⟩
  · exact bounds.1

def JointInterval.odds (j : JointInterval) : Prop :=
  ∀ (pc pt : unitInterval),
    pc ∈ BinomialInterval.confidenceSet j.n j.tail.real j.observed.control →
    pt ∈ BinomialInterval.confidenceSet j.m j.tail.real j.observed.treatment →
    0 < (pc : ℝ) → (pc : ℝ) < 1 → (pt : ℝ) < 1 →
    let effect := Association.odds pt / Association.odds pc
    let lower := if j.control.upper.num < j.control.upper.den then
      Association.odds j.treatment.lower.real / Association.odds j.control.upper.real ≤ effect
      else 0 ≤ effect
    if 0 < j.control.lower.num ∧ j.treatment.upper.num < j.treatment.upper.den then
      lower ∧ effect ≤ Association.odds j.treatment.upper.real / Association.odds j.control.lower.real
    else lower

theorem JointInterval.odds_sound (j : JointInterval) (h : j.check) : j.odds := by
  intro pc pt hc ht positive below treatedBelow
  have c := j.control.contains_real _ _ _ h.2.2.2.1 pc hc
  have t := j.treatment.contains_real _ _ _ h.2.2.2.2 pt ht
  have bounds := Association.odds_ratio_bounds c t j.treatment.lower.real_nonneg
    positive below treatedBelow
  dsimp only
  split
  · next upper =>
    refine ⟨?_, bounds.2.2 (ProbabilityFraction.real_pos upper.1)
      (ProbabilityFraction.real_lt_one upper.2)⟩
    split
    · next lower => exact bounds.2.1 (ProbabilityFraction.real_lt_one lower)
    · exact bounds.1
  · split
    · next lower => exact bounds.2.1 (ProbabilityFraction.real_lt_one lower)
    · exact bounds.1

def JointInterval.mixtureCoverage (j : JointInterval) (n : ℕ) : Prop :=
  ∀ (q pc pt : unitInterval), j.level.real ≤
    (Association.mixture n q (fun k => productBinomial (n - k) k pc pt)).real
      (Association.given n (fun k =>
        {x | pc ∈ BinomialInterval.confidenceSet (n - k) j.tail.real x} ×ˢ
        {y | pt ∈ BinomialInterval.confidenceSet k j.tail.real y}))

theorem JointInterval.mixtureCovered (j : JointInterval) (h : j.check) (n : ℕ) :
    j.mixtureCoverage n :=
  fun q pc pt => le_trans (j.budget h).2 (Association.mixture_joint_coverage _ _
    j.tail.real_nonneg (j.budget h).1 q pc pt)

def associationInterval (table : AssociationTable) (measure : String) (j : JointInterval) :
    Checked Unit where
  Statement := fun _ =>
    (if table.model.groups.isSome then j.coverage else j.mixtureCoverage table.total) ∧
    (if measure == "odds_ratio" then j.odds
     else if measure == "risk_ratio" || measure == "prevalence_ratio" then j.ratio
     else j.difference)
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ =>
    decide (j.check ∧ table.model.exposureScale = .binary ∧ table.model.outcomeScale = .binary ∧
      table.model.survey = .simple_random ∧
      (table.model.groups = some (j.n, j.m) ∨
        (table.model.groups = none ∧ table.model.n = some table.total))) &&
    (measure == "odds_ratio" || ["risk_ratio", "risk_difference", "prevalence_ratio",
      "prevalence_difference"].contains measure)
  sound := by
    intro _ _ checked
    have h := (of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1).1
    constructor
    · split
      · exact j.covered h
      · exact j.mixtureCovered h table.total
    · split
      · exact j.odds_sound h
      · split
        · exact j.ratio_sound h
        · exact j.difference_sound h

def Endpoints.odds (ends : Endpoints) (n x : ℕ) (tail : ProbabilityFraction)
    (scale : ℝ) : Prop :=
  ∀ p : unitInterval, p ∈ BinomialInterval.confidenceSet n tail.real x → (p : ℝ) < 1 →
    let lower := Association.odds ends.lower.real * scale ≤ Association.odds p * scale
    if ends.upper.num < ends.upper.den then
      lower ∧ Association.odds p * scale ≤ Association.odds ends.upper.real * scale
    else lower

theorem Endpoints.odds_sound (ends : Endpoints) (n x : ℕ) (tail : ProbabilityFraction)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (checked : ends.check n x tail) :
    ends.odds n x tail scale := by
  intro p member below
  have limits := ends.contains_real n x tail checked p member
  have lower := mul_le_mul_of_nonneg_right (Association.odds_mono limits.1 below) nonnegative
  split
  · next high =>
    exact ⟨lower, mul_le_mul_of_nonneg_right
      (Association.odds_mono limits.2 (ProbabilityFraction.real_lt_one high)) nonnegative⟩
  · exact lower

def Endpoints.unscaledOdds (ends : Endpoints) (n x : ℕ) (tail : ProbabilityFraction) : Prop :=
  ∀ p : unitInterval, p ∈ BinomialInterval.confidenceSet n tail.real x → (p : ℝ) < 1 →
    let lower := Association.odds ends.lower.real ≤ Association.odds p
    if ends.upper.num < ends.upper.den then
      lower ∧ Association.odds p ≤ Association.odds ends.upper.real
    else lower

theorem Endpoints.unscaledOdds_sound (ends : Endpoints) (n x : ℕ) (tail : ProbabilityFraction)
    (checked : ends.check n x tail) : ends.unscaledOdds n x tail := by
  intro p member below
  simpa only [mul_one] using
    ends.odds_sound n x tail 1 zero_le_one checked p member below

def matchedInterval (pairs : PairCounts) (level tail : ProbabilityFraction)
    (ends : Endpoints) : Checked Unit where
  Statement := fun _ =>
    (∀ δ π, level.real ≤ (Matched.pairsLaw pairs.total δ π).real
      (Association.given pairs.total (fun n => {x | π ∈ BinomialInterval.confidenceSet n tail.real x}))) ∧
    ends.unscaledOdds pairs.discordant pairs.caseOnly tail
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ => decide (pairs.model.pairs = some pairs.total ∧
    pairs.model.design = .matched_case_control ∧ 0 < pairs.discordant ∧
    level.value ≤ 1 - 2 * tail.value ∧ ends.check pairs.discordant pairs.caseOnly tail)
  sound := by
    intro _ _ checked
    have h := of_decide_eq_true checked
    have bound : level.real ≤ 1 - 2 * tail.real := by
      rw [← level.real_cast, ← tail.real_cast]
      exact_mod_cast h.2.2.2.1
    exact ⟨fun δ π => le_trans bound (Matched.pairs_coverage _ _ tail.real_nonneg δ π),
      ends.unscaledOdds_sound _ _ _ h.2.2.2.2⟩

def EventCounts.scale (e : EventCounts) : ℚ := e.unexposedTime / e.exposedTime
def EventCounts.scaleReal (e : EventCounts) : ℝ := (e.scale.num.toNat : ℝ) / e.scale.den

def rateInterval (events : EventCounts) (level tail : ProbabilityFraction)
    (ends : Endpoints) : Checked Unit where
  Statement := fun _ =>
    (∀ total π, level.real ≤ (Incidence.ratesLaw total π).real
      (Incidence.given (fun n => {x | π ∈ BinomialInterval.confidenceSet n tail.real x}))) ∧
    ends.odds events.total events.exposed tail events.scaleReal
  Hint := PUnit
  empty := PUnit.unit
  check := fun _ _ => decide (events.model.design = .person_time_cohort ∧
    0 < events.exposedTime ∧ 0 < events.unexposedTime ∧ 0 < events.total ∧
    level.value ≤ 1 - 2 * tail.value ∧ ends.check events.total events.exposed tail)
  sound := by
    intro _ _ checked
    have h := of_decide_eq_true checked
    have bound : level.real ≤ 1 - 2 * tail.real := by
      rw [← level.real_cast, ← tail.real_cast]
      exact_mod_cast h.2.2.2.2.1
    exact ⟨fun total π => le_trans bound (Incidence.coverage _ _ tail.real_nonneg π),
      ends.odds_sound _ _ _ _ (by unfold EventCounts.scaleReal; positivity) h.2.2.2.2.2⟩

def IntervalData.checked : IntervalData → Checked Unit
  | .binomial n x level tail ends => binomialInterval n x level tail ends
  | .proportion study _ group cases level tail ends =>
    let n := match study.groups with
      | some sizes => if group = some "exposed" then sizes.2 else sizes.1
      | none => study.total.getD 0
    binomialInterval n cases level tail ends
  | .difference model o level tail c t =>
    differenceInterval model ⟨model.sizes.nControl, model.sizes.nTreatment, o, level, tail, c, t⟩
  | .association table measure level tail c t =>
    let (n, m, o) := table.sides
    associationInterval table measure ⟨n, m, o, level, tail, c, t⟩
  | .matched pairs level tail ends => matchedInterval pairs level tail ends
  | .rate events level tail ends => rateInterval events level tail ends

end

end StatClaim.Semantics
