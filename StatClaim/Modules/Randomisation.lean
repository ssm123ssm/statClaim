module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Basic.Real.Basic

/-!
Randomisation tests.

Under complete randomisation every split of the units into arms of the declared
sizes is equally likely. If treatment changes no unit's outcome (the sharp
null), the recorded outcomes are the same whatever the split, so the test
statistic is a fixed function of the split. Its randomisation p-value is the
share of splits whose statistic is at least the observed one, and the
probability that this share is at most `alpha` is at most `alpha`.

The bound is proved once, for any finite set of equally likely outcomes and any
statistic with ordered values (`uniform_tail_le`). The design statement
(`typeI`) applies it to the splits of `n` units with `k` treated. Units may
affect one another: the sharp null says no assignment changes any unit's
record. Nothing requires the units to be people: with clusters as units, each
unit's record is whatever was measured on the cluster's members.

The exact p-value counts every split. A Monte Carlo p-value compares the observed
assignment with `B` independent uniform draws, counting the observed one among
them; its bound is proved separately (`drawnRejection_le`), with the independence
of the draws stated as a product of uniform laws (`pi_uniform`).
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Randomisation

open MeasureTheory

section Generic

variable {Ω : Type*} {β : Type*} [LinearOrder β]

/-- Elements of `support` whose statistic is at least that of `observed`. Ties count. -/
def tail (support : Finset Ω) (statistic : Ω → β) (observed : Ω) : Finset Ω :=
  support.filter (fun outcome => statistic observed ≤ statistic outcome)

/-- The share of `support` whose statistic is at least that of `observed`. -/
noncomputable def tailShare (support : Finset Ω) (statistic : Ω → β) (observed : Ω) : ℝ :=
  ((tail support statistic observed).card : ℝ) / support.card

/-- The counting argument: at most `c` outcomes have at most `c` outcomes at or
above them. Take the rejected outcome with the smallest statistic; every rejected
outcome lies at or above it. -/
theorem card_rejected_le (support : Finset Ω) (statistic : Ω → β) (c : ℝ) (c_nonneg : 0 ≤ c) :
    ((support.filter (fun outcome =>
      ((tail support statistic outcome).card : ℝ) ≤ c)).card : ℝ) ≤ c := by
  classical
  set rejected := support.filter
    (fun outcome => ((tail support statistic outcome).card : ℝ) ≤ c) with rejected_def
  by_cases inhabited : rejected.Nonempty
  · obtain ⟨lowest, lowest_mem, minimal⟩ := rejected.exists_min_image statistic inhabited
    have subset : rejected ⊆ tail support statistic lowest := by
      intro outcome outcome_mem
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp outcome_mem).1, minimal outcome outcome_mem⟩
    calc ((rejected.card : ℕ) : ℝ)
        ≤ ((tail support statistic lowest).card : ℝ) := by
          exact_mod_cast Finset.card_le_card subset
      _ ≤ c := (Finset.mem_filter.mp lowest_mem).2
  · rw [Finset.not_nonempty_iff_eq_empty.mp inhabited]
    simpa using c_nonneg

/-- Under the uniform law on a finite set, the share of outcomes at or above the
observed one is at most `alpha` with probability at most `alpha`, for every
statistic and every `alpha ≥ 0`. -/
theorem uniform_tail_le [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (support : Finset Ω) (statistic : Ω → β) (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) :
    (Measure.uniformOfFinset support).real
      {outcome | tailShare support statistic outcome ≤ alpha} ≤ alpha := by
  classical
  rcases support.eq_empty_or_nonempty with empty | nonempty
  · subst empty
    simp [Measure.real, Measure.uniformOfFinset_apply, alpha_nonneg]
  have positive : (0 : ℝ) < support.card := by exact_mod_cast nonempty.card_pos
  have same : support.filter (fun outcome => outcome ∈
      {outcome | tailShare support statistic outcome ≤ alpha}) =
      support.filter (fun outcome =>
        ((tail support statistic outcome).card : ℝ) ≤ alpha * support.card) := by
    apply Finset.filter_congr
    intro outcome _
    simp only [Set.mem_ofPred_eq, tailShare]
    exact div_le_iff₀ positive
  have counted := card_rejected_le support statistic (alpha * support.card)
    (mul_nonneg alpha_nonneg positive.le)
  rw [Measure.real, Measure.uniformOfFinset_apply, same, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_le_iff₀ positive]
  exact counted

/-- The uniform law on a nonempty finite set is a probability law. -/
theorem uniform_univ [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (support : Finset Ω) (nonempty : support.Nonempty) :
    (Measure.uniformOfFinset support) Set.univ = 1 := by
  classical
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast nonempty.card_pos.ne') (ENNReal.natCast_ne_top _)

/-- The general Type I bound: assignments drawn uniformly from any finite set, a
statistic computed from the assignment and the record it produced, and a record
that no assignment changes (the sharp null). Complete, stratified and blocked
designs differ only in the set. -/
def uniformRejection {Record : Type*} (support : Finset Ω) (statistic : Ω → Record → β)
    (outcomes : Ω → Record) (alpha : ℝ) : Set Ω :=
  {assignment | tailShare support (fun other => statistic other (outcomes assignment))
    assignment ≤ alpha}

theorem uniformRejection_le [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {Record : Type*}
    (support : Finset Ω) (statistic : Ω → Record → β) (outcomes : Ω → Record)
    (sharp : ∀ first second, outcomes first = outcomes second)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) :
    (Measure.uniformOfFinset support).real (uniformRejection support statistic outcomes alpha)
      ≤ alpha := by
  classical
  rcases support.eq_empty_or_nonempty with empty | ⟨fixed, _⟩
  · subst empty
    simp [Measure.real, Measure.uniformOfFinset_apply, alpha_nonneg]
  have same : uniformRejection support statistic outcomes alpha =
      {assignment | tailShare support (fun other => statistic other (outcomes fixed))
        assignment ≤ alpha} := by
    ext assignment
    simp only [uniformRejection, Set.mem_ofPred_eq, sharp assignment fixed]
  rw [same]
  exact uniform_tail_le support (fun other => statistic other (outcomes fixed)) alpha alpha_nonneg

end Generic

section MonteCarlo

variable {Ω : Type*} {β : Type*} [LinearOrder β]

/-- The Monte Carlo p-value of `B` drawn assignments: index 0 is the observed
assignment and indices 1 to `B` the draws. It is the share of all `B + 1`, the
observed one included, whose statistic is at least the observed one's. -/
noncomputable def drawnShare {B : ℕ} (statistic : Ω → β) (draws : Fin (B + 1) → Ω) : ℝ :=
  ((Finset.univ.filter (fun i => statistic (draws 0) ≤ statistic (draws i))).card : ℝ) /
    (B + 1)

/-- The observed assignment and the draws, each from `support`. -/
def drawSpace (support : Finset Ω) (B : ℕ) : Finset (Fin (B + 1) → Ω) :=
  Fintype.piFinset fun _ => support

/-- Draws at whose index `j` the statistic has at most `c` of the `B + 1` at or above it. -/
noncomputable def rejectedAt [DecidableEq Ω] (support : Finset Ω) (B : ℕ) (statistic : Ω → β) (c : ℝ)
    (j : Fin (B + 1)) : Finset (Fin (B + 1) → Ω) :=
  (drawSpace support B).filter (fun draws =>
    ((Finset.univ.filter (fun i => statistic (draws j) ≤ statistic (draws i))).card : ℝ) ≤ c)

/-- Relabelling the draws does not change how many are at or above a given value. -/
theorem card_filter_perm {B : ℕ} (σ : Equiv.Perm (Fin (B + 1))) (p : Fin (B + 1) → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun i => p (σ i))).card = (Finset.univ.filter p).card := by
  simp only [Finset.card_filter]
  exact Equiv.sum_comp σ (fun i => if p i then 1 else 0)

/-- Swapping the observed assignment with draw `j` is a bijection of the draw space, so
every index is rejected as often as the observed one. -/
theorem rejectedAt_card [DecidableEq Ω] (support : Finset Ω) (B : ℕ) (statistic : Ω → β)
    (c : ℝ) (j : Fin (B + 1)) :
    (rejectedAt support B statistic c j).card = (rejectedAt support B statistic c 0).card := by
  classical
  let σ : Equiv.Perm (Fin (B + 1)) := Equiv.swap 0 j
  refine Finset.card_bij (fun draws _ => draws ∘ σ) ?_ ?_ ?_
  · intro draws member
    obtain ⟨inside, count⟩ := Finset.mem_filter.mp member
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [drawSpace, Fintype.mem_piFinset] at inside ⊢
      exact fun i => inside (σ i)
    · have zero : σ 0 = j := Equiv.swap_apply_left 0 j
      simp only [Function.comp_apply, zero]
      rw [card_filter_perm σ (fun i => statistic (draws j) ≤ statistic (draws i))]
      exact count
  · intro first _ second _ same
    funext i
    have := congrFun same (σ i)
    simpa [σ, Function.comp_apply, Equiv.swap_apply_self] using this
  · intro draws member
    refine ⟨draws ∘ σ, ?_, ?_⟩
    · obtain ⟨inside, count⟩ := Finset.mem_filter.mp member
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [drawSpace, Fintype.mem_piFinset] at inside ⊢
        exact fun i => inside (σ i)
      · have back : σ j = 0 := Equiv.swap_apply_right 0 j
        simp only [Function.comp_apply, back]
        rw [card_filter_perm σ (fun i => statistic (draws 0) ≤ statistic (draws i))]
        exact count
    · funext i
      simp [σ, Function.comp_apply, Equiv.swap_apply_self]

/-- The Monte Carlo counting argument. Summed over the `B + 1` indices, the rejected
draws number at most `c` per point of the draw space, and each index is rejected
equally often, so the observed index is rejected at most a share `alpha`. -/
theorem card_drawn_le (support : Finset Ω) (B : ℕ) (statistic : Ω → β)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) :
    (((drawSpace support B).filter (fun draws => drawnShare statistic draws ≤ alpha)).card : ℝ)
      ≤ alpha * (drawSpace support B).card := by
  classical
  set c : ℝ := alpha * (B + 1) with c_def
  have positive : (0 : ℝ) < B + 1 := by positivity
  have first : (drawSpace support B).filter (fun draws => drawnShare statistic draws ≤ alpha) =
      rejectedAt support B statistic c 0 := by
    apply Finset.filter_congr
    intro draws _
    unfold drawnShare
    rw [div_le_iff₀ positive]
  have each : ∀ draws ∈ drawSpace support B,
      ((Finset.univ.filter (fun j => draws ∈ rejectedAt support B statistic c j)).card : ℝ) ≤ c := by
    intro draws inside
    have same : Finset.univ.filter (fun j => draws ∈ rejectedAt support B statistic c j) =
        Finset.univ.filter (fun j => ((tail Finset.univ (fun i => statistic (draws i)) j).card : ℝ)
          ≤ c) := by
      apply Finset.filter_congr
      intro j _
      simp [rejectedAt, inside, tail]
    rw [same]
    exact card_rejected_le Finset.univ (fun i => statistic (draws i)) c
      (mul_nonneg alpha_nonneg positive.le)
  have total : ∑ j : Fin (B + 1), ((rejectedAt support B statistic c j).card : ℝ) ≤
      c * (drawSpace support B).card := by
    have swapped : ∑ j : Fin (B + 1), ((rejectedAt support B statistic c j).card : ℝ) =
        ∑ draws ∈ drawSpace support B,
          ((Finset.univ.filter (fun j => draws ∈ rejectedAt support B statistic c j)).card : ℝ) := by
      have inner : ∀ j, ((rejectedAt support B statistic c j).card : ℝ) =
          ∑ draws ∈ drawSpace support B,
            (if draws ∈ rejectedAt support B statistic c j then (1 : ℝ) else 0) := by
        intro j
        have inside : rejectedAt support B statistic c j ⊆ drawSpace support B :=
          Finset.filter_subset _ _
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr inside]
        simp
      simp_rw [inner]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro draws _
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [swapped]
    calc ∑ draws ∈ drawSpace support B,
          ((Finset.univ.filter (fun j => draws ∈ rejectedAt support B statistic c j)).card : ℝ)
        ≤ ∑ _draws ∈ drawSpace support B, c := Finset.sum_le_sum each
      _ = c * (drawSpace support B).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [first]
  have scaled : (B + 1 : ℝ) * (rejectedAt support B statistic c 0).card ≤
      (B + 1) * (alpha * (drawSpace support B).card) := by
    calc (B + 1 : ℝ) * (rejectedAt support B statistic c 0).card
        = ∑ j : Fin (B + 1), ((rejectedAt support B statistic c j).card : ℝ) := by
          simp only [rejectedAt_card support B statistic c, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ c * (drawSpace support B).card := total
      _ = (B + 1) * (alpha * (drawSpace support B).card) := by rw [c_def]; ring
  exact le_of_mul_le_mul_left scaled positive


/-- The uniform law on a finite set has finite total mass, so it can be a factor of a
product measure. -/
instance uniform_isFiniteMeasure [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (support : Finset Ω) : IsFiniteMeasure (Measure.uniformOfFinset support) := by
  refine ⟨lt_of_le_of_lt ?_ ENNReal.one_lt_top⟩
  rcases support.eq_empty_or_nonempty with empty | nonempty
  · subst empty
    simp [Measure.uniformOfFinset]
  · exact (uniform_univ support nonempty).le

/-- Independent uniform draws: the observed assignment and `B` draws, each uniform on
`support` and independent of one another, have the uniform law on the draw space. -/
theorem pi_uniform [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (support : Finset Ω) (B : ℕ) :
    Measure.pi (fun _ : Fin (B + 1) => Measure.uniformOfFinset support) =
      Measure.uniformOfFinset (drawSpace support B) := by
  classical
  refine Measure.pi_eq (fun sets _ => ?_)
  have filtered : (drawSpace support B).filter (fun draws => draws ∈ Set.pi Set.univ sets) =
      Fintype.piFinset (fun i => support.filter (fun x => x ∈ sets i)) := by
    ext draws
    simp [drawSpace, Fintype.mem_piFinset, Set.mem_pi, forall_and]
  rw [Measure.uniformOfFinset_apply, filtered, drawSpace, Fintype.card_piFinset,
    Fintype.card_piFinset]
  simp only [Measure.uniformOfFinset_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_prod, Nat.cast_pow, div_eq_mul_inv, Finset.prod_mul_distrib,
    ENNReal.inv_pow]

/-- The record a Monte Carlo test sees comes from the observed assignment, index 0. -/
def drawnRejection {Record : Type*} (B : ℕ) (statistic : Ω → Record → β)
    (outcomes : Ω → Record) (alpha : ℝ) : Set (Fin (B + 1) → Ω) :=
  {draws | drawnShare (fun other => statistic other (outcomes (draws 0))) draws ≤ alpha}

/-- The Type I bound of the Monte Carlo randomisation test: the observed assignment and
`B` independent draws, each uniform on `support`, and a record no assignment changes. -/
theorem drawnRejection_le [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {Record : Type*}
    (support : Finset Ω) (B : ℕ) (statistic : Ω → Record → β) (outcomes : Ω → Record)
    (sharp : ∀ first second, outcomes first = outcomes second)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) :
    (Measure.pi (fun _ : Fin (B + 1) => Measure.uniformOfFinset support)).real
      (drawnRejection B statistic outcomes alpha) ≤ alpha := by
  classical
  rw [pi_uniform]
  rcases support.eq_empty_or_nonempty with empty | ⟨fixed, _⟩
  · subst empty
    simp [Measure.real, Measure.uniformOfFinset_apply, alpha_nonneg, drawSpace]
  have same : drawnRejection B statistic outcomes alpha =
      {draws | drawnShare (fun other => statistic other (outcomes fixed)) draws ≤ alpha} := by
    ext draws
    simp only [drawnRejection, Set.mem_ofPred_eq, sharp (draws 0) fixed]
  have positive : (0 : ℝ) < (drawSpace support B).card := by
    have : (drawSpace support B).Nonempty := by
      rw [drawSpace, Fintype.piFinset_nonempty]
      exact fun _ => ⟨fixed, by assumption⟩
    exact_mod_cast this.card_pos
  rw [same, Measure.real, Measure.uniformOfFinset_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_le_iff₀ positive]
  exact card_drawn_le support B (fun other => statistic other (outcomes fixed)) alpha
    alpha_nonneg

/-- The same at an exact rational level, as a certificate states it. -/
theorem drawnRejection_le_of_level [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {Record : Type*} (support : Finset Ω) (B : ℕ) (statistic : Ω → Record → β)
    (outcomes : Ω → Record) (sharp : ∀ first second, outcomes first = outcomes second)
    (alpha : ℚ) (alpha_nonneg : 0 ≤ alpha) :
    (Measure.pi (fun _ : Fin (B + 1) => Measure.uniformOfFinset support)).real
      (drawnRejection B statistic outcomes alpha) ≤ (alpha : ℝ) :=
  drawnRejection_le support B statistic outcomes sharp alpha (by exact_mod_cast alpha_nonneg)

/-- No Monte Carlo p-value is below `1 / (B + 1)`: the observed assignment counts itself. -/
theorem drawnShare_ge {B : ℕ} (statistic : Ω → β) (draws : Fin (B + 1) → Ω) :
    1 / ((B : ℝ) + 1) ≤ drawnShare statistic draws := by
  have one : (1 : ℝ) ≤ ((Finset.univ.filter
      (fun i => statistic (draws 0) ≤ statistic (draws i))).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, by simp⟩
  unfold drawnShare
  exact div_le_div_of_nonneg_right one (by positivity)

end MonteCarlo

section Design

/-- An assignment of `n` units: the set of treated units. -/
abbrev Assignment (n : ℕ) := Finset (Fin n)

/-- Every assignment with exactly `k` of the `n` units treated. -/
def splits (n k : ℕ) : Finset (Assignment n) := (Finset.univ : Finset (Fin n)).powersetCard k

theorem splits_card (n k : ℕ) : (splits n k).card = n.choose k := by
  simp [splits, Finset.card_powersetCard]

theorem splits_nonempty (n k : ℕ) (le : k ≤ n) : (splits n k).Nonempty :=
  Finset.powersetCard_nonempty.mpr (by simpa using le)

/-- Complete randomisation: every split with `k` treated is equally likely. -/
noncomputable def law (n k : ℕ) : Measure (Assignment n) :=
  Measure.uniformOfFinset (splits n k)

theorem law_univ (n k : ℕ) (le : k ≤ n) : law n k Set.univ = 1 :=
  uniform_univ _ (splits_nonempty n k le)

variable {n : ℕ} {Value : Type*}

/-- Potential outcomes: what would be recorded for every unit under each assignment.
A unit's record may depend on the arms of other units, as within a cluster. -/
abbrev PotentialOutcomes (n : ℕ) (Value : Type*) := Assignment n → Fin n → Value

/-- The sharp null: no assignment changes any unit's record. -/
def SharpNull (outcomes : PotentialOutcomes n Value) : Prop :=
  ∀ first second, outcomes first = outcomes second

/-- Potential outcomes without interference: each unit has one outcome per arm. -/
def unitOutcomes (untreated treated : Fin n → Value) : PotentialOutcomes n Value :=
  fun assignment unit => if unit ∈ assignment then treated unit else untreated unit

/-- If treatment changes no unit's own outcome, the sharp null holds. -/
theorem sharpNull_of_units (untreated treated : Fin n → Value)
    (same : ∀ unit, untreated unit = treated unit) :
    SharpNull (unitOutcomes untreated treated) := by
  have constant : ∀ assignment, unitOutcomes untreated treated assignment = untreated := by
    intro assignment
    funext unit
    by_cases treatedUnit : unit ∈ assignment
    · simp [unitOutcomes, treatedUnit, same unit]
    · simp [unitOutcomes, treatedUnit]
  intro first second
  rw [constant, constant]

/-- The randomisation p-value of a record: the share of splits whose statistic,
computed from the recorded outcomes, is at least the observed statistic. -/
noncomputable def pValue (n k : ℕ) {β : Type*} [LinearOrder β]
    (statistic : Assignment n → (Fin n → Value) → β)
    (assignment : Assignment n) (recorded : Fin n → Value) : ℝ :=
  tailShare (splits n k) (fun other => statistic other recorded) assignment

/-- The assignments for which the test rejects: the p-value of the record
actually produced is at most `alpha`. -/
def rejection (n k : ℕ) {β : Type*} [LinearOrder β]
    (statistic : Assignment n → (Fin n → Value) → β)
    (outcomes : PotentialOutcomes n Value) (alpha : ℝ) : Set (Assignment n) :=
  {assignment | pValue n k statistic assignment (outcomes assignment) ≤ alpha}

/-- No p-value is below one over the number of splits: the observed split is
always at or above itself. With fewer splits than `1 / alpha` the test never rejects. -/
theorem pValue_ge (n k : ℕ) {β : Type*} [LinearOrder β]
    (statistic : Assignment n → (Fin n → Value) → β)
    (assignment : Assignment n) (member : assignment ∈ splits n k) (recorded : Fin n → Value) :
    1 / ((splits n k).card : ℝ) ≤ pValue n k statistic assignment recorded := by
  have inside : assignment ∈ tail (splits n k) (fun other => statistic other recorded) assignment :=
    Finset.mem_filter.mpr ⟨member, le_rfl⟩
  have one : (1 : ℝ) ≤ ((tail (splits n k) (fun other => statistic other recorded)
      assignment).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨assignment, inside⟩
  unfold pValue tailShare
  exact div_le_div_of_nonneg_right one (Nat.cast_nonneg _)

/-- The Type I bound of the randomisation test, for every design size, every
statistic and all potential outcomes satisfying the sharp null. -/
theorem typeI (n k : ℕ) {β : Type*} [LinearOrder β]
    (statistic : Assignment n → (Fin n → Value) → β)
    (outcomes : PotentialOutcomes n Value) (sharp : SharpNull outcomes)
    (alpha : ℝ) (alpha_nonneg : 0 ≤ alpha) :
    (law n k).real (rejection n k statistic outcomes alpha) ≤ alpha := by
  classical
  -- Under the sharp null the record is the same whatever the assignment.
  have fixed : rejection n k statistic outcomes alpha =
      {assignment | tailShare (splits n k) (fun other => statistic other (outcomes ∅))
        assignment ≤ alpha} := by
    ext assignment
    simp only [rejection, pValue, Set.mem_ofPred_eq, sharp assignment ∅]
  rw [fixed]
  exact uniform_tail_le (splits n k) (fun other => statistic other (outcomes ∅)) alpha
    alpha_nonneg

/-- The same bound at an exact rational level, as a certificate states it. -/
theorem typeI_of_level (n k : ℕ) {β : Type*} [LinearOrder β]
    (statistic : Assignment n → (Fin n → Value) → β)
    (outcomes : PotentialOutcomes n Value) (sharp : SharpNull outcomes)
    (alpha : ℚ) (alpha_nonneg : 0 ≤ alpha) :
    (law n k).real (rejection n k statistic outcomes alpha) ≤ (alpha : ℝ) :=
  typeI n k statistic outcomes sharp alpha (by exact_mod_cast alpha_nonneg)

end Design

section Grouped

/-- Strata or blocks: each group's size and its number of treated units. Groups are
randomised independently of one another, and units are numbered within their group. -/
abbrev Groups := List (ℕ × ℕ)

/-- An assignment of grouped units: the treated units of each group. -/
abbrev GroupedAssignment (groups : Groups) := (j : Fin groups.length) → Finset (Fin groups[j.1].1)

/-- Every assignment with each group's declared number of treated units. -/
def groupedSplits (groups : Groups) : Finset (GroupedAssignment groups) :=
  Fintype.piFinset (fun j => (Finset.univ : Finset (Fin groups[j.1].1)).powersetCard groups[j.1].2)

/-- The number of splits of one group, computed through factorials so the kernel
can evaluate it quickly. -/
def splitCount (group : ℕ × ℕ) : ℕ :=
  group.1.factorial / (group.2.factorial * (group.1 - group.2).factorial)

theorem groupedSplits_card (groups : Groups) (fits : ∀ group ∈ groups, group.2 ≤ group.1) :
    (groupedSplits groups).card = (groups.map splitCount).prod := by
  rw [groupedSplits, Fintype.card_piFinset, ← Fin.prod_univ_fun_getElem groups splitCount]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  exact Nat.choose_eq_factorial_div_factorial (fits _ (List.getElem_mem _))

theorem groupedSplits_nonempty (groups : Groups) (fits : ∀ group ∈ groups, group.2 ≤ group.1) :
    (groupedSplits groups).Nonempty := by
  rw [groupedSplits, Fintype.piFinset_nonempty]
  intro j
  exact Finset.powersetCard_nonempty.mpr (by simpa using fits _ (List.getElem_mem _))

/-- Stratified or blocked randomisation: within each group every split with its
declared number of treated units is equally likely, independently between groups. -/
noncomputable def groupedLaw (groups : Groups) : Measure (GroupedAssignment groups) :=
  Measure.uniformOfFinset (groupedSplits groups)

theorem groupedLaw_univ (groups : Groups) (fits : ∀ group ∈ groups, group.2 ≤ group.1) :
    groupedLaw groups Set.univ = 1 :=
  uniform_univ _ (groupedSplits_nonempty groups fits)

/-- The Type I bound for stratified or blocked randomisation, for every statistic and
every record that no assignment changes. -/
theorem groupedTypeI_of_level (groups : Groups) {Record : Type*} {β : Type*} [LinearOrder β]
    (statistic : GroupedAssignment groups → Record → β)
    (outcomes : GroupedAssignment groups → Record)
    (sharp : ∀ first second, outcomes first = outcomes second)
    (alpha : ℚ) (alpha_nonneg : 0 ≤ alpha) :
    (groupedLaw groups).real
        (uniformRejection (groupedSplits groups) statistic outcomes alpha) ≤ (alpha : ℝ) :=
  uniformRejection_le _ statistic outcomes sharp alpha (by exact_mod_cast alpha_nonneg)

end Grouped

end StatClaim.Modules.Randomisation
