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

The p-value here counts every split. A p-value from a random sample of splits
is a different procedure and is not covered.
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

end Generic

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

end StatClaim.Modules.Randomisation
