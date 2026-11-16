module

public import StatProof.Modules.FisherPower
public import StatProof.BinomialMonotone

/-!
An exact test for a difference of two proportions with a margin, such as a
non-inferiority test. The null is `p_treatment - p_control ≤ margin`. The test
rejects when the treatment successes reach a threshold that depends on the
control successes. The thresholds are part of the declared test; they must not
decrease as control successes increase.

The rejection region is a lower set in control successes and an upper set in
treatment successes, so its probability over a rectangle of rates is largest at
one corner. The range of control rates is cut into cells; one kernel evaluation
per cell bounds the error over that cell, and the cells cover the whole null.
-/

@[expose] public section

set_option autoImplicit false

namespace StatProof.Modules.DifferenceTest

open MeasureTheory TwoArmBinomial

/-- Reject when the treatment successes reach the threshold listed for the
observed control successes. A missing entry never rejects. -/
def rejects (nTreatment : ℕ) (thresholds : List ℕ) (control treatment : ℕ) : Bool :=
  decide (thresholds.getD control (nTreatment + 1) ≤ treatment)

def region (nTreatment : ℕ) (thresholds : List ℕ) : Set (ℕ × ℕ) :=
  {counts | rejects nTreatment thresholds counts.1 counts.2 = true}

/-- More control successes never lower the number of treatment successes needed. -/
def Increasing (nControl nTreatment : ℕ) (thresholds : List ℕ) : Prop :=
  ∀ x, x < nControl →
    thresholds.getD x (nTreatment + 1) ≤ thresholds.getD (x + 1) (nTreatment + 1)

instance (nControl nTreatment : ℕ) (thresholds : List ℕ) :
    Decidable (Increasing nControl nTreatment thresholds) := by
  unfold Increasing
  infer_instance

theorem region_lower (nControl nTreatment : ℕ) (thresholds : List ℕ)
    (increasing : Increasing nControl nTreatment thresholds) (x y : ℕ) (bound : x < nControl)
    (member : (x + 1, y) ∈ region nTreatment thresholds) :
    (x, y) ∈ region nTreatment thresholds := by
  simp only [region, rejects, Set.mem_ofPred_eq, decide_eq_true_eq] at member ⊢
  exact (increasing x bound).trans member

theorem region_upper (nTreatment : ℕ) (thresholds : List ℕ) (x y : ℕ)
    (member : (x, y) ∈ region nTreatment thresholds) :
    (x, y + 1) ∈ region nTreatment thresholds := by
  simp only [region, rejects, Set.mem_ofPred_eq, decide_eq_true_eq] at member ⊢
  exact member.trans (Nat.le_succ y)

/-- Null: the treatment rate exceeds the control rate by at most the margin. -/
noncomputable def analysis (sizes : FixedSampleDesign) (thresholds : List ℕ)
    (margin : ℚ) : Core.PolicyAnalysis (Core.Policy.fixed (model sizes)) where
  hypothesis := proportionDifferenceAtMost margin
  rejection := region sizes.nTreatment thresholds
  rejection_measurable := .of_discrete

/-- Exact rejection probability at rational rates. -/
theorem rejection_probability (nControl nTreatment : ℕ) (thresholds : List ℕ)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e) :
    (productBinomial nControl nTreatment (ratPoint a d le₁ positive₁)
        (ratPoint b e le₂ positive₂)).real
        (region nTreatment thresholds) =
      (rejectionNumerator nControl nTreatment a d b e (rejects nTreatment thresholds) : ℝ) /
        (rejectionDenominator nControl nTreatment d e : ℝ) := by
  rw [rejectionDenominator_cast]
  exact productBinomial_real_ratPoint _ _ a d b e le₁ positive₁ le₂ positive₂ _ _
    (fun _ _ _ _ => Iff.rfl)

/-! ### A cheaper evaluation

The treatment weights are computed once as a list. For each control count the
rejected treatment counts form a tail of that list. -/

theorem list_sum_range (f : ℕ → ℕ) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem tail_sum_range (f : ℕ → ℕ) (start : ℕ) :
    ∀ n, (((List.range n).map f).drop start).sum =
      ∑ i ∈ Finset.range n, if start ≤ i then f i else 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, Finset.sum_range_succ, ← ih]
    by_cases reached : start ≤ n
    · rw [List.drop_append_of_le_length (by simpa using reached)]
      simp [reached]
    · have beyond : n < start := Nat.lt_of_not_le reached
      rw [List.drop_of_length_le (by simp; omega), List.drop_of_length_le (by simp; omega)]
      simp [reached]

/-- The same numerator as `rejectionNumerator` for this rule, sharing the
treatment weights across control counts. -/
def thresholdNumerator (nControl nTreatment a d b e : ℕ) (thresholds : List ℕ) : ℕ :=
  ((List.range (nControl + 1)).map (fun x => binomialWeight nControl a d x *
    (((List.range (nTreatment + 1)).map (binomialWeight nTreatment b e)).drop
      (thresholds.getD x (nTreatment + 1))).sum)).sum

theorem thresholdNumerator_eq (nControl nTreatment a d b e : ℕ) (thresholds : List ℕ) :
    thresholdNumerator nControl nTreatment a d b e thresholds =
      rejectionNumerator nControl nTreatment a d b e (rejects nTreatment thresholds) := by
  unfold thresholdNumerator rejectionNumerator
  rw [list_sum_range]
  apply Finset.sum_congr rfl
  intro x _
  rw [tail_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp [rejects]

/-- One cell: control rates from `low/grid` to `high/grid`. The bound is
evaluated at the smallest control rate and the largest treatment rate the null
allows in the cell. -/
def cellCheck (nControl nTreatment : ℕ) (thresholds : List ℕ) (grid shiftPos shiftNeg
    boundNum boundDen low high : ℕ) : Bool :=
  decide (low ≤ high) && decide (high ≤ grid) &&
    decide (thresholdNumerator nControl nTreatment low grid
        (min grid (high + shiftPos - shiftNeg)) grid thresholds * boundDen ≤
      boundNum * rejectionDenominator nControl nTreatment grid grid)

/-- Consecutive cells, each passing the check. -/
def cellsOk (check : ℕ → ℕ → Bool) : ℕ → List ℕ → Bool
  | _, [] => true
  | low, high :: rest => check low high && cellsOk check high rest

def lastOf : ℕ → List ℕ → ℕ
  | low, [] => low
  | _, high :: rest => lastOf high rest

theorem lastOf_append : ∀ (first : List ℕ) (low : ℕ) (second : List ℕ),
    lastOf low (first ++ second) = lastOf (lastOf low first) second := by
  intro first
  induction first with
  | nil => intro low second; rfl
  | cons high rest ih => intro low second; exact ih high second

/-- Cells can be checked in pieces: a long list is the join of shorter ones. -/
theorem cellsOk_append (check : ℕ → ℕ → Bool) : ∀ (first : List ℕ) (low middle : ℕ)
    (second : List ℕ), lastOf low first = middle → cellsOk check low first = true →
    cellsOk check middle second = true → cellsOk check low (first ++ second) = true := by
  intro first
  induction first with
  | nil =>
    intro low middle second reached _ ok
    rw [← reached] at ok
    exact ok
  | cons high rest ih =>
    intro low middle second reached ok_first ok_second
    simp only [cellsOk, Bool.and_eq_true] at ok_first
    simp only [List.cons_append, cellsOk, Bool.and_eq_true]
    exact ⟨ok_first.1, ih high middle second reached ok_first.2 ok_second⟩

/-- Any point between the first and last boundary lies in a checked cell. -/
theorem cell_exists (check : ℕ → ℕ → Bool) (point : ℝ) :
    ∀ (rest : List ℕ) (low : ℕ), rest ≠ [] → cellsOk check low rest = true →
      (low : ℝ) ≤ point → point ≤ (lastOf low rest : ℝ) →
      ∃ a b : ℕ, check a b = true ∧ (a : ℝ) ≤ point ∧ point ≤ (b : ℝ) := by
  intro rest
  induction rest with
  | nil => intro low nonempty; exact absurd rfl nonempty
  | cons high rest ih =>
    intro low _ ok above below
    simp only [cellsOk, Bool.and_eq_true] at ok
    by_cases inside : point ≤ (high : ℝ)
    · exact ⟨low, high, ok.1, above, inside⟩
    · have nonempty : rest ≠ [] := by
        intro empty
        rw [empty] at below
        exact inside below
      exact ih high nonempty ok.2 (le_of_lt (not_le.mp inside)) below

/-- Type I error over the whole null, from one checked list of cells. The margin
is `(shiftPos - shiftNeg) / grid`, with one of the two shifts zero. -/
theorem typeI_of_cells (sizes : FixedSampleDesign) (thresholds : List ℕ)
    (increasing : Increasing sizes.nControl sizes.nTreatment thresholds)
    (grid : ℕ) (grid_pos : 0 < grid) (shiftPos shiftNeg : ℕ)
    (one_sided : shiftPos = 0 ∨ shiftNeg = 0) (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (cells : List ℕ) (nonempty : cells ≠ [])
    (ok : cellsOk (cellCheck sizes.nControl sizes.nTreatment thresholds grid
      shiftPos shiftNeg boundNum boundDen) shiftNeg cells = true)
    (complete : lastOf shiftNeg cells = grid) :
    ((analysis sizes thresholds (((shiftPos : ℚ) - shiftNeg) / grid)).typeIClaim
      ((boundNum : ℝ) / boundDen)).statement := by
  intro parameter null
  rw [Core.Policy.fixed_law]
  change (productBinomial sizes.nControl sizes.nTreatment parameter.1 parameter.2).real
    (region sizes.nTreatment thresholds) ≤ _
  have gridR : (0 : ℝ) < grid := by exact_mod_cast grid_pos
  have margin : (parameter.2 : ℝ) - (parameter.1 : ℝ) ≤ ((shiftPos : ℝ) - shiftNeg) / grid := by
    have stated : (parameter.2 : ℝ) - (parameter.1 : ℝ) ≤
        ((((shiftPos : ℚ) - shiftNeg) / grid : ℚ) : ℝ) := null
    simpa using stated
  have control0 := parameter.1.property.1
  have control1 := parameter.1.property.2
  have treatment0 := parameter.2.property.1
  have treatment1 := parameter.2.property.2
  -- Scale the control rate to the grid and locate its cell.
  have scaled : (parameter.2 : ℝ) * grid - (parameter.1 : ℝ) * grid ≤
      (shiftPos : ℝ) - shiftNeg := by
    have := mul_le_mul_of_nonneg_right margin gridR.le
    rwa [sub_mul, div_mul_cancel₀ _ gridR.ne'] at this
  have above : (shiftNeg : ℝ) ≤ (parameter.1 : ℝ) * grid := by
    rcases one_sided with zero | zero
    · rw [zero, Nat.cast_zero] at scaled
      nlinarith [mul_nonneg treatment0 gridR.le]
    · rw [zero, Nat.cast_zero]
      exact mul_nonneg control0 gridR.le
  have below : (parameter.1 : ℝ) * grid ≤ (lastOf shiftNeg cells : ℝ) := by
    rw [complete]
    nlinarith
  obtain ⟨a, b, checked, left, right⟩ :=
    cell_exists _ ((parameter.1 : ℝ) * grid) cells shiftNeg nonempty ok above below
  simp only [cellCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  obtain ⟨⟨a_le_b, b_le_grid⟩, bound⟩ := checked
  rw [thresholdNumerator_eq] at bound
  have a_le_grid : a ≤ grid := a_le_b.trans b_le_grid
  have top_le : min grid (b + shiftPos - shiftNeg) ≤ grid := min_le_left _ _
  -- The cell's corner dominates the true rates.
  have corner_control : ratPoint a grid a_le_grid grid_pos ≤ parameter.1 := by
    apply Subtype.coe_le_coe.mp
    change (a : ℝ) / grid ≤ (parameter.1 : ℝ)
    rw [div_le_iff₀ gridR]
    exact left
  have corner_treatment :
      parameter.2 ≤ ratPoint (min grid (b + shiftPos - shiftNeg)) grid top_le grid_pos := by
    apply Subtype.coe_le_coe.mp
    change (parameter.2 : ℝ) ≤ ((min grid (b + shiftPos - shiftNeg) : ℕ) : ℝ) / grid
    rw [le_div_iff₀ gridR]
    by_cases capped : grid ≤ b + shiftPos - shiftNeg
    · rw [min_eq_left capped]
      nlinarith
    · rw [min_eq_right (le_of_lt (not_le.mp capped))]
      have reaches : (shiftNeg : ℝ) ≤ (b : ℝ) := above.trans right
      have enough : shiftNeg ≤ b + shiftPos :=
        (by exact_mod_cast reaches : shiftNeg ≤ b).trans (Nat.le_add_right _ _)
      rw [Nat.cast_sub enough, Nat.cast_add]
      linarith
  refine le_trans (productBinomial_real_le_corner sizes.nControl sizes.nTreatment _
    (fun x y bound member => region_lower _ _ _ increasing x y bound member)
    (fun x y _ member => region_upper _ _ x y member)
    _ parameter.1 parameter.2 _ corner_control corner_treatment) ?_
  rw [rejection_probability]
  exact ratio_le_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ grid_pos grid_pos)
    boundDen_pos bound

/-- Power at one declared pair of rates, from one natural-number check. -/
theorem power_of_check (sizes : FixedSampleDesign) (thresholds : List ℕ) (margin : ℚ)
    (a d b e : ℕ) (le₁ : a ≤ d) (positive₁ : 0 < d) (le₂ : b ≤ e) (positive₂ : 0 < e)
    (boundNum boundDen : ℕ) (boundDen_pos : 0 < boundDen)
    (check : boundNum * rejectionDenominator sizes.nControl sizes.nTreatment d e ≤
      rejectionNumerator sizes.nControl sizes.nTreatment a d b e
        (rejects sizes.nTreatment thresholds) * boundDen) :
    ((analysis sizes thresholds margin).powerClaim
      (fun parameter => parameter = FisherPower.ratePoint a d b e le₁ positive₁ le₂ positive₂)
      ((boundNum : ℝ) / boundDen)).statement := by
  intro parameter alternative
  rw [show parameter = FisherPower.ratePoint a d b e le₁ positive₁ le₂ positive₂ from
    alternative, Core.Policy.fixed_law]
  change _ ≤ (productBinomial sizes.nControl sizes.nTreatment (ratPoint a d le₁ positive₁)
    (ratPoint b e le₂ positive₂)).real
    (region sizes.nTreatment thresholds)
  rw [rejection_probability]
  exact le_ratio_of_check _ _ _ _ (rejectionDenominator_pos _ _ _ _ positive₁ positive₂)
    boundDen_pos check

end StatProof.Modules.DifferenceTest
