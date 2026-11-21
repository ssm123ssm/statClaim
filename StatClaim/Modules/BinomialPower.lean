module

public import StatClaim.Modules.Incidence

/-!
Exact power of the two-sided exact binomial test, given its count's number of trials, and
of McNemar's test, averaged over the number of discordant pairs.

Given `n` trials, the test of a share `c/f` rejects a count when twice the smaller of its
tails is at most alpha (`Incidence.rejectionAt`; `Matched.rejection` is the case `1/2`).
The lower tail grows with the count and the upper tail shrinks, so the test rejects the
counts below some `low` and those from some `high` up. Supplied values of `low` and `high`
are untrusted: `RegionValid` checks them with four tail sums, and `region_iff` turns them
into the exact region. At a rational planning point the rejection probability is then a
ratio of natural numbers (`binomial_real_region`, `pairs_real_ratPoint`), and one
comparison bounds the power from below or above.

Power at a planning point is not a guarantee at other points, and says nothing of cause.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.BinomialPower

open MeasureTheory ProbabilityTheory OneSampleBinomial BinomialInterval

theorem lowerNumerator_mono (n a d : ℕ) {x y : ℕ} (h : x ≤ y) :
    lowerNumerator n a d x ≤ lowerNumerator n a d y := by
  unfold lowerNumerator
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ≤ x
  · simp [hk, hk.trans h]
  · simp [hk]

theorem tailNumerator_anti (n a d : ℕ) {x y : ℕ} (h : x ≤ y) :
    tailNumerator n a d y ≤ tailNumerator n a d x := by
  unfold tailNumerator
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : y ≤ k
  · simp [hk, h.trans hk]
  · simp [hk]

/-- Twice the smaller tail is small when either tail is. -/
theorem twice_min_iff (U L ad X : ℕ) :
    2 * min U L * ad ≤ X ↔ 2 * U * ad ≤ X ∨ 2 * L * ad ≤ X := by
  rcases le_total U L with h | h
  · rw [min_eq_left h]
    refine ⟨Or.inl, fun hor => hor.elim id fun hL => ?_⟩
    exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) hL
  · rw [min_eq_right h]
    refine ⟨Or.inr, fun hor => hor.elim (fun hU => ?_) id⟩
    exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) hU

/-- The test of the share `c/f` with `n` trials, at level `an/ad`, rejects the counts below
`low` and those from `high` up, and no other count up to `n`. -/
def RegionValid (n c f an ad low high : ℕ) : Prop :=
  (low = 0 ∨ 2 * lowerNumerator n c f (low - 1) * ad ≤ an * f ^ n) ∧
    (n < low ∨ an * f ^ n < 2 * lowerNumerator n c f low * ad) ∧
    (n < high ∨ 2 * tailNumerator n c f high * ad ≤ an * f ^ n) ∧
    (high = 0 ∨ an * f ^ n < 2 * tailNumerator n c f (high - 1) * ad)

instance (n c f an ad low high : ℕ) : Decidable (RegionValid n c f an ad low high) := by
  unfold RegionValid
  infer_instance

theorem region_iff (n c f an ad low high : ℕ) (valid : RegionValid n c f an ad low high)
    (x : ℕ) (x_le : x ≤ n) :
    2 * min (tailNumerator n c f x) (lowerNumerator n c f x) * ad ≤ an * f ^ n ↔
      x < low ∨ high ≤ x := by
  obtain ⟨lowIn, lowOut, highIn, highOut⟩ := valid
  rw [twice_min_iff]
  have lower : 2 * lowerNumerator n c f x * ad ≤ an * f ^ n ↔ x < low := by
    constructor
    · intro small
      by_contra big
      rcases lowOut with out | out
      · omega
      · have := Nat.mul_le_mul_right ad
          (Nat.mul_le_mul_left 2 (lowerNumerator_mono n c f (Nat.le_of_not_lt big)))
        omega
    · intro below
      rcases lowIn with zero | small
      · omega
      · exact le_trans (Nat.mul_le_mul_right ad
          (Nat.mul_le_mul_left 2 (lowerNumerator_mono n c f (by omega)))) small
  have upper : 2 * tailNumerator n c f x * ad ≤ an * f ^ n ↔ high ≤ x := by
    constructor
    · intro small
      by_contra below
      rcases highOut with zero | out
      · omega
      · have := Nat.mul_le_mul_right ad
          (Nat.mul_le_mul_left 2 (tailNumerator_anti n c f (show x ≤ high - 1 by omega)))
        omega
    · intro above
      rcases highIn with out | small
      · omega
      · exact le_trans (Nat.mul_le_mul_right ad
          (Nat.mul_le_mul_left 2 (tailNumerator_anti n c f above))) small
  rw [lower, upper]
  exact Or.comm

theorem mem_rejectionAt_iff (n c f an ad : ℕ) (hc : c ≤ f) (hf : 0 < f) (had : 0 < ad)
    (alpha : ℝ) (level : alpha = (an : ℝ) / ad) (x : ℕ) :
    x ∈ Incidence.rejectionAt (ratPoint c f hc hf) n alpha ↔
      2 * min (tailNumerator n c f x) (lowerNumerator n c f x) * ad ≤ an * f ^ n := by
  simp only [Incidence.rejectionAt, Set.mem_ofPred_eq]
  rw [upper_tail_ratPoint, lower_tail_ratPoint]
  exact Incidence.twice_min_le_iff _ _ _ an ad alpha (Nat.pow_pos hf) had level

/-- Integer numerator of the probability of the counts below `low` or from `high` up, at the
share `a/d`; the denominator is `d ^ n`. -/
def regionNumerator (n a d low high : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (n + 1), if x < low ∨ high ≤ x then binomialWeight n a d x else 0

/-- With validated bounds, the rejection probability at a rational share is a ratio of
natural numbers. -/
theorem binomial_real_region (n a d c f an ad low high : ℕ) (ha : a ≤ d) (hd : 0 < d)
    (hc : c ≤ f) (hf : 0 < f) (had : 0 < ad) (alpha : ℝ) (level : alpha = (an : ℝ) / ad)
    (valid : RegionValid n c f an ad low high) :
    (binomial n (ratPoint a d ha hd)).real (Incidence.rejectionAt (ratPoint c f hc hf) n alpha) =
      (regionNumerator n a d low high : ℝ) / ((d ^ n : ℕ) : ℝ) := by
  classical
  rw [binomial_real_eq_expectation]
  simp only [binomialExpectation, regionNumerator, Nat.cast_sum, Finset.sum_div, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro x x_mem
  have x_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp x_mem)
  rw [binomialMass_ratPoint n a d x ha hd x_le]
  have key := (mem_rejectionAt_iff n c f an ad hc hf had alpha level x).trans
    (region_iff n c f an ad low high valid x x_le)
  by_cases r : x < low ∨ high ≤ x
  · simp [key.mpr r, r]
  · simp [show x ∉ Incidence.rejectionAt (ratPoint c f hc hf) n alpha from
      fun member => r (key.mp member), r]

/-- Power of the test given `n` trials, at a rational planning point, from one check. -/
theorem power_of_check (n a d c f an ad low high : ℕ) (ha : a ≤ d) (hd : 0 < d)
    (hc : c ≤ f) (hf : 0 < f) (had : 0 < ad) (alpha : ℝ) (level : alpha = (an : ℝ) / ad)
    (valid : RegionValid n c f an ad low high) (boundNum boundDen : ℕ) (hb : 0 < boundDen)
    (check : boundNum * d ^ n ≤ regionNumerator n a d low high * boundDen) :
    (boundNum : ℝ) / boundDen ≤
      (binomial n (ratPoint a d ha hd)).real (Incidence.rejectionAt (ratPoint c f hc hf) n alpha) := by
  rw [binomial_real_region n a d c f an ad low high ha hd hc hf had alpha level valid]
  exact le_ratio_of_check _ _ _ _ (Nat.pow_pos hd) hb check

/-- The power falls short of the bound, from one check. -/
theorem power_lt_of_check (n a d c f an ad low high : ℕ) (ha : a ≤ d) (hd : 0 < d)
    (hc : c ≤ f) (hf : 0 < f) (had : 0 < ad) (alpha : ℝ) (level : alpha = (an : ℝ) / ad)
    (valid : RegionValid n c f an ad low high) (boundNum boundDen : ℕ) (hb : 0 < boundDen)
    (check : regionNumerator n a d low high * boundDen < boundNum * d ^ n) :
    (binomial n (ratPoint a d ha hd)).real (Incidence.rejectionAt (ratPoint c f hc hf) n alpha) <
      (boundNum : ℝ) / boundDen := by
  rw [binomial_real_region n a d c f an ad low high ha hd hc hf had alpha level valid]
  exact ratio_lt_of_check _ _ _ _ (Nat.pow_pos hd) hb check

/-! ### McNemar's test, averaged over the number of discordant pairs -/

variable {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- The probability of an event under a mixture is the average of its probabilities. -/
theorem mixture_real_apply (n : ℕ) (q : unitInterval) (inner : ℕ → Measure α)
    [∀ k, IsProbabilityMeasure (inner k)] (event : ℕ → Set α) :
    (Association.mixture n q inner).real (Association.given n event) =
      ∑ k ∈ Finset.range (n + 1), binomialMass n (q : ℝ) k * (inner k).real (event k) := by
  rw [measureReal_def, Association.mixture_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (binomialMass_nonnegative n (q : ℝ) k q.property.1 q.property.2), measureReal_def]
  · intro k _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- Every number of discordant pairs up to `n` has validated bounds, at level `an/ad`. -/
def PairsValid (n an ad : ℕ) (lows highs : List ℕ) : Prop :=
  ∀ k, k < n + 1 → RegionValid k 1 2 an ad (lows.getD k 0) (highs.getD k 0)

instance (n an ad : ℕ) (lows highs : List ℕ) : Decidable (PairsValid n an ad lows highs) := by
  unfold PairsValid
  infer_instance

/-- The bounds for each number of discordant pairs do not depend on the total, so bounds
checked up to `n` serve every smaller total. -/
theorem PairsValid.mono {n m an ad : ℕ} {lows highs : List ℕ}
    (valid : PairsValid n an ad lows highs) (smaller : m ≤ n) : PairsValid m an ad lows highs :=
  fun k below => valid k (by omega)

/-- Integer numerator of McNemar's rejection probability when a pair is discordant with
probability `a/d` and the case is the exposed one with probability `b/e`; the denominator
is `d ^ n * e ^ n`. -/
def pairsNumerator (n a d b e : ℕ) (lows highs : List ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    binomialWeight n a d k * regionNumerator k b e (lows.getD k 0) (highs.getD k 0) * e ^ (n - k)

theorem pairs_real_ratPoint (n a d b e an ad : ℕ) (ha : a ≤ d) (hd : 0 < d) (hb : b ≤ e)
    (he : 0 < e) (had : 0 < ad) (alpha : ℝ) (level : alpha = (an : ℝ) / ad)
    (lows highs : List ℕ) (valid : PairsValid n an ad lows highs) :
    (Matched.pairsLaw n (ratPoint a d ha hd) (ratPoint b e hb he)).real
        (Matched.pairsRejection n alpha) =
      (pairsNumerator n a d b e lows highs : ℝ) / ((d ^ n * e ^ n : ℕ) : ℝ) := by
  unfold Matched.pairsLaw Matched.pairsRejection
  rw [mixture_real_apply, pairsNumerator, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k k_mem
  have k_le := Nat.lt_succ_iff.mp (Finset.mem_range.mp k_mem)
  rw [show Matched.rejection k alpha =
      Incidence.rejectionAt (ratPoint 1 2 (by decide) (by decide)) k alpha from rfl,
    binomialMass_ratPoint n a d k ha hd k_le,
    binomial_real_region k b e 1 2 an ad _ _ hb he (by decide) (by decide) had alpha level
      (valid k (by omega))]
  have split : (e : ℝ) ^ n = (e : ℝ) ^ k * (e : ℝ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' k_le]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  push_cast
  rw [split]
  field_simp

theorem pairs_power_of_check (n a d b e an ad : ℕ) (ha : a ≤ d) (hd : 0 < d) (hb : b ≤ e)
    (he : 0 < e) (had : 0 < ad) (alpha : ℝ) (level : alpha = (an : ℝ) / ad)
    (lows highs : List ℕ) (valid : PairsValid n an ad lows highs)
    (boundNum boundDen : ℕ) (hbd : 0 < boundDen)
    (check : boundNum * (d ^ n * e ^ n) ≤ pairsNumerator n a d b e lows highs * boundDen) :
    (boundNum : ℝ) / boundDen ≤
      (Matched.pairsLaw n (ratPoint a d ha hd) (ratPoint b e hb he)).real
        (Matched.pairsRejection n alpha) := by
  rw [pairs_real_ratPoint n a d b e an ad ha hd hb he had alpha level lows highs valid]
  exact le_ratio_of_check _ _ _ _ (Nat.mul_pos (Nat.pow_pos hd) (Nat.pow_pos he)) hbd check

theorem pairs_power_lt_of_check (n a d b e an ad : ℕ) (ha : a ≤ d) (hd : 0 < d) (hb : b ≤ e)
    (he : 0 < e) (had : 0 < ad) (alpha : ℝ) (level : alpha = (an : ℝ) / ad)
    (lows highs : List ℕ) (valid : PairsValid n an ad lows highs)
    (boundNum boundDen : ℕ) (hbd : 0 < boundDen)
    (check : pairsNumerator n a d b e lows highs * boundDen < boundNum * (d ^ n * e ^ n)) :
    (Matched.pairsLaw n (ratPoint a d ha hd) (ratPoint b e hb he)).real
        (Matched.pairsRejection n alpha) < (boundNum : ℝ) / boundDen := by
  rw [pairs_real_ratPoint n a d b e an ad ha hd hb he had alpha level lows highs valid]
  exact ratio_lt_of_check _ _ _ _ (Nat.mul_pos (Nat.pow_pos hd) (Nat.pow_pos he)) hbd check

end StatClaim.Modules.BinomialPower
