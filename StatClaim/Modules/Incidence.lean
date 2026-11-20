module

public import StatClaim.Modules.Matched
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
Incidence rates in a cohort followed over person-time.

Events in each group occur at a constant rate over its person-time. The total number of
events is Poisson, and given it the exposed group's share is binomial, with probability
proportional to the exposed person-time times its rate (`ratesLaw`). Equal rates make that
probability the exposed share of person-time.

Given the total, the two-sided exact test of that share has level alpha (`levelAt`); a bound
that holds for every total holds on average over any law of the total (`compound_le`,
`le_compound`), so the test keeps its level (`typeI`) and the exact interval for the share
keeps its coverage (`coverage`). The rate ratio is the odds of the share times the ratio of
unexposed to exposed person-time (`rate_ratio_contains`). Nothing here concerns cause.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Incidence

open MeasureTheory ProbabilityTheory NNReal

/-- A total count from any law on ℕ; given the total `n`, the data follow `inner n`. -/
noncomputable def compound (count : Measure ℕ) (inner : ℕ → Measure ℕ) : Measure (ℕ × ℕ) :=
  count.bind (fun n => (Measure.dirac n).prod (inner n))

/-- An event that depends on the total. -/
def given (event : ℕ → Set ℕ) : Set (ℕ × ℕ) := {t | t.2 ∈ event t.1}

theorem compound_apply (count : Measure ℕ) (inner : ℕ → Measure ℕ) [∀ n, SFinite (inner n)]
    (event : ℕ → Set ℕ) :
    compound count inner (given event) = ∫⁻ n, inner n (event n) ∂count := by
  rw [compound, Measure.bind_apply (Set.to_countable _).measurableSet
    (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro n
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
    (Set.to_countable _).measurableSet]
  congr 1

theorem compound_univ (count : Measure ℕ) [IsProbabilityMeasure count] (inner : ℕ → Measure ℕ)
    [∀ n, IsProbabilityMeasure (inner n)] : compound count inner Set.univ = 1 := by
  rw [compound, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
  simp

instance compound_isProbabilityMeasure (count : Measure ℕ) [IsProbabilityMeasure count]
    (inner : ℕ → Measure ℕ) [∀ n, IsProbabilityMeasure (inner n)] :
    IsProbabilityMeasure (compound count inner) :=
  ⟨compound_univ count inner⟩

theorem compound_le (count : Measure ℕ) [IsProbabilityMeasure count] (inner : ℕ → Measure ℕ)
    [∀ n, IsProbabilityMeasure (inner n)] (event : ℕ → Set ℕ) (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ n, (inner n).real (event n) ≤ c) :
    (compound count inner).real (given event) ≤ c := by
  have total : compound count inner (given event) ≤ ENNReal.ofReal c := by
    rw [compound_apply]
    calc ∫⁻ n, inner n (event n) ∂count ≤ ∫⁻ _, ENNReal.ofReal c ∂count := by
          apply lintegral_mono
          intro n
          show inner n (event n) ≤ ENNReal.ofReal c
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (bound n)
      _ = ENNReal.ofReal c := by simp
  exact ENNReal.toReal_le_of_le_ofReal hc total

theorem le_compound (count : Measure ℕ) [IsProbabilityMeasure count] (inner : ℕ → Measure ℕ)
    [∀ n, IsProbabilityMeasure (inner n)] (event : ℕ → Set ℕ) (c : ℝ)
    (bound : ∀ n, c ≤ (inner n).real (event n)) :
    c ≤ (compound count inner).real (given event) := by
  rcases le_or_gt c 0 with nonpositive | positive
  · exact nonpositive.trans measureReal_nonneg
  have total : ENNReal.ofReal c ≤ compound count inner (given event) := by
    rw [compound_apply]
    calc ENNReal.ofReal c = ∫⁻ _, ENNReal.ofReal c ∂count := by simp
      _ ≤ ∫⁻ n, inner n (event n) ∂count := by
          apply lintegral_mono
          intro n
          show ENNReal.ofReal c ≤ inner n (event n)
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (bound n)
  rw [measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp total

/-- Events in two groups with constant rates: the total is Poisson, and given it the
exposed group's share is binomial. -/
noncomputable def ratesLaw (total : ℝ≥0) (π : unitInterval) : Measure (ℕ × ℕ) :=
  compound (poissonMeasure total) (fun n => binomial n π)

/-- Given `n` events, the two-sided exact test of the share `p` rejects when twice the
smaller tail is at most alpha. -/
def rejectionAt (p : unitInterval) (n : ℕ) (alpha : ℝ) : Set ℕ :=
  {x | 2 * min ((binomial n p).real (Set.Ici x)) ((binomial n p).real (Set.Iic x)) ≤ alpha}

theorem levelAt (p : unitInterval) (n : ℕ) (alpha : ℝ) (nonnegative : 0 ≤ alpha) :
    (binomial n p).real (rejectionAt p n alpha) ≤ alpha := by
  set μ := binomial n p
  have subset : rejectionAt p n alpha ⊆
      {x | μ.real (Set.Ici x) ≤ alpha / 2} ∪ {x | μ.real (Set.Iic x) ≤ alpha / 2} := by
    intro x member
    have small : min (μ.real (Set.Ici x)) (μ.real (Set.Iic x)) ≤ alpha / 2 := by
      have := member
      simp only [rejectionAt, Set.mem_ofPred_eq] at this
      linarith
    rcases min_le_iff.mp small with upper | lower
    · exact Or.inl upper
    · exact Or.inr lower
  calc μ.real (rejectionAt p n alpha)
      ≤ μ.real ({x | μ.real (Set.Ici x) ≤ alpha / 2} ∪ {x | μ.real (Set.Iic x) ≤ alpha / 2}) :=
        measureReal_mono subset
    _ ≤ μ.real {x | μ.real (Set.Ici x) ≤ alpha / 2} +
          μ.real {x | μ.real (Set.Iic x) ≤ alpha / 2} := measureReal_union_le _ _
    _ ≤ alpha / 2 + alpha / 2 :=
        add_le_add (BinomialInterval.upper_tail_valid μ (alpha / 2) (by linarith))
          (BinomialInterval.lower_tail_valid μ n (BinomialInterval.binomial_full n p)
            (alpha / 2) (by linarith))
    _ = alpha := by ring

/-- With equal rates, the exposed share of events is the exposed share of person-time `p`;
the conditional test has Type I error at most alpha for every total rate. -/
theorem typeI (total : ℝ≥0) (p : unitInterval) (alpha : ℝ) (nonnegative : 0 ≤ alpha) :
    (ratesLaw total p).real (given (fun n => rejectionAt p n alpha)) ≤ alpha :=
  compound_le _ _ _ alpha nonnegative (fun n => levelAt p n alpha nonnegative)

theorem coverage (total : ℝ≥0) (a : ℝ) (nonnegative : 0 ≤ a) (π : unitInterval) :
    1 - 2 * a ≤ (ratesLaw total π).real
      (given (fun n => {x | π ∈ BinomialInterval.confidenceSet n a x})) :=
  le_compound _ _ _ _ (fun n => BinomialInterval.coverage n a nonnegative π)

/-- The interval for the exposed share bounds the rate ratio, its odds times the ratio of
unexposed to exposed person-time. -/
theorem rate_ratio_contains (n x aNum aDen : ℕ) (aDen_pos : 0 < aDen)
    (lNum lDen : ℕ) (lower_le : lNum ≤ lDen) (lower_pos : 0 < lDen)
    (uNum uDen : ℕ) (upper_le : uNum ≤ uDen) (upper_pos : 0 < uDen)
    (lowerCheck : lNum = 0 ∨
      OneSampleBinomial.tailNumerator n lNum lDen x * aDen ≤ aNum * lDen ^ n)
    (upperCheck : uNum = uDen ∨
      BinomialInterval.lowerNumerator n uNum uDen x * aDen ≤ aNum * uDen ^ n)
    (k : ℝ) (k_nonneg : 0 ≤ k)
    (π : unitInterval) (member : π ∈ BinomialInterval.confidenceSet n ((aNum : ℝ) / aDen) x)
    (below : (π : ℝ) < 1) :
    Association.odds ((lNum : ℝ) / lDen) * k ≤ Association.odds π * k ∧
      (uNum < uDen → Association.odds π * k ≤ Association.odds ((uNum : ℝ) / uDen) * k) := by
  have bounds := Matched.odds_contains n x aNum aDen aDen_pos lNum lDen lower_le lower_pos
    uNum uDen upper_le upper_pos lowerCheck upperCheck π member below
  exact ⟨mul_le_mul_of_nonneg_right bounds.1 k_nonneg,
    fun upper => mul_le_mul_of_nonneg_right (bounds.2 upper) k_nonneg⟩

/-- The decision of a two-sided exact test as one comparison of whole numbers: twice the
smaller tail, `U / D` or `L / D`, against the level `an / ad`. -/
theorem twice_min_le_iff (U L D an ad : ℕ) (alpha : ℝ) (hD : 0 < D) (had : 0 < ad)
    (level : alpha = (an : ℝ) / ad) :
    2 * min ((U : ℝ) / D) ((L : ℝ) / D) ≤ alpha ↔ 2 * min U L * ad ≤ an * D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have had' : (0 : ℝ) < ad := by exact_mod_cast had
  rw [level, min_div_div_right hD'.le, ← mul_div_assoc, div_le_div_iff₀ hD' had']
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

end StatClaim.Modules.Incidence
