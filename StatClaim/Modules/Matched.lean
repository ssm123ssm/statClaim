module

public import StatClaim.Modules.Association

/-!
McNemar's exact test, and an interval for the conditional odds ratio, in a 1:1 matched
case-control study.

Each pair is one case and one control matched on chosen characteristics. A pair is
discordant when exactly one of the two was exposed. Pairs are independent; given `d`
discordant pairs, the number in which the case is the exposed one is binomial with
probability `π`, and the conditional odds ratio is `π / (1 - π)`. No association within
pairs is `π = 1/2`.

Given `d`, the two-sided exact test rejects when twice the smaller binomial tail at 1/2
is at most alpha; each tail is a valid p-value, so the test has level alpha
(`level`). The number of discordant pairs is binomial too, so averaging keeps the
level (`typeI`) and the coverage of the exact interval for `π` (`pairs_coverage`).
The odds are increasing, so the interval for `π` gives one for the odds ratio
(`odds_contains`). Nothing here concerns cause: exposure was not assigned.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Matched

open MeasureTheory ProbabilityTheory

/-- One half: within a pair, the case and the control are equally likely to be the
exposed one. -/
noncomputable def half : unitInterval := ratPoint 1 2 (by decide) (by decide)

/-- Given `d` discordant pairs, the two-sided exact test rejects when twice the smaller
tail of the binomial law at one half is at most alpha. -/
def rejection (d : ℕ) (alpha : ℝ) : Set ℕ :=
  {x | 2 * min ((binomial d half).real (Set.Ici x)) ((binomial d half).real (Set.Iic x)) ≤
    alpha}

/-- Given the number of discordant pairs, the test has level alpha. -/
theorem level (d : ℕ) (alpha : ℝ) (nonnegative : 0 ≤ alpha) :
    (binomial d half).real (rejection d alpha) ≤ alpha := by
  set μ := binomial d half
  have subset : rejection d alpha ⊆
      {x | μ.real (Set.Ici x) ≤ alpha / 2} ∪ {x | μ.real (Set.Iic x) ≤ alpha / 2} := by
    intro x member
    have small : min (μ.real (Set.Ici x)) (μ.real (Set.Iic x)) ≤ alpha / 2 := by
      have := member
      simp only [rejection, Set.mem_ofPred_eq] at this
      linarith
    rcases min_le_iff.mp small with upper | lower
    · exact Or.inl upper
    · exact Or.inr lower
  calc μ.real (rejection d alpha)
      ≤ μ.real ({x | μ.real (Set.Ici x) ≤ alpha / 2} ∪ {x | μ.real (Set.Iic x) ≤ alpha / 2}) :=
        measureReal_mono subset
    _ ≤ μ.real {x | μ.real (Set.Ici x) ≤ alpha / 2} +
          μ.real {x | μ.real (Set.Iic x) ≤ alpha / 2} := measureReal_union_le _ _
    _ ≤ alpha / 2 + alpha / 2 :=
        add_le_add (BinomialInterval.upper_tail_valid μ (alpha / 2) (by linarith))
          (BinomialInterval.lower_tail_valid μ d (BinomialInterval.binomial_full d half)
            (alpha / 2) (by linarith))
    _ = alpha := by ring

/-- `n` pairs, each discordant with probability `δ`; given `d` discordant pairs, the
number in which the case is the exposed one is binomial with probability `π`. -/
noncomputable def pairsLaw (n : ℕ) (δ π : unitInterval) : Measure (ℕ × ℕ) :=
  Association.mixture n δ (fun d => binomial d π)

/-- The test applied to the observed pairs: the discordant pairs, and those with the case
exposed. -/
def pairsRejection (n : ℕ) (alpha : ℝ) : Set (ℕ × ℕ) :=
  Association.given n (fun d => rejection d alpha)

theorem pairsLaw_univ (n : ℕ) (δ π : unitInterval) : pairsLaw n δ π Set.univ = 1 :=
  Association.mixture_univ n δ _

/-- McNemar's exact test has Type I error at most alpha under no association within
pairs, for every probability that a pair is discordant. -/
theorem typeI (n : ℕ) (δ : unitInterval) (alpha : ℝ) (nonnegative : 0 ≤ alpha) :
    (pairsLaw n δ half).real (pairsRejection n alpha) ≤ alpha :=
  Association.mixture_le n δ _ _ alpha nonnegative (fun d _ => level d alpha nonnegative)

/-- The exact interval for the probability that the case is the exposed one contains it
with probability at least `1 - 2a`, averaged over the number of discordant pairs. -/
theorem pairs_coverage (n : ℕ) (a : ℝ) (nonnegative : 0 ≤ a) (δ π : unitInterval) :
    1 - 2 * a ≤ (pairsLaw n δ π).real
      (Association.given n (fun d => {x | π ∈ BinomialInterval.confidenceSet d a x})) :=
  Association.le_mixture n δ _ _ _ (fun d _ => BinomialInterval.coverage d a nonnegative π)

/-- For one observed count, the interval for `π` bounds the conditional odds ratio. -/
theorem odds_contains (d x aNum aDen : ℕ) (aDen_pos : 0 < aDen)
    (lNum lDen : ℕ) (lower_le : lNum ≤ lDen) (lower_pos : 0 < lDen)
    (uNum uDen : ℕ) (upper_le : uNum ≤ uDen) (upper_pos : 0 < uDen)
    (lowerCheck : lNum = 0 ∨
      OneSampleBinomial.tailNumerator d lNum lDen x * aDen ≤ aNum * lDen ^ d)
    (upperCheck : uNum = uDen ∨
      BinomialInterval.lowerNumerator d uNum uDen x * aDen ≤ aNum * uDen ^ d)
    (π : unitInterval) (member : π ∈ BinomialInterval.confidenceSet d ((aNum : ℝ) / aDen) x)
    (below : (π : ℝ) < 1) :
    Association.odds ((lNum : ℝ) / lDen) ≤ Association.odds π ∧
      (uNum < uDen → Association.odds π ≤ Association.odds ((uNum : ℝ) / uDen)) := by
  have bounds := BinomialInterval.interval_contains d x aNum aDen aDen_pos lNum lDen lower_le
    lower_pos uNum uDen upper_le upper_pos lowerCheck upperCheck π member
  refine ⟨Association.odds_mono (Subtype.coe_le_coe.mpr bounds.1) below, fun upper => ?_⟩
  refine Association.odds_mono (Subtype.coe_le_coe.mpr bounds.2) ?_
  rw [div_lt_one (by exact_mod_cast upper_pos)]
  exact_mod_cast upper

end StatClaim.Modules.Matched
