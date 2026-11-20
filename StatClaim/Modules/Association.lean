module

public import StatClaim.Fisher
public import StatClaim.Modules.BinomialInterval

/-!
Fisher's exact test of no association, and intervals for effect measures, in an
observational 2×2 study.

A cohort study fixes how many exposed and unexposed participants are followed; a
case-control study fixes how many cases and controls are sampled. Either way the
table holds two independent binomial counts, and no association makes their
success probabilities equal. That is the model of `StatClaim.Fisher`, with the
two groups in place of arms, so `groups_typeI_le_alpha` is Fisher's theorem.

A cross-sectional study, or a cohort that does not fix how many are exposed, fixes
only the total. Under independent sampling the number exposed is binomial, and
given that number the outcome counts are two independent binomials: `mixture`.
Every multinomial law of a 2×2 table has this form, with the probability of
exposure and the probability of the outcome in each group as its parameters.
A bound that holds given every number exposed holds on average (`mixture_le`,
`le_mixture`), so Fisher's test keeps its level (`mixture_typeI_le_alpha`) and
the groups' exact confidence sets keep their joint coverage
(`mixture_joint_coverage`).

Intervals for a difference, a ratio or an odds ratio follow from intervals for
each group's probability (`ratio_contains`, `odds_ratio_contains`). No theorem
here concerns cause: exposure was not assigned.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.Association

open MeasureTheory

/-- Fixed groups: Fisher's bound, for every common probability in [0, 1]. -/
theorem groups_typeI_le_alpha (first second : ℕ) (p : unitInterval) (alpha : ℚ)
    (alpha_nonnegative : 0 ≤ alpha) :
    (fisherNullLaw first second p).real (fisherRejectionRegionAt first second alpha) ≤
      (alpha : ℝ) :=
  fisher_typeI_error_le_alpha first second p alpha alpha_nonnegative

/-- A table of a sample whose number exposed is random: the number exposed, then the
outcome counts among the unexposed and among the exposed. -/
abbrev Table := ℕ × (ℕ × ℕ)

/-- `n` participants, each exposed with probability `q`; given `k` exposed, the counts
follow `inner k`. -/
noncomputable def mixture (n : ℕ) (q : unitInterval) (inner : ℕ → Measure (ℕ × ℕ)) :
    Measure Table :=
  ∑ k ∈ Finset.range (n + 1),
    ENNReal.ofReal (binomialMass n (q : ℝ) k) • (Measure.dirac k).prod (inner k)

/-- An event that depends on the number exposed. -/
def given (n : ℕ) (event : ℕ → Set (ℕ × ℕ)) : Set Table :=
  {table | table.1 ≤ n ∧ table.2 ∈ event table.1}

theorem term_apply (n k : ℕ) (k_le : k ≤ n) (inner : Measure (ℕ × ℕ)) [SFinite inner]
    (event : ℕ → Set (ℕ × ℕ)) :
    (Measure.dirac k).prod inner (given n event) = inner (event k) := by
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (.of_discrete)]
  congr 1
  ext counts
  simp [given, k_le]

theorem weights_sum (n : ℕ) (q : unitInterval) :
    ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (binomialMass n (q : ℝ) k) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun k _ => binomialMass_nonnegative n (q : ℝ) k q.property.1 q.property.2),
    binomialMass_sum_one, ENNReal.ofReal_one]

theorem mixture_apply (n : ℕ) (q : unitInterval) (inner : ℕ → Measure (ℕ × ℕ))
    [∀ k, SFinite (inner k)] (event : ℕ → Set (ℕ × ℕ)) :
    mixture n q inner (given n event) =
      ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (binomialMass n (q : ℝ) k) * inner k (event k) := by
  simp only [mixture, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k member
  rw [term_apply n k (Nat.lt_succ_iff.mp (Finset.mem_range.mp member))]

theorem mixture_univ (n : ℕ) (q : unitInterval) (inner : ℕ → Measure (ℕ × ℕ))
    [∀ k, IsProbabilityMeasure (inner k)] : mixture n q inner Set.univ = 1 := by
  simp only [mixture, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  exact weights_sum n q

instance mixture_isProbabilityMeasure (n : ℕ) (q : unitInterval) (inner : ℕ → Measure (ℕ × ℕ))
    [∀ k, IsProbabilityMeasure (inner k)] : IsProbabilityMeasure (mixture n q inner) :=
  ⟨mixture_univ n q inner⟩

/-- Averaging keeps an upper bound that holds for every number exposed. -/
theorem mixture_le (n : ℕ) (q : unitInterval) (inner : ℕ → Measure (ℕ × ℕ))
    [∀ k, IsProbabilityMeasure (inner k)] (event : ℕ → Set (ℕ × ℕ)) (c : ℝ) (hc : 0 ≤ c)
    (bound : ∀ k ≤ n, (inner k).real (event k) ≤ c) :
    (mixture n q inner).real (given n event) ≤ c := by
  have total : mixture n q inner (given n event) ≤ ENNReal.ofReal c := by
    rw [mixture_apply]
    calc _ ≤ ∑ k ∈ Finset.range (n + 1), ENNReal.ofReal (binomialMass n (q : ℝ) k) *
            ENNReal.ofReal c := by
          apply Finset.sum_le_sum
          intro k member
          gcongr
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal
            (bound k (Nat.lt_succ_iff.mp (Finset.mem_range.mp member)))
      _ = ENNReal.ofReal c := by rw [← Finset.sum_mul, weights_sum, one_mul]
  exact ENNReal.toReal_le_of_le_ofReal hc total

/-- Averaging keeps a lower bound that holds for every number exposed. -/
theorem le_mixture (n : ℕ) (q : unitInterval) (inner : ℕ → Measure (ℕ × ℕ))
    [∀ k, IsProbabilityMeasure (inner k)] (event : ℕ → Set (ℕ × ℕ)) (c : ℝ)
    (bound : ∀ k ≤ n, c ≤ (inner k).real (event k)) :
    c ≤ (mixture n q inner).real (given n event) := by
  rcases le_or_gt c 0 with nonpositive | positive
  · exact nonpositive.trans measureReal_nonneg
  have total : ENNReal.ofReal c ≤ mixture n q inner (given n event) := by
    rw [mixture_apply]
    calc ENNReal.ofReal c = ∑ k ∈ Finset.range (n + 1),
            ENNReal.ofReal (binomialMass n (q : ℝ) k) * ENNReal.ofReal c := by
          rw [← Finset.sum_mul, weights_sum, one_mul]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro k member
          gcongr
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal
            (bound k (Nat.lt_succ_iff.mp (Finset.mem_range.mp member)))
  rw [measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp total

/-- The law of a table with a random number exposed, under no association. -/
noncomputable def mixtureLaw (n : ℕ) (q p : unitInterval) : Measure Table :=
  mixture n q (fun k => fisherNullLaw (n - k) k p)

/-- Fisher's test applied to the observed table, with the observed group sizes. -/
def mixtureRejection (n : ℕ) (alpha : ℚ) : Set Table :=
  given n (fun k => fisherRejectionRegionAt (n - k) k alpha)

/-- The mixture is a probability law. -/
theorem mixtureLaw_univ (n : ℕ) (q p : unitInterval) : mixtureLaw n q p Set.univ = 1 :=
  mixture_univ n q _

/-- With the number exposed random, Fisher's test of no association has Type I error at
most alpha, for every exposure probability and every common outcome probability. -/
theorem mixture_typeI_le_alpha (n : ℕ) (q p : unitInterval) (alpha : ℚ)
    (alpha_nonnegative : 0 ≤ alpha) :
    (mixtureLaw n q p).real (mixtureRejection n alpha) ≤ (alpha : ℝ) :=
  mixture_le n q _ _ (alpha : ℝ) (by exact_mod_cast alpha_nonnegative)
    (fun k _ => groups_typeI_le_alpha (n - k) k p alpha alpha_nonnegative)

/-- With the number exposed random, the two groups' exact confidence sets both contain
their true probabilities with probability at least `(1 - 2a)^2`, for every probability
of exposure and every pair of outcome probabilities. -/
theorem mixture_joint_coverage (n : ℕ) (a : ℝ) (nonnegative : 0 ≤ a) (small : 2 * a ≤ 1)
    (q pc pt : unitInterval) :
    (1 - 2 * a) ^ 2 ≤ (mixture n q (fun k => productBinomial (n - k) k pc pt)).real
      (given n (fun k => {x | pc ∈ BinomialInterval.confidenceSet (n - k) a x} ×ˢ
        {y | pt ∈ BinomialInterval.confidenceSet k a y})) :=
  le_mixture n q _ _ _
    (fun k _ => BinomialInterval.joint_coverage (n - k) k a nonnegative small pc pt)

/-- The odds of a probability below one. -/
noncomputable def odds (p : ℝ) : ℝ := p / (1 - p)

theorem odds_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p < 1) : 0 ≤ odds p :=
  div_nonneg h0 (by linarith)

theorem odds_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 0 < odds p :=
  div_pos h0 (by linarith)

theorem odds_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) : odds a ≤ odds b := by
  unfold odds
  have h1 : 0 < 1 - b := by linarith
  have h2 : 0 < 1 - a := by linarith
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

theorem ratio_lower {cU tL pc pt : ℝ} (hpc : 0 < pc) (hcU : pc ≤ cU) (htL : tL ≤ pt)
    (htL0 : 0 ≤ tL) : tL / cU ≤ pt / pc :=
  calc tL / cU ≤ tL / pc := div_le_div_of_nonneg_left htL0 hpc hcU
    _ ≤ pt / pc := div_le_div_of_nonneg_right htL hpc.le

theorem ratio_upper {cL tU pc pt : ℝ} (hcL : 0 < cL) (hcLpc : cL ≤ pc) (htU : pt ≤ tU)
    (hpt : 0 ≤ pt) : pt / pc ≤ tU / cL :=
  calc pt / pc ≤ pt / cL := div_le_div_of_nonneg_left hpt hcL hcLpc
    _ ≤ tU / cL := div_le_div_of_nonneg_right htU hcL.le

/-- Bounds on a ratio of two probabilities from bounds on each. The ratio is defined when
the denominator's probability is positive; its upper bound needs a positive lower end. -/
theorem ratio_bounds {cL cU tL tU pc pt : ℝ} (hc : cL ≤ pc ∧ pc ≤ cU) (ht : tL ≤ pt ∧ pt ≤ tU)
    (htL0 : 0 ≤ tL) (hpc : 0 < pc) :
    tL / cU ≤ pt / pc ∧ (0 < cL → pt / pc ≤ tU / cL) :=
  ⟨ratio_lower hpc hc.2 ht.1 htL0,
    fun hcL => ratio_upper hcL hc.1 ht.2 (htL0.trans ht.1)⟩

/-- Bounds on an odds ratio from bounds on each probability, for probabilities strictly
inside (0, 1) in the denominator and below 1 in the numerator. -/
theorem odds_ratio_bounds {cL cU tL tU pc pt : ℝ} (hc : cL ≤ pc ∧ pc ≤ cU)
    (ht : tL ≤ pt ∧ pt ≤ tU) (htL0 : 0 ≤ tL) (hpc0 : 0 < pc) (hpc1 : pc < 1) (hpt1 : pt < 1) :
    0 ≤ odds pt / odds pc ∧
      (cU < 1 → odds tL / odds cU ≤ odds pt / odds pc) ∧
      (0 < cL → tU < 1 → odds pt / odds pc ≤ odds tU / odds cL) := by
  have hpt0 : 0 ≤ pt := htL0.trans ht.1
  refine ⟨div_nonneg (odds_nonneg hpt0 hpt1) (odds_pos hpc0 hpc1).le, fun hcU1 => ?_,
    fun hcL htU1 => ?_⟩
  · exact ratio_lower (odds_pos hpc0 hpc1) (odds_mono hc.2 hcU1) (odds_mono ht.1 hpt1)
      (odds_nonneg htL0 (lt_of_le_of_lt ht.1 hpt1))
  · exact ratio_upper (odds_pos hcL (lt_of_le_of_lt hc.1 hpc1)) (odds_mono hc.1 hpc1)
      (odds_mono ht.2 htU1) (odds_nonneg hpt0 (lt_of_le_of_lt ht.2 htU1))

/-- The interval for each group's probability, checked for one observed table, bounds the
ratio of the probabilities. -/
theorem ratio_contains (n m x y aNum aDen : ℕ) (aDen_pos : 0 < aDen)
    (cLNum cLDen : ℕ) (cL_le : cLNum ≤ cLDen) (cL_pos : 0 < cLDen)
    (cUNum cUDen : ℕ) (cU_le : cUNum ≤ cUDen) (cU_pos : 0 < cUDen)
    (tLNum tLDen : ℕ) (tL_le : tLNum ≤ tLDen) (tL_pos : 0 < tLDen)
    (tUNum tUDen : ℕ) (tU_le : tUNum ≤ tUDen) (tU_pos : 0 < tUDen)
    (cLower : cLNum = 0 ∨
      OneSampleBinomial.tailNumerator n cLNum cLDen x * aDen ≤ aNum * cLDen ^ n)
    (cUpper : cUNum = cUDen ∨
      BinomialInterval.lowerNumerator n cUNum cUDen x * aDen ≤ aNum * cUDen ^ n)
    (tLower : tLNum = 0 ∨
      OneSampleBinomial.tailNumerator m tLNum tLDen y * aDen ≤ aNum * tLDen ^ m)
    (tUpper : tUNum = tUDen ∨
      BinomialInterval.lowerNumerator m tUNum tUDen y * aDen ≤ aNum * tUDen ^ m)
    (pc pt : unitInterval)
    (control : pc ∈ BinomialInterval.confidenceSet n ((aNum : ℝ) / aDen) x)
    (treatment : pt ∈ BinomialInterval.confidenceSet m ((aNum : ℝ) / aDen) y)
    (positive : 0 < (pc : ℝ)) :
    ((tLNum : ℝ) / tLDen) / ((cUNum : ℝ) / cUDen) ≤ (pt : ℝ) / pc ∧
      (0 < cLNum → (pt : ℝ) / pc ≤ ((tUNum : ℝ) / tUDen) / ((cLNum : ℝ) / cLDen)) := by
  have c := BinomialInterval.interval_contains n x aNum aDen aDen_pos cLNum cLDen cL_le cL_pos
    cUNum cUDen cU_le cU_pos cLower cUpper pc control
  have t := BinomialInterval.interval_contains m y aNum aDen aDen_pos tLNum tLDen tL_le tL_pos
    tUNum tUDen tU_le tU_pos tLower tUpper pt treatment
  have bounds := ratio_bounds (cL := (cLNum : ℝ) / cLDen) (cU := (cUNum : ℝ) / cUDen)
    (tL := (tLNum : ℝ) / tLDen) (tU := (tUNum : ℝ) / tUDen)
    ⟨Subtype.coe_le_coe.mpr c.1, Subtype.coe_le_coe.mpr c.2⟩
    ⟨Subtype.coe_le_coe.mpr t.1, Subtype.coe_le_coe.mpr t.2⟩ (by positivity) positive
  exact ⟨bounds.1, fun hcL => bounds.2 (by positivity)⟩

/-- The interval for each group's probability, checked for one observed table, bounds the
odds ratio. -/
theorem odds_ratio_contains (n m x y aNum aDen : ℕ) (aDen_pos : 0 < aDen)
    (cLNum cLDen : ℕ) (cL_le : cLNum ≤ cLDen) (cL_pos : 0 < cLDen)
    (cUNum cUDen : ℕ) (cU_le : cUNum ≤ cUDen) (cU_pos : 0 < cUDen)
    (tLNum tLDen : ℕ) (tL_le : tLNum ≤ tLDen) (tL_pos : 0 < tLDen)
    (tUNum tUDen : ℕ) (tU_le : tUNum ≤ tUDen) (tU_pos : 0 < tUDen)
    (cLower : cLNum = 0 ∨
      OneSampleBinomial.tailNumerator n cLNum cLDen x * aDen ≤ aNum * cLDen ^ n)
    (cUpper : cUNum = cUDen ∨
      BinomialInterval.lowerNumerator n cUNum cUDen x * aDen ≤ aNum * cUDen ^ n)
    (tLower : tLNum = 0 ∨
      OneSampleBinomial.tailNumerator m tLNum tLDen y * aDen ≤ aNum * tLDen ^ m)
    (tUpper : tUNum = tUDen ∨
      BinomialInterval.lowerNumerator m tUNum tUDen y * aDen ≤ aNum * tUDen ^ m)
    (pc pt : unitInterval)
    (control : pc ∈ BinomialInterval.confidenceSet n ((aNum : ℝ) / aDen) x)
    (treatment : pt ∈ BinomialInterval.confidenceSet m ((aNum : ℝ) / aDen) y)
    (positive : 0 < (pc : ℝ)) (below : (pc : ℝ) < 1) (treatedBelow : (pt : ℝ) < 1) :
    0 ≤ odds pt / odds pc ∧
      (cUNum < cUDen → odds ((tLNum : ℝ) / tLDen) / odds ((cUNum : ℝ) / cUDen) ≤
        odds pt / odds pc) ∧
      (0 < cLNum → tUNum < tUDen →
        odds pt / odds pc ≤ odds ((tUNum : ℝ) / tUDen) / odds ((cLNum : ℝ) / cLDen)) := by
  have c := BinomialInterval.interval_contains n x aNum aDen aDen_pos cLNum cLDen cL_le cL_pos
    cUNum cUDen cU_le cU_pos cLower cUpper pc control
  have t := BinomialInterval.interval_contains m y aNum aDen aDen_pos tLNum tLDen tL_le tL_pos
    tUNum tUDen tU_le tU_pos tLower tUpper pt treatment
  have bounds := odds_ratio_bounds (cL := (cLNum : ℝ) / cLDen) (cU := (cUNum : ℝ) / cUDen)
    (tL := (tLNum : ℝ) / tLDen) (tU := (tUNum : ℝ) / tUDen)
    ⟨Subtype.coe_le_coe.mpr c.1, Subtype.coe_le_coe.mpr c.2⟩
    ⟨Subtype.coe_le_coe.mpr t.1, Subtype.coe_le_coe.mpr t.2⟩ (by positivity) positive below
    treatedBelow
  refine ⟨bounds.1, fun hcU => bounds.2.1 ?_, fun hcL htU => bounds.2.2 (by positivity) ?_⟩
  · rw [div_lt_one (by exact_mod_cast cU_pos)]
    exact_mod_cast hcU
  · rw [div_lt_one (by exact_mod_cast tU_pos)]
    exact_mod_cast htU

end StatClaim.Modules.Association
