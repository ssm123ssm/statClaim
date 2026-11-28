module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import StatClaim.Modules.DifferenceTest

/-!
The one-sided Farrington–Manning score rule for a negative risk-difference margin.
The constrained likelihood is maximized on the boundary of the composite null.
Rational score signs bracket every maximizer, including boundary optima.
-/

@[expose] public section

set_option autoImplicit false

namespace StatClaim.Modules.FarringtonManning

open Set MeasureTheory

section Rule

variable {K : Type*} [Field K]

def difference (nc nt x y : ℕ) (delta : K) : K :=
  (y : K) / nt - (x : K) / nc + delta

def score (nc nt x y : ℕ) (delta u : K) : K :=
  (x : K) / u - ((nc - x : ℕ) : K) / (1 - u) +
    (y : K) / (u - delta) - ((nt - y : ℕ) : K) / (1 - u + delta)

def variance (nc nt : ℕ) (delta u : K) : K :=
  u * (1 - u) / nc + (u - delta) * (1 - u + delta) / nt

def lowerVariance (nc nt : ℕ) (delta lo hi : K) : K :=
  lo * (1 - hi) / nc + (lo - delta) * (1 - hi + delta) / nt

def upperVariance (nc nt : ℕ) (delta lo hi : K) : K :=
  lowerVariance nc nt delta hi lo

end Rule

def likelihood (nc nt x y : ℕ) (delta u : ℝ) : ℝ :=
  u ^ x * (1 - u) ^ (nc - x) * (u - delta) ^ y * (1 - u + delta) ^ (nt - y)

/-- The rule uses a positive score and compares its square to the declared cutoff. -/
def rejection (sizes : FixedSampleDesign) (delta cutoff : ℚ) : Set (ℕ × ℕ) :=
  {xy | xy.1 ≤ sizes.nControl ∧ xy.2 ≤ sizes.nTreatment ∧
    let gap := difference sizes.nControl sizes.nTreatment xy.1 xy.2 (delta : ℝ)
    0 < gap ∧ ∃ u ∈ Icc (delta : ℝ) 1,
      IsMaxOn (likelihood sizes.nControl sizes.nTreatment xy.1 xy.2 delta) (Icc (delta : ℝ) 1) u ∧
      (cutoff : ℝ) * variance sizes.nControl sizes.nTreatment (delta : ℝ) u < gap ^ 2}

private theorem score_strictAnti (nc nt x y : ℕ) (delta : ℝ)
    (hd : 0 < delta) (hn : 0 < nc) :
    StrictAntiOn (score nc nt x y delta) (Ioo delta 1) := by
  intro u hu v hv huv
  have hu0 : 0 < u := hd.trans hu.1
  have hv0 : 0 < v := hd.trans hv.1
  have h1u := sub_pos.mpr hu.2
  have h1v := sub_pos.mpr hv.2
  have a := div_le_div_of_nonneg_left (show 0 ≤ (x : ℝ) by positivity) hu0 huv.le
  have b := div_le_div_of_nonneg_left (show 0 ≤ ((nc - x : ℕ) : ℝ) by positivity)
    h1v (show 1 - v ≤ 1 - u by linarith)
  have c := div_le_div_of_nonneg_left (show 0 ≤ (y : ℝ) by positivity)
    (sub_pos.mpr hu.1) (show u - delta ≤ v - delta by linarith)
  have d := div_le_div_of_nonneg_left (show 0 ≤ ((nt - y : ℕ) : ℝ) by positivity)
    (show 0 < 1 - v + delta by linarith) (show 1 - v + delta ≤ 1 - u + delta by linarith)
  unfold score
  by_cases h : x = 0
  · have count : (0 : ℝ) < ((nc - x : ℕ) : ℝ) := by
      rw [h, Nat.sub_zero]
      exact_mod_cast hn
    have strict := div_lt_div_of_pos_left count h1v (show 1 - v < 1 - u by linarith)
    linarith
  · have count : (0 : ℝ) < (x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have strict := div_lt_div_of_pos_left count hu0 huv
    linarith

private theorem hasDerivAt_pow_score {f : ℝ → ℝ} {f' u : ℝ}
    (hf : HasDerivAt f f' u) (hfu : f u ≠ 0) (k : ℕ) :
    HasDerivAt (fun v => f v ^ k) (f u ^ k * ((k : ℝ) * f' / f u)) u := by
  convert hf.pow k using 1
  cases k with
  | zero => simp
  | succ k =>
    simp only [pow_succ (f u) k, Nat.succ_sub_one]
    field_simp

private theorem likelihood_deriv (nc nt x y : ℕ) (delta u : ℝ) (hd : 0 < delta)
    (hu : u ∈ Ioo delta 1) :
    deriv (likelihood nc nt x y delta) u =
      likelihood nc nt x y delta u * score nc nt x y delta u := by
  have hA : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id u
  have hB : HasDerivAt (fun v : ℝ => 1 - v) (-1) u := by
    simpa only [zero_sub] using hA.const_sub (1 : ℝ)
  have hC := hA.sub_const delta
  have hD := hB.add_const delta
  have a := hasDerivAt_pow_score hA (ne_of_gt (hd.trans hu.1)) x
  have b := hasDerivAt_pow_score hB (ne_of_gt (sub_pos.mpr hu.2)) (nc - x)
  have c := hasDerivAt_pow_score hC (ne_of_gt (sub_pos.mpr hu.1)) y
  have d := hasDerivAt_pow_score hD
    (ne_of_gt (show 0 < 1 - u + delta from add_pos (sub_pos.mpr hu.2) hd)) (nt - y)
  have h := ((a.mul b).mul c).mul d
  rw [show deriv (likelihood nc nt x y delta) u = _ from h.deriv]
  unfold likelihood score
  simp only [Pi.mul_apply, mul_one, mul_neg, neg_div]
  ring

private theorem likelihood_pos (nc nt x y : ℕ) (delta u : ℝ) (hd : 0 < delta)
    (hu : u ∈ Ioo delta 1) : 0 < likelihood nc nt x y delta u := by
  have hu0 := hd.trans hu.1
  have h1u := sub_pos.mpr hu.2
  have hshift := sub_pos.mpr hu.1
  unfold likelihood
  positivity

private theorem max_ge (nc nt x y : ℕ) {delta u m : ℝ} (hd : 0 < delta)
    (hn : 0 < nc) (hu : u ∈ Icc delta 1)
    (hm : m ∈ Ioo delta 1) (hmax : IsMaxOn (likelihood nc nt x y delta) (Icc delta 1) u)
    (hscore : 0 ≤ score nc nt x y delta m) : m ≤ u := by
  by_contra! lt
  have increasing : StrictMonoOn (likelihood nc nt x y delta) (Icc delta m) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold likelihood; fun_prop)
    intro v hv
    rw [interior_Icc] at hv
    have hv' : v ∈ Ioo delta 1 := ⟨hv.1, hv.2.trans hm.2⟩
    rw [likelihood_deriv nc nt x y delta v hd hv']
    exact mul_pos (likelihood_pos nc nt x y delta v hd hv')
      (hscore.trans_lt (score_strictAnti nc nt x y delta hd hn hv' hm hv.2))
  exact (not_lt_of_ge (hmax ⟨hm.1.le, hm.2.le⟩))
    (increasing ⟨hu.1, lt.le⟩ ⟨hm.1.le, le_rfl⟩ lt)

private theorem max_le (nc nt x y : ℕ) {delta u m : ℝ} (hd : 0 < delta)
    (hn : 0 < nc) (hu : u ∈ Icc delta 1)
    (hm : m ∈ Ioo delta 1) (hmax : IsMaxOn (likelihood nc nt x y delta) (Icc delta 1) u)
    (hscore : score nc nt x y delta m ≤ 0) : u ≤ m := by
  by_contra! lt
  have decreasing : StrictAntiOn (likelihood nc nt x y delta) (Icc m 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by unfold likelihood; fun_prop)
    intro v hv
    rw [interior_Icc] at hv
    have hv' : v ∈ Ioo delta 1 := ⟨hm.1.trans hv.1, hv.2⟩
    rw [likelihood_deriv nc nt x y delta v hd hv']
    exact mul_neg_of_pos_of_neg (likelihood_pos nc nt x y delta v hd hv')
      ((score_strictAnti nc nt x y delta hd hn hm hv' hv.1).trans_le hscore)
  exact (not_lt_of_ge (hmax ⟨hm.1.le, hm.2.le⟩))
    (decreasing ⟨le_rfl, hm.2.le⟩ ⟨lt.le, hu.2⟩ lt)

/-- Check the likelihood bracket using exact rationals. The endpoints of the parameter
space are legal bracket endpoints without a score evaluation. -/
def bracketOk (nc nt x y : ℕ) (delta lo hi : ℚ) : Prop :=
  delta ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1 ∧
    (lo = delta ∨ lo < 1 ∧ 0 ≤ score nc nt x y delta lo) ∧
    (hi = 1 ∨ delta < hi ∧ score nc nt x y delta hi ≤ 0)

instance (nc nt x y : ℕ) (delta lo hi : ℚ) : Decidable (bracketOk nc nt x y delta lo hi) := by
  unfold bracketOk
  infer_instance

private theorem score_cast (nc nt x y : ℕ) (delta u : ℚ) :
    ((score nc nt x y delta u : ℚ) : ℝ) = score nc nt x y (delta : ℝ) (u : ℝ) := by
  simp [score]

private theorem bracket_contains (nc nt x y : ℕ) {delta lo hi : ℚ}
    (hd : 0 < delta) (hn : 0 < nc)
    (checked : bracketOk nc nt x y delta lo hi) {u : ℝ} (hu : u ∈ Icc (delta : ℝ) 1)
    (hmax : IsMaxOn (likelihood nc nt x y delta) (Icc (delta : ℝ) 1) u) :
    (lo : ℝ) ≤ u ∧ u ≤ (hi : ℝ) := by
  obtain ⟨hlo, order, hhi, hleft, hright⟩ := checked
  have hd' : (0 : ℝ) < (delta : ℝ) := by exact_mod_cast hd
  constructor
  · rcases hleft with rfl | ⟨hlo1, s⟩
    · exact hu.1
    · rcases hlo.eq_or_lt with rfl | hlo
      · exact hu.1
      apply max_ge nc nt x y (m := (lo : ℝ)) hd' hn hu ⟨by exact_mod_cast hlo, by exact_mod_cast hlo1⟩ hmax
      simpa only [Rat.cast_zero, score_cast] using (Rat.cast_le (K := ℝ)).mpr s
  · rcases hright with rfl | ⟨hhi0, s⟩
    · simpa using hu.2
    · rcases hhi.eq_or_lt with rfl | hhi
      · simpa using hu.2
      apply max_le nc nt x y (m := (hi : ℝ)) hd' hn hu ⟨by exact_mod_cast hhi0, by exact_mod_cast hhi⟩ hmax
      simpa only [Rat.cast_zero, score_cast] using (Rat.cast_le (K := ℝ)).mpr s

private theorem variance_bounds (nc nt : ℕ) {delta lo hi u : ℝ}
    (hd : 0 ≤ delta) (hlo : delta ≤ lo) (hu : lo ≤ u ∧ u ≤ hi) (hhi : hi ≤ 1) :
    lowerVariance nc nt delta lo hi ≤ variance nc nt delta u ∧
      variance nc nt delta u ≤ upperVariance nc nt delta lo hi := by
  have hulo := hu.1
  have huhi := hu.2
  constructor <;> simp only [upperVariance, lowerVariance, variance] <;> gcongr <;> linarith

noncomputable def analysis (sizes : FixedSampleDesign) (delta cutoff : ℚ) :
    Core.PolicyAnalysis (Core.Policy.fixed (TwoArmBinomial.model sizes)) where
  hypothesis := TwoArmBinomial.proportionDifferenceAtMost (-delta)
  rejection := rejection sizes delta cutoff
  rejection_measurable := .of_discrete

structure RegionHint where
  thresholds : List ℕ
  brackets : List (ℚ × ℚ)

def RegionHint.bracket (h : RegionHint) (nt x y : ℕ) (delta : ℚ) : ℚ × ℚ :=
  h.brackets.getD (x * (nt + 1) + y) (delta, 1)

/-- The upper region contains every rejection. The lower region contains only
rejections. These checks can leave a table out of the lower region while including
it in the upper region when its score is too close to the cutoff. -/
def tableCheck (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (upper : Bool) (x y : ℕ) : Prop :=
  let nc := sizes.nControl
  let nt := sizes.nTreatment
  let gap := difference nc nt x y delta
  let (lo, hi) := h.bracket nt x y delta
  if DifferenceTest.rejects nt h.thresholds x y = upper then True
  else if upper then
    gap ≤ 0 ∨ bracketOk nc nt x y delta lo hi ∧
      gap ^ 2 ≤ cutoff * lowerVariance nc nt delta lo hi
  else
    0 < gap ∧ bracketOk nc nt x y delta lo hi ∧
      cutoff * upperVariance nc nt delta lo hi < gap ^ 2

instance (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (upper : Bool) (x y : ℕ) : Decidable (tableCheck sizes delta cutoff h upper x y) := by
  unfold tableCheck
  infer_instance

def regionCheck (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (upper : Bool) : Bool :=
  decide (0 < delta ∧ delta < 1 ∧ 0 < cutoff) &&
  decide (∀ x, x < sizes.nControl + 1 → ∀ y, y < sizes.nTreatment + 1 →
    tableCheck sizes delta cutoff h upper x y)

private theorem difference_cast (nc nt x y : ℕ) (delta : ℚ) :
    ((difference nc nt x y delta : ℚ) : ℝ) = difference nc nt x y (delta : ℝ) := by
  simp [difference]

private theorem lowerVariance_cast (nc nt : ℕ) (delta lo hi : ℚ) :
    ((lowerVariance nc nt delta lo hi : ℚ) : ℝ) =
      lowerVariance nc nt (delta : ℝ) (lo : ℝ) (hi : ℝ) := by
  simp [lowerVariance]

private theorem upper_subset (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (ok : regionCheck sizes delta cutoff h true = true) :
    rejection sizes delta cutoff ⊆ DifferenceTest.region sizes.nTreatment h.thresholds := by
  obtain ⟨range, checks⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hd, _, hc⟩ := of_decide_eq_true range
  intro ⟨x, y⟩ member
  obtain ⟨hx, hy, gap, u, hu, hmax, rejected⟩ := member
  change DifferenceTest.rejects sizes.nTreatment h.thresholds x y = true
  by_contra! outside
  have trial := (of_decide_eq_true checks) x (by omega) y (by omega)
  simp only [tableCheck, ite_eq_right outside, ite_true] at trial
  rcases trial with sign | ⟨bracket, bound⟩
  · have signR := (Rat.cast_le (K := ℝ)).mpr sign
    rw [difference_cast, Rat.cast_zero] at signR
    exact (not_lt_of_ge signR) gap
  · have sides := bracket_contains _ _ _ _ hd sizes.controlPositive bracket hu hmax
    have vb := (variance_bounds sizes.nControl sizes.nTreatment (delta := (delta : ℝ))
      (by exact_mod_cast hd.le) (by exact_mod_cast bracket.1) sides
      (by exact_mod_cast bracket.2.2.1)).1
    have boundR := (Rat.cast_le (K := ℝ)).mpr bound
    simp only [Rat.cast_pow, Rat.cast_mul, difference_cast, lowerVariance_cast] at boundR
    exact (not_lt_of_ge (boundR.trans (mul_le_mul_of_nonneg_left vb
      (by exact_mod_cast hc.le)))) rejected

private theorem lower_subset (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (ok : regionCheck sizes delta cutoff h false = true) :
    DifferenceTest.region sizes.nTreatment h.thresholds ∩
      ↑(binomialCountSupport sizes.nControl sizes.nTreatment) ⊆ rejection sizes delta cutoff := by
  obtain ⟨range, checks⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨hd, hd1, hc⟩ := of_decide_eq_true range
  intro ⟨x, y⟩ member
  have selected : DifferenceTest.rejects sizes.nTreatment h.thresholds x y = true := member.1
  have feasible := member.2
  simp only [Finset.mem_coe, binomialCountSupport, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff] at feasible
  obtain ⟨hx, hy⟩ := feasible
  have trial := (of_decide_eq_true checks) x (by omega) y (by omega)
  simp only [tableCheck, selected, Bool.true_eq_false, ite_false] at trial
  obtain ⟨sign, bracket, bound⟩ := trial
  have hdR : (delta : ℝ) < 1 := by exact_mod_cast hd1
  obtain ⟨u, hu, max⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hdR.le)
    (show ContinuousOn (likelihood sizes.nControl sizes.nTreatment x y delta) _ by
      unfold likelihood
      fun_prop)
  have sides := bracket_contains _ _ _ _ hd sizes.controlPositive bracket hu max
  have vb := (variance_bounds sizes.nControl sizes.nTreatment (delta := (delta : ℝ))
    (by exact_mod_cast hd.le) (by exact_mod_cast bracket.1) sides
    (by exact_mod_cast bracket.2.2.1)).2
  have signR := (Rat.cast_lt (K := ℝ)).mpr sign
  rw [difference_cast, Rat.cast_zero] at signR
  have boundR := (Rat.cast_lt (K := ℝ)).mpr bound
  simp only [upperVariance, Rat.cast_pow, Rat.cast_mul, difference_cast, lowerVariance_cast] at boundR
  exact ⟨hx, hy, signR, u, hu, max,
    (mul_le_mul_of_nonneg_left vb (by exact_mod_cast hc.le)).trans_lt boundR⟩

/-- A monotone region enclosing every rejection gives a bound on the entire null. -/
theorem typeI_of_region (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (checked : regionCheck sizes delta cutoff h true = true) (bound : ℝ)
    (upper : ((DifferenceTest.analysis sizes h.thresholds (-delta)).typeIClaim bound).statement) :
    ((analysis sizes delta cutoff).typeIClaim bound).statement := by
  intro theta null
  have cap := upper theta null
  rw [Core.Policy.fixed_law] at cap ⊢
  exact (measureReal_mono (μ := productBinomial sizes.nControl sizes.nTreatment theta.1 theta.2)
    (upper_subset sizes delta cutoff h checked)).trans cap

/-- An exact probability of the inner region is a lower bound at the chosen null rates. -/
theorem probability_ge_of_region (sizes : FixedSampleDesign) (delta cutoff : ℚ) (h : RegionHint)
    (checked : regionCheck sizes delta cutoff h false = true) (p q : unitInterval) :
    (productBinomial sizes.nControl sizes.nTreatment p q).real
        (DifferenceTest.region sizes.nTreatment h.thresholds) ≤
      (productBinomial sizes.nControl sizes.nTreatment p q).real (rejection sizes delta cutoff) := by
  classical
  rw [productBinomial_real_eq_sum, productBinomial_real_eq_sum]
  apply Finset.sum_le_sum
  intro counts supported
  by_cases member : counts ∈ DifferenceTest.region sizes.nTreatment h.thresholds
  · simp only [member, ite_true,
      lower_subset sizes delta cutoff h checked ⟨member, Finset.mem_coe.mpr supported⟩]
    exact le_rfl
  · simp only [member, ite_false]
    split
    · exact mul_nonneg (binomialMass_nonnegative _ _ _ p.property.1 p.property.2)
        (binomialMass_nonnegative _ _ _ q.property.1 q.property.2)
    · exact le_rfl

end StatClaim.Modules.FarringtonManning
