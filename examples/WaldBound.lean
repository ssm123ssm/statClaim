import StatClaim.WaldBound

/-!
An upper bound for the standard two-sided 5% unpooled Wald rule with 20
observations in each arm. The squared normal cutoff is between 3.84 and 3.85.
The proof applies to every real cutoff in that interval.
-/

namespace StatClaim.Examples.WaldBound

private def waldHalfRejectingWeight (n a b : ℕ) : ℕ :=
  ∑ total ∈ Finset.range (2 * n + 1),
    2 * ∑ j ∈ Finset.range (min n total + 1 - balancedWaldUpperCutoff n a b total),
      hypergeometricWeight n n total (balancedWaldUpperCutoff n a b total + j)

private theorem waldProbability_eq_halfWeights (n a b : ℕ)
    (den_pos : 0 < b * (2 * n) + a) :
    balancedWaldNullRejectionProbability n a b (1 / 2) =
      (waldHalfRejectingWeight n a b : ℝ) / 2 ^ (2 * n) := by
  rw [balancedWaldNullRejectionProbability_eq_pooledSum n a b _ den_pos]
  push_cast [waldHalfRejectingWeight]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro total ht
  have ht' : total ≤ 2 * n := by simpa using ht
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hhalf, ← pow_add, Nat.add_sub_of_le ht', one_div_pow, mul_one_div]

/-- With 20 observations per arm and equal true probabilities of one half,
every squared cutoff between 3.84 and 3.85 gives this exact null rejection
probability. The usual two-sided 5% normal cutoff lies in this range. -/
theorem balancedWaldTwentyAtHalf (cutoff : ℝ)
    (hlo : (96 : ℝ) / 25 ≤ cutoff) (hhi : cutoff ≤ (77 : ℝ) / 20) :
    balancedWaldNullRejectionProbabilityAt 20 cutoff (1 / 2) =
      (22195551235 : ℝ) / 274877906944 := by
  have anti := balancedWaldNullRejectionProbabilityAt_antitone 20 (1 / 2)
    (by decide) (by norm_num) (by norm_num)
  have lower := anti hhi
  have upper := anti hlo
  have weightLo : waldHalfRejectingWeight 20 96 25 = 88782204940 := by decide +kernel
  have weightHi : waldHalfRejectingWeight 20 77 20 = 88782204940 := by decide +kernel
  have eqLo := balancedWaldNullRejectionProbabilityAt_eq 20 96 25 (1 / 2)
    (by decide) (by decide)
  have eqHi := balancedWaldNullRejectionProbabilityAt_eq 20 77 20 (1 / 2)
    (by decide) (by decide)
  simp only [Nat.cast_ofNat] at eqLo eqHi
  dsimp only at lower upper
  rw [eqLo, waldProbability_eq_halfWeights 20 96 25 (by decide)] at upper
  rw [eqHi, waldProbability_eq_halfWeights 20 77 20 (by decide)] at lower
  rw [weightLo] at upper
  rw [weightHi] at lower
  norm_num at upper lower
  exact le_antisymm upper lower

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8192 in
private theorem twentyUniformCertificate :
    balancedWaldUniformBound 20 96 25 4 2047 ≤ (103 : ℚ) / 1250 := by
  decide +kernel

/-- The Type I error is at most 8.24% uniformly over the common null rate. -/
theorem balancedWaldTwentyUniform (cutoff p : ℝ) (hlo : (96 : ℝ) / 25 ≤ cutoff)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    balancedWaldNullRejectionProbabilityAt 20 cutoff p ≤ (103 : ℝ) / 1250 := by
  have hcut : ((96 : ℕ) : ℝ) / ((25 : ℕ) : ℝ) ≤ cutoff := by exact_mod_cast hlo
  have hcert :=
    (Rat.cast_le (K := ℝ)).mpr twentyUniformCertificate
  rw [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat] at hcert
  exact (balancedWaldNullRejectionProbabilityAt_le_uniformBound 20 96 25 4 2047 cutoff p
    (by decide) (by decide) hcut hp₀ hp₁).trans hcert

end StatClaim.Examples.WaldBound
