import StatProof

/-!
Policy-level operating characteristics checked for concrete designs, plus
negative cases: a failing bound must not be provable by the same check.
-/

open StatProof StatProof.Modules

namespace StatProof.Tests.Policies

/-- Simon's optimal two-stage design for 20% versus 40% response. -/
def simon := TwoStageBinomial.thresholdDesign 13 30 3 12

theorem simon_typeI :
    ((TwoStageBinomial.analysis simon (ratPoint 1 5 (by decide) (by decide))).typeIClaim
      ((1 : ℝ) / 20)).statement := by
  have checked := TwoStageBinomial.typeI_of_check simon 1 5 (by decide) (by decide) 1 20
    (by decide) (by decide +kernel)
  simpa using checked

theorem simon_power :
    ((TwoStageBinomial.analysis simon (ratPoint 1 5 (by decide) (by decide))).powerClaim
      (fun rate => rate = ratPoint 2 5 (by decide) (by decide)) ((4 : ℝ) / 5)).statement := by
  have checked := TwoStageBinomial.power_of_check simon (ratPoint 1 5 (by decide) (by decide))
    2 5 (by decide) (by decide) 4 5 (by decide) (by decide +kernel)
  simpa using checked

/-- The same bound holds for every response rate at or below 20%. -/
theorem simon_typeI_composite :
    ((TwoStageBinomial.analysisAtMost simon (ratPoint 1 5 (by decide) (by decide))).typeIClaim
      ((1 : ℝ) / 20)).statement := by
  have checked := TwoStageBinomial.typeI_atMost_of_check simon
    (TwoStageBinomial.thresholdDesign_monotone 13 30 3 12) 1 5 (by decide) (by decide) 1 20
    (by decide) (by decide +kernel)
  simpa using checked

/-- One-sample exact binomial test: 25 patients, reject at 10 or more responses. -/
theorem one_sample_typeI :
    ((OneSampleBinomial.analysis ⟨25, 10⟩ (ratPoint 1 5 (by decide) (by decide))).typeIClaim
      ((1 : ℝ) / 20)).statement := by
  have checked := OneSampleBinomial.typeI_of_check ⟨25, 10⟩ 1 5 (by decide) (by decide) 1 20
    (by decide) (by decide +kernel)
  simpa using checked

/-- The same check refutes a bound the design does not meet. -/
example : ¬ (rejectionNumerator 13 30 1 5 1 5 simon.rejectRule * 25 ≤
    1 * rejectionDenominator 13 30 5 5) := by decide +kernel

/-- Uniform prior; continue when P(rate > 1/5) ≥ 1/2, succeed when ≥ 19/20. -/
def posterior := TwoStageBinomial.posteriorDesign 10 20 1 1 1 5 1 2 19 20

example : posterior.continues 1 = false ∧ posterior.continues 2 = true := by decide +kernel

theorem posterior_typeI :
    ((TwoStageBinomial.analysis posterior (ratPoint 1 5 (by decide) (by decide))).typeIClaim
      ((1 : ℝ) / 10)).statement := by
  have checked := TwoStageBinomial.typeI_of_check posterior 1 5 (by decide) (by decide) 1 10
    (by decide) (by decide +kernel)
  simpa using checked

/-- The posterior design's error bound also holds for every smaller rate. -/
theorem posterior_typeI_composite :
    ((TwoStageBinomial.analysisAtMost posterior (ratPoint 1 5 (by decide) (by decide))).typeIClaim
      ((1 : ℝ) / 10)).statement := by
  have checked := TwoStageBinomial.typeI_atMost_of_check posterior
    (TwoStageBinomial.posteriorDesign_monotone 10 20 1 1 1 5 1 2 19 20) 1 5 (by decide)
    (by decide) 1 10 (by decide) (by decide +kernel)
  simpa using checked

/-- Fisher power at 10% versus 40% with 36 per arm exceeds 4/5. -/
def sizes : FixedSampleDesign := ⟨36, 36, by decide, by decide⟩
def level : SignificanceLevel := ⟨(1 : ℚ) / 20, by norm_num, by norm_num⟩

theorem fisher_power :
    ((FisherPower.analysis sizes level).powerClaim
      (fun parameter => parameter = FisherPower.ratePoint 1 10 2 5
        (by decide) (by decide) (by decide) (by decide)) ((4 : ℝ) / 5)).statement := by
  have checked := FisherPower.power_of_check sizes level 1 20 (by decide)
    (by norm_num [level]) 1 10 2 5 (by decide) (by decide) (by decide) (by decide)
    4 5 (by decide) (by decide +kernel)
  simpa using checked

/-- With 35 per arm the same bound fails. -/
example : ¬ (4 * rejectionDenominator 35 35 10 5 ≤
    rejectionNumerator 35 35 1 10 2 5 (FisherPower.checkedReject 35 35 1 20) * 5) := by
  decide +kernel

end StatProof.Tests.Policies

namespace StatProof.Tests.Minimality
open StatProof StatProof.Modules

/-- No equal-arm size from 2 to 11 reaches 80% Fisher power at 10% versus 40%. -/
example : FisherPower.SmallerFail 1 2 12 1 20 1 10 2 5 4 5 := by decide +kernel

/-- Proposed thresholds are validated, so a wrong one is rejected. -/
example : ¬ FisherPower.HintsValid 2 2 1 20 [0, 0, 6, 0, 0] [0, 0, 0, 0, 0] := by decide +kernel

/-- No one-sample size from 10 to 34 meets both targets; 35 rejects at 12. -/
example : OneSampleBinomial.SmallerFail 10 35 1 5 1 20 1 20 2 5 4 5 := by decide +kernel
example : OneSampleBinomial.criticalValue 35 1 5 1 20 = 12 := by decide +kernel

/-- A too-narrow interval fails the endpoint check: at rate 3/10 the upper
tail for 14 of 35 is above 1/40. -/
example : ¬ (OneSampleBinomial.tailNumerator 35 3 10 14 * 40 ≤ 1 * 10 ^ 35) := by
  decide +kernel

/-- Wrong one-sided bounds are rejected: at total 2 with two per arm, no table
has a one-sided p-value at or below 1/20. -/
example : ¬ FisherOneSided.HintsValid 2 2 1 20 [0, 0, 1, 1, 2] := by decide +kernel

/-- A cell whose corner exceeds the bound fails its check: with one participant
per arm and "reject on a treatment success", the error at control rate 0 and
treatment rate 1/2 is 1/2, above 1/40. -/
example : DifferenceTest.cellCheck 1 1 [1, 1] 2 0 0 1 40 0 1 = false := by decide +kernel

/-- Thresholds must not decrease as control successes increase. -/
example : ¬ DifferenceTest.Increasing 2 2 [2, 1, 3] := by decide

end StatProof.Tests.Minimality
