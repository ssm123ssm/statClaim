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
