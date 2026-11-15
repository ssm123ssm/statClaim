import StatProof

namespace StatProof.Examples.MultipleTesting

open Core Modules MeasureTheory

def sizes : FixedSampleDesign := ⟨200, 100, by decide, by decide⟩
def endpointLevel : SignificanceLevel := ⟨1 / 40, by norm_num, by norm_num⟩
def familyLevel : SignificanceLevel := ⟨1 / 20, by norm_num, by norm_num⟩

-- This example supplies independent endpoints. The composition theorem itself
-- also accepts dependent endpoint laws when their marginal contracts are proved.
noncomputable def samplingLaw : SamplingLaw FisherFamily.Parameters FisherFamily.Outcomes where
  law := fun parameter => (TwoArmBinomial.jointLaw sizes parameter.1).prod
    (TwoArmBinomial.jointLaw sizes parameter.2)
  probability := fun _ => by infer_instance

theorem matching_marginals : FisherFamily.MarginalContract sizes sizes samplingLaw := by
  intro parameter
  constructor
  · simp [samplingLaw, Measure.map_fst_prod, TwoArmBinomial.model]
  · simp [samplingLaw, Measure.map_snd_prod, TwoArmBinomial.model]

theorem allocation : (endpointLevel.value : ℝ) + (endpointLevel.value : ℝ) ≤
    (familyLevel.value : ℝ) := by
  norm_num [endpointLevel, familyLevel]

noncomputable def family := FisherFamily.family sizes sizes endpointLevel endpointLevel samplingLaw

noncomputable def guarantee : Bonferroni.FamilywiseGuarantee family (familyLevel.value : ℝ) :=
  (FisherFamily.module sizes sizes endpointLevel endpointLevel (familyLevel.value : ℝ)).provide
    samplingLaw ⟨matching_marginals, allocation⟩

-- For every joint parameter, probability of any rejection of a true null ≤ 5%.
-- Neither null is asserted true; this includes mixed true/false configurations.
#check guarantee.certificate.establishes

-- The provider's actual requirement fails for two 5% allocations and a 5%
-- family budget, despite the matching marginals already being available.
example : ¬ (FisherFamily.module sizes sizes defaultLevel defaultLevel
    (familyLevel.value : ℝ)).Requires samplingLaw := by
  intro requirement
  have allocation := requirement.2
  norm_num [defaultLevel, targetAlpha, familyLevel] at allocation

end StatProof.Examples.MultipleTesting
