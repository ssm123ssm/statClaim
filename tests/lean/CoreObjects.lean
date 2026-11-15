import StatProof

namespace StatProof.Tests.CoreObjects

open Core

def sizes : FixedSampleDesign := ⟨4, 4, by decide, by decide⟩
noncomputable def model := Modules.TwoArmBinomial.model sizes
noncomputable def fixedDesign := StudyDesign.fixed model
noncomputable def analysis := Modules.Fisher.analysis sizes fixedDesign

-- The model has separate unknown probabilities; its null is a restriction.
example : Modules.TwoArmBinomial.equalProportions
    ((⟨0, by norm_num⟩ : unitInterval), (⟨0, by norm_num⟩ : unitInterval)) := by
  rfl
example : ¬ Modules.TwoArmBinomial.equalProportions
    ((⟨0, by norm_num⟩ : unitInterval), (⟨1, by norm_num⟩ : unitInterval)) := by
  norm_num [Modules.TwoArmBinomial.equalProportions]

-- The fixed-law contract is supplied explicitly.
example : (Modules.Fisher.module sizes).Requires fixedDesign :=
  ⟨Compatibility.fixed model⟩

noncomputable def guarantee : TypeIGuarantee analysis (defaultLevel.value : ℝ) :=
  (Modules.Fisher.module sizes).provide fixedDesign ⟨Compatibility.fixed model⟩

example : (analysis.typeIClaim guarantee.compatibility (defaultLevel.value : ℝ)).statement :=
  guarantee.certificate.establishes

def observed : Observation model :=
  Modules.TwoArmBinomial.observe sizes 0 4 (by decide) (by decide)
def candidate : Result analysis := ⟨observed, (1 : ℚ) / 35⟩

theorem candidate_correct : candidate.exactClaim.statement := by
  change (1 / 35 : ℚ) = hypergeometricPValue 4 4 4 0
  symm
  apply hypergeometricPValue_eq_of_cross_product 4 4 4 0 1 35 (by decide) (by decide)
  decide +kernel

theorem valueCertificate : Certificate candidate.exactClaim := ⟨candidate_correct⟩

-- Changing the proposed result requires another proof.
def changedCandidate : Result analysis := ⟨observed, (1 : ℚ) / 2⟩
example : True := by
  fail_if_success
    have invalid : Certificate changedCandidate.exactClaim := valueCertificate
  trivial

-- A point-value certificate does not establish an error-bound claim.
example : True := by
  fail_if_success
    have invalid : Certificate (analysis.typeIClaim guarantee.compatibility (defaultLevel.value : ℝ)) :=
      valueCertificate
  trivial

-- Explicitly assuming a claim does not manufacture a proof or certificate.
def assumedValue : Assessment candidate.exactClaim := .assumed
example : True := by
  fail_if_success
    have invalid := Certificate.establishes assumedValue
  trivial

-- Domain checking rejects invalid observations at their source.
example : True := by
  fail_if_success
    have invalid := Modules.TwoArmBinomial.observe sizes 5 4 (by decide) (Nat.le_refl 4)
  trivial

-- Changing the design does not retain the fixed sampling-law witness.
noncomputable def adaptiveDesign := StudyDesign.unresolvedAdaptive model
example : ¬ Nonempty (Compatibility adaptiveDesign) := no_compatibility_without_law _ rfl
example : True := by
  fail_if_success
    have invalid : Compatibility adaptiveDesign := Compatibility.fixed model
  trivial

-- A supplied law can still violate compatibility. A normalized alternative law
-- is not enough: the provider also needs its equality to the model's law.
noncomputable def swappedLaw : SamplingLaw Modules.TwoArmBinomial.Parameters (ℕ × ℕ) where
  law := fun parameter => Modules.TwoArmBinomial.jointLaw sizes parameter.swap
  probability := fun parameter => Modules.TwoArmBinomial.jointLaw_probability sizes parameter.swap

noncomputable def mismatchedDesign : StudyDesign model where
  sampling := {kind := .fixedSample, inducedLaw := some swappedLaw}

example : True := by
  fail_if_success
    have invalid : Compatibility mismatchedDesign := {
      samplingLaw := swappedLaw, supplied := rfl, agrees := fun _ => rfl }
  trivial

-- Results are tied to the model's outcome domain, including its arm sizes.
def smallerSizes : FixedSampleDesign := ⟨1, 1, by decide, by decide⟩
noncomputable def smallerModel := Modules.TwoArmBinomial.model smallerSizes
example : True := by
  fail_if_success
    have invalid : Observation smallerModel := observed
  trivial

-- The core procedure supports output types beyond rational Fisher p-values.
noncomputable def identityProcedure : Procedure model where
  Output := ℕ × ℕ
  evaluate := id
  reject := fun counts => counts.1 = counts.2
  rejection_measurable := .of_discrete

noncomputable def identityAnalysis : Analysis model where
  design := fixedDesign
  hypothesis := fun _ => True
  procedure := identityProcedure

def identityResult : Result identityAnalysis := ⟨observed, observed.val⟩
example : identityResult.exactClaim.statement := rfl

end StatProof.Tests.CoreObjects

namespace StatProof.Tests.HypothesisContracts

open StatProof.Modules.TwoArmBinomial

example (parameter : Parameters) :
    proportionDifference 0 parameter ↔ equalProportions parameter :=
  proportionDifference_zero_iff parameter

example (parameter : Parameters)
    (h : (parameter.2 : ℝ) < (parameter.1 : ℝ)) :
    proportionDifferenceAtMost 0 parameter ∧ ¬ equalProportions parameter := by
  constructor
  · simpa [proportionDifferenceAtMost] using (sub_nonpos.mpr (le_of_lt h))
  · intro equal
    exact (ne_of_lt h) equal.symm

end StatProof.Tests.HypothesisContracts
