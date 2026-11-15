import StatProof
import Lean.Util.CollectAxioms

-- Check transitive dependencies of the milestone theorems, including imports.
-- Unexpected assumptions cause this command, and therefore CI, to fail.
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let checked := #[
    ``StatProof.probabilityOrdered_rejection_mass_le,
    ``StatProof.hypergeometricMass_sum_one,
    ``StatProof.hypergeometricPValue_eq_weight_ratio,
    ``StatProof.hypergeometric_rejection_mass_le_targetAlpha,
    ``StatProof.independentBinomialMass_conditional,
    ``StatProof.fisherNullRejectionProbability_le_targetAlpha,
    ``StatProof.fisherNullLaw_real_support,
    ``StatProof.hypergeometricPValue_eq_of_cross_product,
    ``StatProof.hypergeometricMass_eq_of_cross_product,
    ``StatProof.Core.no_compatibility_without_law,
    ``StatProof.Modules.TwoArmBinomial.law_under_null,
    ``StatProof.Modules.TwoArmBinomial.proportionDifference_zero_iff,
    ``StatProof.Modules.Fisher.rejectionEvent_eq,
    ``StatProof.Modules.Fisher.typeI_statement,
    ``StatProof.Modules.Fisher.adaptive_requirement_missing,
    ``StatProof.fisher_typeI_error_le,
    ``StatProof.fisherNullRejectionProbability_le_alpha,
    ``StatProof.fisher_typeI_error_le_alpha,
    ``StatProof.Modules.Bonferroni.strong_control,
    ``StatProof.Modules.FisherFamily.marginal_bound,
    ``StatProof.Modules.FisherFamily.marginal_bounds,
    ``StatProof.Modules.FisherFamily.strong_control,
    ``StatProof.productBinomial_real_eq_sum,
    ``StatProof.productBinomial_real_ratPoint,
    ``StatProof.Core.Policy.law_real_apply,
    ``StatProof.Core.TypeIGuarantee.toPolicy,
    ``StatProof.Modules.TwoStageBinomial.rejection_probability,
    ``StatProof.Modules.TwoStageBinomial.typeI_of_check,
    ``StatProof.Modules.TwoStageBinomial.power_of_check,
    ``StatProof.Modules.FisherPower.checkedReject_iff,
    ``StatProof.Modules.FisherPower.rejection_probability,
    ``StatProof.Modules.FisherPower.power_of_check,
    ``StatProof.Modules.FisherPower.typeI_statement,
    ``StatProof.binomialExpectation_mono,
    ``StatProof.binomial_real_mono,
    ``StatProof.productBinomial_real_mono,
    ``StatProof.Modules.OneSampleBinomial.typeI_of_check,
    ``StatProof.Modules.OneSampleBinomial.power_of_check,
    ``StatProof.Modules.TwoStageBinomial.typeI_atMost_of_check,
    ``StatProof.Modules.TwoStageBinomial.thresholdDesign_monotone,
    ``StatProof.Modules.FisherPower.rejectionNumerator_hint,
    ``StatProof.Modules.FisherPower.power_lt_of_smallerFail,
    ``StatProof.Modules.FisherPower.smallerFail_of_hinted,
    ``StatProof.Modules.OneSampleBinomial.fails_of_smallerFail,
    ``StatProof.Modules.FisherFamilyN.strong_control,
    ``StatProof.Modules.OneSampleBinomial.pValue_eq_of_cross_product,
    ``StatProof.Modules.BinomialInterval.coverage,
    ``StatProof.Modules.BinomialInterval.interval_contains,
    ``StatProof.Modules.TwoStageBinomial.posteriorDesign_monotone]
  for theoremName in checked do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {dependency} in {theoremName}"
    logInfo m!"Checked {theoremName}: {dependencies}"
