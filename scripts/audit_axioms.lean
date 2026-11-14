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
    ``StatProof.fisher_typeI_error_le]
  for theoremName in checked do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {theoremName}"
    let dependencies ← collectAxioms theoremName
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {dependency} in {theoremName}"
    logInfo m!"Checked {theoremName}: {dependencies}"
