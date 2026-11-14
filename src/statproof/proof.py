"""Generate explicit Lean claims from validated numerical inputs.

Only validated integer literals and a computed SHA-256 identifier enter the
template. The generated statement is retained in every certificate bundle.
"""

import re
from fractions import Fraction

from statproof.design import Design
from statproof.fisher import FisherResult

CHECKED_THEOREMS = [
    "checked_counts",
    "checked_support",
    "checked_p_value",
    "checked_table_probability",
    "checked_decision",
    "checked_typeI",
]

DESIGN_CHECKED_THEOREMS = [
    "checked_sizes",
    "checked_stopping",
    "checked_contract",
    "checked_design",
    "checked_typeI",
]


def render_design_proof(design: Design, input_sha256: str) -> str:
    """Check the declared analysis and its general guarantee without observations."""
    if design.stopping != "fixed":
        raise ValueError("A fixed-sample design certificate requires stopping='fixed'.")
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    nc, nt = design.n_control, design.n_treatment
    audit_names = ",\n    ".join(
        f"``StatProofCertificate.{name}" for name in DESIGN_CHECKED_THEOREMS
    )
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical design SHA-256: {input_sha256}
-- No observed counts or numerical test results are supplied.
namespace StatProofCertificate
open StatProof

def declaredSizes : FixedSampleDesign := ⟨{nc}, {nt}, by decide, by decide⟩
noncomputable def declaredModel := Modules.TwoArmBinomial.model declaredSizes
noncomputable def declaredDesign := Core.StudyDesign.fixed declaredModel
noncomputable def declaredAnalysis := Modules.Fisher.analysis declaredSizes declaredDesign

theorem checked_sizes : declaredSizes.nControl = {nc} ∧ declaredSizes.nTreatment = {nt} ∧
    0 < declaredSizes.nControl ∧ 0 < declaredSizes.nTreatment := by decide

theorem checked_stopping : declaredDesign.sampling.kind = Core.SamplingKind.fixedSample := rfl

theorem checked_contract : (Modules.Fisher.module declaredSizes).Requires declaredDesign :=
  ⟨Core.Compatibility.fixed declaredModel⟩

noncomputable def guarantee : Core.TypeIGuarantee declaredAnalysis (1 / 20 : ℝ) :=
  (Modules.Fisher.module declaredSizes).provide declaredDesign checked_contract

theorem checked_design :
    (declaredAnalysis.typeIClaim guarantee.compatibility (1 / 20 : ℝ)).statement :=
  guarantee.certificate.establishes

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw {nc} {nt} p).real (fisherRejectionRegion {nc} {nt}) ≤ (1 / 20 : ℝ) := by
  have bound := checked_design (p, p) rfl
  change (guarantee.compatibility.samplingLaw.law (p, p)).real
    (Modules.Fisher.procedure declaredSizes).rejectionEvent ≤ (1 / 20 : ℝ) at bound
  rw [guarantee.compatibility.agrees,
    Modules.TwoArmBinomial.law_under_null declaredSizes (p, p) rfl,
    Modules.Fisher.rejectionEvent_eq] at bound
  exact bound

end StatProofCertificate

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[{audit_names}] do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {{theoremName}}"
    for dependency in ← collectAxioms theoremName do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {{dependency}} in {{theoremName}}"
  logInfo "STATPROOF_CHECKED {input_sha256}"
"""


def validate_result(design: Design, result: FisherResult) -> None:
    if design.stopping != "fixed":
        raise ValueError("A fixed-sample certificate requires stopping='fixed'.")
    if (result.n_control, result.n_treatment) != (design.n_control, design.n_treatment):
        raise ValueError("Result sample sizes do not match the declared design.")
    for count, size in (
        (result.control_successes, design.n_control),
        (result.treatment_successes, design.n_treatment),
    ):
        if type(count) is not int or not 0 <= count <= size:
            raise ValueError("Success counts must be integers within their declared arm sizes.")
    for value in (result.p_value, result.observed_table_probability):
        if not isinstance(value, Fraction) or not 0 <= value <= 1:
            raise ValueError("Proposed probabilities must be fractions between zero and one.")
    for bound in (result.support_min, result.support_max):
        if type(bound) is not int or bound < 0:
            raise ValueError("Support bounds must be nonnegative integers.")


def render_proof(design: Design, result: FisherResult, input_sha256: str) -> str:
    validate_result(design, result)
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    nc, nt = design.n_control, design.n_treatment
    xc, xt = result.control_successes, result.treatment_successes
    total = xc + xt
    numerator, denominator = result.p_value.as_integer_ratio()
    observed_num, observed_den = result.observed_table_probability.as_integer_ratio()
    truth = "True" if result.reject_null else "False"
    audit_names = ",\n    ".join(f"``StatProofCertificate.{name}" for name in CHECKED_THEOREMS)
    return f"""import StatProof
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- Fixed sample sizes and the declared independent-binomial model are assumed.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatProofCertificate
open StatProof

theorem checked_counts : 0 < {nc} ∧ 0 < {nt} ∧ {xc} ≤ {nc} ∧ {xt} ≤ {nt} := by decide

theorem checked_support (k : ℕ) :
    k ∈ hypergeometricSupport {nc} {nt} {total} ↔
      {result.support_min} ≤ k ∧ k ≤ {result.support_max} := by
  simpa only [show {total} - {nt} = {result.support_min} from by decide,
    show min {nc} {total} = {result.support_max} from by decide] using
    mem_hypergeometricSupport_iff {nc} {nt} {total} k

theorem checked_p_value : hypergeometricPValue {nc} {nt} {total} {xc} =
    ({numerator} : ℚ) / {denominator} := by
  apply hypergeometricPValue_eq_of_cross_product {nc} {nt} {total} {xc}
    {numerator} {denominator} (by decide) (by decide)
  decide +kernel

theorem checked_table_probability : hypergeometricMass {nc} {nt} {total} {xc} =
    ({observed_num} : ℚ) / {observed_den} := by
  apply hypergeometricMass_eq_of_cross_product {nc} {nt} {total} {xc}
    {observed_num} {observed_den} (by decide) (by decide)
  decide +kernel

theorem checked_decision : (({xc}, {xt}) ∈ fisherRejectionRegion {nc} {nt}) ↔ {truth} := by
  simp only [fisherRejectionRegion, Finset.mem_filter, binomialCountSupport,
    Finset.mem_product, Finset.mem_range]
  rw [checked_p_value]
  norm_num [targetAlpha]

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw {nc} {nt} p).real (fisherRejectionRegion {nc} {nt}) ≤ (1 / 20 : ℝ) :=
  fisher_typeI_error_le {nc} {nt} p

end StatProofCertificate

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[{audit_names}] do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {{theoremName}}"
    for dependency in ← collectAxioms theoremName do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {{dependency}} in {{theoremName}}"
  logInfo "STATPROOF_CHECKED {input_sha256}"
"""
