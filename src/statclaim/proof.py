"""Generate explicit Lean claims from validated numerical inputs.

Only validated integer literals and a computed SHA-256 identifier enter the
template. The generated statement is retained in every certificate bundle.
"""

import re
from fractions import Fraction

from statclaim.design import Design
from statclaim.fisher import FisherResult, validate_alpha
from statclaim.lean_translation import statements as S
from statclaim.lean_translation.statements import CERTIFICATE as C
from statclaim.planning import _audit, _lean_list, fisher_bounds

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

ONE_SIDED_DESIGN_THEOREMS = ["checked_sizes", "checked_region", "checked_sections", "checked_typeI"]
ONE_SIDED_RESULT_THEOREMS = [
    "checked_counts",
    "checked_p_value",
    "checked_decision",
    "checked_region",
    "checked_sections",
    "checked_typeI",
]


def _one_sided_preamble(design: Design) -> str:
    """Declarations and the Type I theorem shared by one-sided certificates."""
    nc, nt = design.n_control, design.n_treatment
    an, ad = design.alpha.as_integer_ratio()
    return f"""def declaredSizes : FixedSampleDesign := ⟨{nc}, {nt}, by decide, by decide⟩
def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩
noncomputable def declaredAnalysis := FisherOneSided.analysis declaredSizes declaredLevel
def bounds : List ℕ := {_lean_list(fisher_bounds(nc, nt, design.alpha))}

theorem checked_region : FisherOneSided.HintsValid declaredSizes.nControl
    declaredSizes.nTreatment {an} {ad} bounds := by
  decide +kernel

theorem checked_sections : FisherOneSided.HintSections declaredSizes.nControl
    declaredSizes.nTreatment bounds := by
  decide +kernel

{S.analysis_typeI("declaredAnalysis", "(declaredLevel.value : ℝ)").header()} :=
  FisherOneSided.typeI_of_hints declaredSizes declaredLevel {an} {ad} (by decide)
    (by norm_num [declaredLevel]) bounds checked_region checked_sections"""


def _render_one_sided_design_proof(design: Design, input_sha256: str) -> str:
    nc, nt = design.n_control, design.n_treatment
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical design SHA-256: {input_sha256}
-- No observed counts are supplied. The listed bounds are validated by the kernel.
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

{_one_sided_preamble(design)}

theorem checked_sizes : declaredSizes.nControl = {nc} ∧ declaredSizes.nTreatment = {nt} ∧
    0 < declaredSizes.nControl ∧ 0 < declaredSizes.nTreatment := by decide

end StatClaimCertificate
{_audit(ONE_SIDED_DESIGN_THEOREMS, input_sha256)}"""


def _render_one_sided_result_proof(design: Design, result: FisherResult, input_sha256: str) -> str:
    nc, nt = design.n_control, design.n_treatment
    an, ad = design.alpha.as_integer_ratio()
    xc, xt = result.control_successes, result.treatment_successes
    numerator, denominator = result.p_value.as_integer_ratio()
    truth = "True" if result.reject_null else "False"
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- The proposed p-value is confirmed by the kernel against the formal definition.
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace StatClaimCertificate
open StatClaim StatClaim.Modules

{_one_sided_preamble(design)}

{S.counts(nc, nt, xc, xt).header()} := by decide

{S.one_sided_p_value(C, nc, nt, xc + xt, xc, (numerator, denominator)).header()} := by
  apply FisherOneSided.lowerPValue_eq_of_cross_product {nc} {nt} {xc + xt} {xc}
    {numerator} {denominator} (by decide) (by decide)
  decide +kernel

{S.one_sided_decision(C, nc, nt, xc + xt, xc, (an, ad), truth).header()} := by
  rw [checked_p_value]
  norm_num

end StatClaimCertificate
{_audit(ONE_SIDED_RESULT_THEOREMS, input_sha256)}"""


def render_design_proof(design: Design, input_sha256: str) -> str:
    """Check the declared analysis and its general guarantee without observations."""
    if design.stopping != "fixed":
        raise ValueError("A fixed-sample design certificate requires stopping='fixed'.")
    if design.alternative == "greater":
        return _render_one_sided_design_proof(design, input_sha256)
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    nc, nt = design.n_control, design.n_treatment
    an, ad = design.alpha.as_integer_ratio()
    audit_names = ",\n    ".join(
        f"``StatClaimCertificate.{name}" for name in DESIGN_CHECKED_THEOREMS
    )
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical design SHA-256: {input_sha256}
-- No observed counts or numerical test results are supplied.
namespace StatClaimCertificate
open StatClaim

def declaredSizes : FixedSampleDesign := ⟨{nc}, {nt}, by decide, by decide⟩
def declaredLevel : SignificanceLevel :=
  ⟨({an} : ℚ) / {ad}, by norm_num, by norm_num⟩
noncomputable def declaredModel := Modules.TwoArmBinomial.model declaredSizes
noncomputable def declaredDesign := Core.StudyDesign.fixed declaredModel
noncomputable def declaredAnalysis :=
  Modules.Fisher.analysis declaredSizes declaredDesign declaredLevel

theorem checked_sizes : declaredSizes.nControl = {nc} ∧ declaredSizes.nTreatment = {nt} ∧
    0 < declaredSizes.nControl ∧ 0 < declaredSizes.nTreatment := by decide

theorem checked_stopping : declaredDesign.sampling.kind = Core.SamplingKind.fixedSample := rfl

theorem checked_contract :
    (Modules.Fisher.module declaredSizes declaredLevel).Requires declaredDesign :=
  ⟨Core.Compatibility.fixed declaredModel⟩

noncomputable def guarantee : Core.TypeIGuarantee declaredAnalysis (declaredLevel.value : ℝ) :=
  (Modules.Fisher.module declaredSizes declaredLevel).provide declaredDesign checked_contract

theorem checked_design :
    (declaredAnalysis.typeIClaim guarantee.compatibility (declaredLevel.value : ℝ)).statement :=
  guarantee.certificate.establishes

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw {nc} {nt} p).real (fisherRejectionRegionAt {nc} {nt} (( {an} : ℚ) / {ad})) ≤
      (({an} : ℝ) / {ad}) := by
  have bound := checked_design (p, p) rfl
  change (guarantee.compatibility.samplingLaw.law (p, p)).real
    (Modules.Fisher.procedure declaredSizes declaredLevel).rejectionEvent ≤
    (declaredLevel.value : ℝ) at bound
  rw [guarantee.compatibility.agrees,
    Modules.TwoArmBinomial.law_under_null declaredSizes (p, p) rfl,
    Modules.Fisher.rejectionEvent_eq declaredSizes declaredLevel] at bound
  convert bound using 1 <;> norm_num [declaredLevel, declaredSizes]

end StatClaimCertificate

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
  logInfo "STATCLAIM_CHECKED {input_sha256}"
"""


def validate_result(design: Design, result: FisherResult) -> None:
    if design.stopping != "fixed":
        raise ValueError("A fixed-sample certificate requires stopping='fixed'.")
    if (result.n_control, result.n_treatment) != (design.n_control, design.n_treatment):
        raise ValueError("Result sample sizes do not match the declared design.")
    validate_alpha(result.alpha)
    if result.alpha != design.alpha:
        raise ValueError("Result alpha does not match the declared analysis.")
    if result.alternative != design.alternative:
        raise ValueError("Result alternative does not match the declared analysis.")
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
    if design.alternative == "greater":
        return _render_one_sided_result_proof(design, result, input_sha256)
    nc, nt = design.n_control, design.n_treatment
    an, ad = design.alpha.as_integer_ratio()
    xc, xt = result.control_successes, result.treatment_successes
    total = xc + xt
    numerator, denominator = result.p_value.as_integer_ratio()
    observed_num, observed_den = result.observed_table_probability.as_integer_ratio()
    truth = "True" if result.reject_null else "False"
    audit_names = ",\n    ".join(f"``StatClaimCertificate.{name}" for name in CHECKED_THEOREMS)
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical input SHA-256: {input_sha256}
-- Fixed sample sizes and the declared independent-binomial model are assumed.
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace StatClaimCertificate
open StatClaim

{S.counts(nc, nt, xc, xt).header()} := by decide

{S.support(C, nc, nt, total, result.support_min, result.support_max).header()} := by
  simpa only [show {total} - {nt} = {result.support_min} from by decide,
    show min {nc} {total} = {result.support_max} from by decide] using
    mem_hypergeometricSupport_iff {nc} {nt} {total} k

{S.p_value(C, nc, nt, total, xc, (numerator, denominator)).header()} := by
  apply hypergeometricPValue_eq_of_cross_product {nc} {nt} {total} {xc}
    {numerator} {denominator} (by decide) (by decide)
  decide +kernel

{S.table_probability(C, nc, nt, total, xc, (observed_num, observed_den)).header()} := by
  apply hypergeometricMass_eq_of_cross_product {nc} {nt} {total} {xc}
    {observed_num} {observed_den} (by decide) (by decide)
  decide +kernel

{S.fisher_decision(C, nc, nt, xc, xt, (an, ad), truth).header()} := by
  simp only [fisherRejectionRegionAt, Finset.mem_filter, binomialCountSupport,
    Finset.mem_product, Finset.mem_range]
  rw [checked_p_value]
  norm_num

{S.fisher_typeI(C, nc, nt, (an, ad)).header()} :=
  by
    have bound := fisher_typeI_error_le_alpha {nc} {nt} p (({an} : ℚ) / {ad}) (by norm_num)
    convert bound using 1 <;> norm_num

end StatClaimCertificate

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
  logInfo "STATCLAIM_CHECKED {input_sha256}"
"""
