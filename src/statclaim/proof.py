"""Generate explicit Lean claims from validated numerical inputs.

Only validated integer literals and a computed SHA-256 identifier enter the
template. The generated statement is retained in every certificate bundle.
"""

import re
from fractions import Fraction

from statclaim.design import Design
from statclaim.family import FisherFamily
from statclaim.fisher import FisherResult, validate_alpha
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

theorem checked_typeI :
    (declaredAnalysis.typeIClaim (declaredLevel.value : ℝ)).statement :=
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

theorem checked_counts : 0 < {nc} ∧ 0 < {nt} ∧ {xc} ≤ {nc} ∧ {xt} ≤ {nt} := by decide

theorem checked_p_value : FisherOneSided.lowerPValue {nc} {nt} {xc + xt} {xc} =
    ({numerator} : ℚ) / {denominator} := by
  apply FisherOneSided.lowerPValue_eq_of_cross_product {nc} {nt} {xc + xt} {xc}
    {numerator} {denominator} (by decide) (by decide)
  decide +kernel

theorem checked_decision :
    (FisherOneSided.lowerPValue {nc} {nt} {xc + xt} {xc} ≤ ({an} : ℚ) / {ad}) ↔ {truth} := by
  rw [checked_p_value]
  norm_num

end StatClaimCertificate
{_audit(ONE_SIDED_RESULT_THEOREMS, input_sha256)}"""


FAMILY_CHECKED_THEOREMS = [
    "checked_sizes",
    "checked_allocation",
    "checked_marginals",
    "checked_family",
]


def render_family_proof(family: FisherFamily, input_sha256: str) -> str:
    if not family.supported:
        raise ValueError("A Fisher family certificate requires fixed sampling for every analysis.")
    if family.allocated_alpha > family.alpha:
        raise ValueError("The allocated alpha exceeds the requested familywise bound.")
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    count = len(family.endpoints)
    sizes, levels = [], []
    for endpoint in family.endpoints:
        design = endpoint.design
        numerator, denominator = design.alpha.as_integer_ratio()
        sizes.append(f"⟨{design.n_control}, {design.n_treatment}, by decide, by decide⟩")
        levels.append(f"⟨({numerator} : ℚ) / {denominator}, by norm_num, by norm_num⟩")
    numerator, denominator = family.alpha.as_integer_ratio()
    separator = ",\n    "
    names = ", ".join(f"``StatClaimCertificate.{name}" for name in FAMILY_CHECKED_THEOREMS)
    return f"""import StatClaim
import Lean.Util.CollectAxioms

-- Canonical family SHA-256: {input_sha256}
-- The theorem is conditional on the explicitly quantified marginal-law contract.
namespace StatClaimCertificate
open StatClaim
open Modules.FisherFamilyN

def designs : Fin {count} → FixedSampleDesign :=
  ![{separator.join(sizes)}]
def levels : Fin {count} → SignificanceLevel :=
  ![{separator.join(levels)}]
def familyLevel : ℚ := ({numerator} : ℚ) / {denominator}

theorem checked_sizes (i : Fin {count}) :
    0 < (designs i).nControl ∧ 0 < (designs i).nTreatment :=
  ⟨(designs i).controlPositive, (designs i).treatmentPositive⟩

theorem checked_allocation : ∑ i, (levels i).value ≤ familyLevel := by
  norm_num [Fin.sum_univ_succ, levels, familyLevel]

theorem checked_marginals (law : Core.SamplingLaw (Parameters {count}) (Outcomes {count}))
    (matching : MarginalContract designs law) :
    (family designs levels law).marginalBounds :=
  marginal_bounds designs levels law matching

theorem checked_family (law : Core.SamplingLaw (Parameters {count}) (Outcomes {count}))
    (matching : MarginalContract designs law) :
    ((family designs levels law).familywiseClaim (familyLevel : ℝ)).statement :=
  strong_control designs levels familyLevel checked_allocation law matching

end StatClaimCertificate

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[{names}] do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {{theoremName}}"
    for dependency in ← collectAxioms theoremName do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {{dependency}} in {{theoremName}}"
  logInfo "STATCLAIM_CHECKED {input_sha256}"
"""


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

theorem checked_decision :
    (({xc}, {xt}) ∈ fisherRejectionRegionAt {nc} {nt} (({an} : ℚ) / {ad})) ↔ {truth} := by
  simp only [fisherRejectionRegionAt, Finset.mem_filter, binomialCountSupport,
    Finset.mem_product, Finset.mem_range]
  rw [checked_p_value]
  norm_num

theorem checked_typeI (p : unitInterval) :
    (fisherNullLaw {nc} {nt} p).real (fisherRejectionRegionAt {nc} {nt} (( {an} : ℚ) / {ad})) ≤
      (({an} : ℝ) / {ad}) :=
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
