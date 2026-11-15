"""Check configurable levels, composition, and false candidates in the real kernel."""

import json
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statproof.design import Design
from statproof.family import load_family
from statproof.report import verify_design, verify_design_only, verify_family
from statproof.verification import VerificationError, canonical_bytes, digest, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]


@pytest.fixture(scope="module")
def family_certificate(tmp_path_factory):
    bundle = tmp_path_factory.mktemp("family") / "checked"
    report = verify_family(
        load_family(ROOT / "examples/two_outcomes.toml"), project=ROOT, output=bundle
    )
    assert report["status"] == "verified", report.get("verification")
    return report, bundle


def test_strong_family_certificate_replays_without_observations(family_certificate):
    report, bundle = family_certificate
    assert report["verification_scope"] == "family"
    assert "calculation" not in report and "decision" not in report
    assert report["formal_reference"]["application_to_this_run"] == "verified_family_only"
    assert report["outstanding_obligations"] == []
    assert any(
        "dependence between outcomes is unrestricted" in a for a in report["required_assumptions"]
    )
    checked = recheck_certificate(bundle, project=ROOT)
    assert checked["kind"] == "statproof_family_certificate"
    assert checked["status"] == "verified"
    assert checked["certificate_id"] == report["certificate"]["certificate_id"]


@pytest.mark.parametrize("alpha", [Fraction(0), Fraction(1), Fraction(1, 40)])
def test_design_certificate_supports_boundary_and_nondefault_levels(tmp_path, alpha):
    report = verify_design_only(
        Design(4, 4, "fixed", alpha), project=ROOT, output=tmp_path / "checked"
    )
    assert report["status"] == "verified", report.get("verification")
    certificate = json.loads(Path(report["certificate"]["file"]).read_text())
    assert certificate["inputs"]["analysis"]["alpha"] == str(alpha)
    assert any(f"at most {alpha}" in claim for claim in certificate["claims"])


@pytest.mark.parametrize("alpha,reject", [(Fraction(1, 40), False), (Fraction(1, 35), True)])
def test_result_decision_is_checked_at_declared_level(tmp_path, alpha, reject):
    report = verify_design(
        Design(4, 4, "fixed", alpha),
        control_successes=0,
        treatment_successes=4,
        project=ROOT,
        output=tmp_path / "checked",
    )
    assert report["status"] == "verified", report.get("verification")
    assert report["calculation"]["p_value_le_alpha"] is reject
    assert report["calculation"]["alpha"]["fraction"] == str(alpha)
    assert recheck_certificate(tmp_path / "checked", project=ROOT)["status"] == "verified"


@pytest.mark.parametrize(
    "before,after",
    [
        ("(1 : ℚ) / 40", "(1 : ℚ) / 20"),
        ("(1 : ℚ) / 20", "(1 : ℚ) / 100"),
    ],
)
def test_kernel_rejects_false_family_allocation(family_certificate, tmp_path, before, after):
    _, bundle = family_certificate
    source = (bundle / "Proof.lean").read_text()
    assert before in source
    proof = tmp_path / "FalseFamily.lean"
    proof.write_text(source.replace(before, after))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=120
    )
    assert checked.returncode != 0
    assert "STATPROOF_CHECKED" not in checked.stdout


@pytest.mark.parametrize("change", ["alpha", "joint_law", "claims"])
def test_rehashed_family_metadata_cannot_change_proved_scope(family_certificate, tmp_path, change):
    _, original = family_certificate
    bundle = tmp_path / "changed"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    if change == "claims":
        certificate["claims"].append("Observed results and power are certified.")
    else:
        payload = certificate["inputs"]
        payload[change] = "1/100" if change == "alpha" else "independent_endpoints"
        (bundle / "inputs.json").write_text(json.dumps(payload))
        certificate["input_sha256"] = digest(canonical_bytes(payload))
        certificate["files_sha256"]["inputs.json"] = digest((bundle / "inputs.json").read_bytes())
    certificate.pop("certificate_id")
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)
