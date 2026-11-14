"""Real Lean checks of design-level certificates without observations."""

import json
import shutil
from pathlib import Path

import pytest

from statproof.design import Design
from statproof.proof import render_design_proof
from statproof.report import verify_design_only
from statproof.verification import (
    VerificationError,
    canonical_bytes,
    digest,
    recheck_certificate,
)

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]


@pytest.fixture(scope="module")
def issued_design(tmp_path_factory):
    bundle = tmp_path_factory.mktemp("designs") / "checked"
    report = verify_design_only(Design(100, 100, "fixed"), project=ROOT, output=bundle)
    assert report["status"] == "verified", report.get("verification")
    return report, bundle


def test_pre_data_design_certificate_is_replayable(issued_design):
    report, bundle = issued_design
    assert report["verification_scope"] == "design"
    assert report["certificate_issued"] is True
    assert report["formal_reference"]["application_to_this_run"] == "verified_design_only"
    assert "calculation" not in report
    assert "decision" not in report
    assert report["outstanding_obligations"] == []
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["kind"] == "statproof_design_certificate"
    assert "result" not in certificate["inputs"]
    assert certificate["inputs"]["analysis"]["alpha"] == "1/20"
    assert len(certificate["assumptions"]) == 3
    assert "no observed results" in certificate["scope"]
    checked = recheck_certificate(bundle, project=ROOT)
    assert checked["status"] == "verified"
    assert checked["kind"] == "statproof_design_certificate"
    assert checked["claims"] == certificate["claims"]


def _write_changed_certificate(bundle, certificate):
    certificate.pop("certificate_id")
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))


def test_design_certificate_cannot_be_promoted_to_result_evidence(issued_design, tmp_path):
    _, original = issued_design
    bundle = tmp_path / "wrong-scope"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    certificate["claims"].append("The observed p-value is correct.")
    _write_changed_certificate(bundle, certificate)
    with pytest.raises(VerificationError, match="Unsupported certificate field: claims"):
        recheck_certificate(bundle, project=ROOT)


def test_changed_design_requires_matching_lean_statements(issued_design, tmp_path):
    _, original = issued_design
    bundle = tmp_path / "changed-input"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    payload = certificate["inputs"]
    payload["design"]["n_control"] = 200
    (bundle / "inputs.json").write_text(json.dumps(payload))
    certificate["input_sha256"] = digest(canonical_bytes(payload))
    certificate["files_sha256"]["inputs.json"] = digest((bundle / "inputs.json").read_bytes())
    _write_changed_certificate(bundle, certificate)
    with pytest.raises(VerificationError, match="Proof statements differ"):
        recheck_certificate(bundle, project=ROOT)


def test_changed_bound_is_rejected_by_statement_binding(issued_design, tmp_path):
    _, original = issued_design
    bundle = tmp_path / "false-bound"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    source = render_design_proof(Design(100, 100, "fixed"), certificate["input_sha256"])
    # Even with a self-consistent file manifest, unbound statements are rejected.
    (bundle / "Proof.lean").write_text(source.replace("1 / 20", "1 / 100"))
    certificate["files_sha256"]["Proof.lean"] = digest((bundle / "Proof.lean").read_bytes())
    _write_changed_certificate(bundle, certificate)
    with pytest.raises(VerificationError, match="Proof statements differ"):
        recheck_certificate(bundle, project=ROOT)
