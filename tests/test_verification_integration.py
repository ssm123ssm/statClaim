"""Real Lean checks, selected by `make integration-check` and the Lean CI job."""

import json
import shutil
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.design import Design
from statclaim.fisher import fisher_exact
from statclaim.proof import render_proof
from statclaim.report import verify_design
from statclaim.verification import (
    VerificationError,
    canonical_bytes,
    certify_result,
    digest,
    recheck_certificate,
    result_payload,
)

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]


@pytest.fixture(scope="module")
def issued(tmp_path_factory):
    output = tmp_path_factory.mktemp("certificates") / "demo"
    report = verify_design(
        Design(100, 100, "fixed"),
        control_successes=10,
        treatment_successes=25,
        project=ROOT,
        output=output,
    )
    assert report["status"] == "verified", report.get("verification")
    return report, output


def test_real_demo_is_certified_and_replayable(issued):
    report, bundle = issued
    assert report["certificate_issued"] is True
    assert report["backend_invoked"] is True
    assert report["formal_reference"]["application_to_this_run"] == "verified_result_only"
    assert report["outstanding_obligations"] == []
    assert report["decision"] == "reject_null"
    assert report["evidence"][0]["formally_verified_implementation"] is False
    assert report["evidence"][1]["kind"] == "formal_proof"
    checked = recheck_certificate(bundle, project=ROOT)
    assert checked["status"] == "verified"
    assert checked["certificate_id"] == report["certificate"]["certificate_id"]


@pytest.mark.parametrize("nc,nt,xc,xt", [(1, 19, 0, 19), (4, 4, 2, 2), (4, 4, 0, 0), (4, 4, 4, 4)])
def test_threshold_nonrejection_and_degenerate_results_are_checked(tmp_path, nc, nt, xc, xt):
    result = fisher_exact(
        n_control=nc, n_treatment=nt, control_successes=xc, treatment_successes=xt
    )
    certificate, _ = certify_result(
        Design(nc, nt, "fixed"), result, project=ROOT, output=tmp_path / "checked"
    )
    assert certificate["status"] == "verified_under_assumptions"


@pytest.mark.parametrize(
    "change",
    [
        {"p_value": Fraction(1, 2)},
        {"observed_table_probability": Fraction(1, 2)},
        {"support_min": 1},
    ],
)
def test_lean_rejects_incorrect_python_candidates(tmp_path, change):
    result = fisher_exact(n_control=4, n_treatment=4, control_successes=0, treatment_successes=4)
    target = tmp_path / "bad"
    with pytest.raises(VerificationError) as failure:
        certify_result(
            Design(4, 4, "fixed"), replace(result, **change), project=ROOT, output=target
        )
    assert failure.value.stage == "proof"
    assert not (target / "certificate.json").exists()
    assert (target / "failure.json").is_file()


@pytest.mark.parametrize("name", ["inputs.json", "Proof.lean", "Proof.olean", "transcript.log"])
def test_bundle_file_tampering_is_detected(issued, tmp_path, name):
    _, original = issued
    bundle = tmp_path / "tampered"
    shutil.copytree(original, bundle)
    with (bundle / name).open("ab") as handle:
        handle.write(b"\nchanged\n")
    with pytest.raises(VerificationError, match="was changed"):
        recheck_certificate(bundle, project=ROOT)


def test_recomputed_hashes_cannot_make_a_false_p_value_valid(issued, tmp_path):
    _, original = issued
    bundle = tmp_path / "forged"
    shutil.copytree(original, bundle)
    design = Design(100, 100, "fixed")
    result = fisher_exact(
        n_control=100, n_treatment=100, control_successes=10, treatment_successes=25
    )
    result = replace(result, p_value=Fraction(1, 2))
    payload = result_payload(design, result)
    input_id = digest(canonical_bytes(payload))
    (bundle / "inputs.json").write_text(json.dumps(payload))
    (bundle / "Proof.lean").write_text(render_proof(design, result, input_id))
    certificate = json.loads((bundle / "certificate.json").read_text())
    certificate.pop("certificate_id")
    certificate["inputs"], certificate["input_sha256"] = payload, input_id
    for name in ("inputs.json", "Proof.lean"):
        certificate["files_sha256"][name] = digest((bundle / name).read_bytes())
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))
    with pytest.raises(VerificationError) as failure:
        recheck_certificate(bundle, project=ROOT)
    assert failure.value.stage == "proof"


def test_bundle_change_during_replay_is_rejected(issued, tmp_path, monkeypatch):
    import statclaim.verification as backend

    _, original = issued
    bundle = tmp_path / "changing"
    shutil.copytree(original, bundle)
    original_check = backend._check_proof

    def change_after_check(*args, **kwargs):
        original_check(*args, **kwargs)
        (bundle / "inputs.json").write_text("changed during replay")

    monkeypatch.setattr(backend, "_check_proof", change_after_check)
    with pytest.raises(VerificationError, match="bundle changed during replay"):
        recheck_certificate(bundle, project=ROOT)


def test_failed_final_write_does_not_publish_a_certificate(tmp_path, monkeypatch):
    import statclaim.verification as backend

    original_write = backend._write_json

    def fail_pending_write(path, value):
        if path.name == "certificate.pending.json":
            path.write_text("partial")
            raise OSError("Simulated incomplete write")
        original_write(path, value)

    monkeypatch.setattr(backend, "_write_json", fail_pending_write)
    result = fisher_exact(n_control=4, n_treatment=4, control_successes=0, treatment_successes=4)
    bundle = tmp_path / "incomplete"
    with pytest.raises(VerificationError, match="Simulated incomplete write"):
        certify_result(Design(4, 4, "fixed"), result, project=ROOT, output=bundle)
    assert not (bundle / "certificate.json").exists()
    assert (bundle / "failure.json").is_file()
