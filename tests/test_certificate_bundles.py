"""How a certificate is built, audited, bound to its inputs and replayed."""

import json
import shutil
import sys
from pathlib import Path

import pytest

from statclaim.language_syntax import Source
from statclaim.lean_translation import certificate as program
from statclaim.verification import (
    VerificationError,
    _check_proof,
    _run,
    canonical_bytes,
    certify_program,
    digest,
    recheck_certificate,
)

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "examples/fisher_result.stat"


def inputs() -> dict:
    return program.payload(Source(RESULT.read_text(), "examples/fisher_result.stat"))


def test_successful_subprocess_without_audit_marker_is_insufficient(monkeypatch, tmp_path):
    monkeypatch.setattr("statclaim.verification._run", lambda *args: "Build succeeded.\n")
    with pytest.raises(VerificationError, match="audited-proof marker"):
        _check_proof(tmp_path, "a" * 64, ROOT, 10, [], compile_output=False)


def test_subprocess_nonzero_exit_is_failure(tmp_path):
    with pytest.raises(VerificationError, match="exited with code 3"):
        _run([sys.executable, "-c", "raise SystemExit(3)"], tmp_path, 5, [], "proof")


def test_subprocess_timeout_is_failure(tmp_path):
    with pytest.raises(VerificationError, match="timed out"):
        _run([sys.executable, "-c", "import time; time.sleep(30)"], tmp_path, 0.02, [], "proof")


@pytest.mark.parametrize("timeout", [0, -1, float("inf"), float("nan")])
def test_invalid_time_limits(tmp_path, timeout):
    with pytest.raises(ValueError, match="positive, finite"):
        certify_program(inputs(), project=ROOT, output=tmp_path / "unused", timeout=timeout)
    assert not (tmp_path / "unused").exists()


def test_existing_output_is_preserved(tmp_path):
    target = tmp_path / "existing"
    target.mkdir()
    (target / "keep.txt").write_text("keep")
    with pytest.raises(FileExistsError):
        certify_program(inputs(), project=ROOT, output=target)
    assert (target / "keep.txt").read_text() == "keep"


@pytest.mark.parametrize("data", [None, [], {}, {"certificate_id": "wrong"}])
def test_malformed_certificates_fail_cleanly(tmp_path, data):
    (tmp_path / "certificate.json").write_text(json.dumps(data))
    with pytest.raises(VerificationError):
        recheck_certificate(tmp_path, project=ROOT)


def test_a_certificate_of_an_earlier_kind_says_where_it_replays(tmp_path):
    certificate = {"kind": "statclaim_design_certificate", "inputs": {}}
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (tmp_path / "certificate.json").write_text(json.dumps(certificate))
    with pytest.raises(VerificationError, match="StatClaim version that issued them"):
        recheck_certificate(tmp_path, project=ROOT)


@pytest.fixture(scope="module")
def issued(tmp_path_factory):
    bundle = tmp_path_factory.mktemp("certificates") / "result"
    certificate, _ = certify_program(inputs(), project=ROOT, output=bundle, timeout=600)
    return certificate, bundle


@pytest.mark.parametrize("name", ["inputs.json", "Proof.lean", "Proof.olean", "transcript.log"])
@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_bundle_file_tampering_is_detected(issued, tmp_path, name):
    _, original = issued
    bundle = tmp_path / "tampered"
    shutil.copytree(original, bundle)
    with (bundle / name).open("ab") as handle:
        handle.write(b"\nchanged\n")
    with pytest.raises(VerificationError, match="was changed"):
        recheck_certificate(bundle, project=ROOT)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_a_rehashed_proof_of_something_else_does_not_replay(issued, tmp_path):
    """Replay states the claims again from the inputs, so a proof edited to claim less,
    with every hash recomputed, no longer matches them."""
    _, original = issued
    bundle = tmp_path / "forged"
    shutil.copytree(original, bundle)
    proof = (bundle / "Proof.lean").read_text()
    assert "(1 : ℚ) / 20" in proof
    (bundle / "Proof.lean").write_text(proof.replace("(1 : ℚ) / 20", "(1 : ℚ) / 10"))
    certificate = json.loads((bundle / "certificate.json").read_text())
    certificate.pop("certificate_id")
    certificate["files_sha256"]["Proof.lean"] = digest((bundle / "Proof.lean").read_bytes())
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))
    with pytest.raises(VerificationError, match="Proof statements differ"):
        recheck_certificate(bundle, project=ROOT)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_bundle_change_during_replay_is_rejected(issued, tmp_path, monkeypatch):
    import statclaim.verification as backend

    _, original = issued
    bundle = tmp_path / "changing"
    shutil.copytree(original, bundle)
    original_check = backend._check_proof

    def change_after_check(*args, **kwargs):
        output = original_check(*args, **kwargs)
        (bundle / "inputs.json").write_text("changed during replay")
        return output

    monkeypatch.setattr(backend, "_check_proof", change_after_check)
    with pytest.raises(VerificationError, match="bundle changed during replay"):
        recheck_certificate(bundle, project=ROOT)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_failed_final_write_does_not_publish_a_certificate(tmp_path, monkeypatch):
    import statclaim.verification as backend

    original_write = backend._write_json

    def fail_pending_write(path, value):
        if path.name == "certificate.pending.json":
            path.write_text("partial")
            raise OSError("Simulated incomplete write")
        original_write(path, value)

    monkeypatch.setattr(backend, "_write_json", fail_pending_write)
    bundle = tmp_path / "incomplete"
    with pytest.raises(VerificationError, match="Simulated incomplete write"):
        certify_program(inputs(), project=ROOT, output=bundle, timeout=600)
    assert not (bundle / "certificate.json").exists()
    assert (bundle / "failure.json").is_file()
