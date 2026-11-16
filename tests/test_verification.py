import json
import sys
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
    _check_proof,
    _run,
    certify_result,
    recheck_certificate,
)

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture
def result():
    return fisher_exact(n_control=4, n_treatment=4, control_successes=0, treatment_successes=4)


@pytest.mark.parametrize(
    "change",
    [
        {"control_successes": "0); sorry"},
        {"treatment_successes": True},
        {"n_control": 5},
        {"p_value": 0.5},
        {"p_value": Fraction(-1)},
        {"support_min": "0"},
    ],
)
def test_invalid_values_cannot_enter_generated_lean(result, change):
    with pytest.raises(ValueError):
        render_proof(Design(4, 4, "fixed"), replace(result, **change), "a" * 64)


def test_proof_uses_kernel_arithmetic_and_binds_the_proposed_value(result):
    source = render_proof(Design(4, 4, "fixed"), result, "a" * 64)
    assert "decide +kernel" in source
    assert "native_decide" not in source
    assert "sorry" not in source
    assert "(1 : ℚ) / 35" in source
    assert "checked_typeI" in source
    assert f"STATCLAIM_CHECKED {'a' * 64}" in source


def test_adaptive_design_never_calls_certificate_backend(monkeypatch, tmp_path):
    def forbidden(*args, **kwargs):
        raise AssertionError("Unsupported sampling must not reach the certificate backend.")

    monkeypatch.setattr("statclaim.report.certify_result", forbidden)
    report = verify_design(
        Design(4, 4, "data_dependent"),
        control_successes=0,
        treatment_successes=4,
        project=ROOT,
        output=tmp_path / "unused",
    )
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert report["decision"] is None
    assert report["backend_invoked"] is False
    assert not (tmp_path / "unused").exists()


def test_failed_check_does_not_issue_a_certificate(monkeypatch):
    def failed(*args, **kwargs):
        raise VerificationError("proof", "Proof check failed.")

    monkeypatch.setattr("statclaim.report.certify_result", failed)
    report = verify_design(
        Design(4, 4, "fixed"),
        control_successes=0,
        treatment_successes=4,
        project=ROOT,
    )
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert report["established_properties"] == []
    assert report["formal_reference"]["checked_in_this_run"] is False


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
def test_invalid_time_limits(result, tmp_path, timeout):
    with pytest.raises(ValueError, match="positive, finite"):
        certify_result(
            Design(4, 4, "fixed"), result, project=ROOT, output=tmp_path / "unused", timeout=timeout
        )
    assert not (tmp_path / "unused").exists()


def test_existing_output_is_preserved(result, tmp_path):
    target = tmp_path / "existing"
    target.mkdir()
    (target / "keep.txt").write_text("keep")
    with pytest.raises(FileExistsError):
        certify_result(Design(4, 4, "fixed"), result, project=ROOT, output=target)
    assert (target / "keep.txt").read_text() == "keep"


@pytest.mark.parametrize("data", [None, [], {}, {"certificate_id": "wrong"}])
def test_malformed_certificates_fail_cleanly(tmp_path, data):
    (tmp_path / "certificate.json").write_text(json.dumps(data))
    with pytest.raises(VerificationError):
        recheck_certificate(tmp_path, project=ROOT)
