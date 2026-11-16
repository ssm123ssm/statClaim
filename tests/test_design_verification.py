import json
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.design import Design
from statclaim.proof import render_design_proof
from statclaim.report import verify_design_only
from statclaim.verification import VerificationError, design_payload

ROOT = Path(__file__).resolve().parents[1]


def test_design_payload_and_proof_do_not_require_observations():
    payload = design_payload(Design(100, 100, "fixed"))
    assert payload["scope"] == "design"
    assert "result" not in payload
    assert payload["analysis"]["null"] == "equal_proportions"
    assert payload["analysis"]["alpha"] == "1/20"
    source = render_design_proof(Design(100, 100, "fixed"), "a" * 64)
    assert "Core.StudyDesign.fixed" in source
    assert "Modules.Fisher.module" in source
    assert "checked_contract" in source
    assert "checked_design" in source
    assert "checked_p_value" not in source
    assert "checked_table_probability" not in source


def test_design_verification_never_calculates_a_p_value(monkeypatch):
    def forbidden(*args, **kwargs):
        raise AssertionError("A design-only request must not calculate a p-value.")

    def failed(*args, **kwargs):
        raise VerificationError("proof", "No checked proof was returned.")

    monkeypatch.setattr("statclaim.report.fisher_exact", forbidden)
    monkeypatch.setattr("statclaim.report.certify_design", failed)
    report = verify_design_only(Design(100, 100, "fixed"), project=ROOT)
    assert report["verification_scope"] == "design"
    assert report["certificate_issued"] is False
    assert report["status"] == "unresolved_obligation"
    assert report["established_properties"] == []
    assert "calculation" not in report
    assert "decision" not in report
    assert not any("supplied counts" in item for item in report["required_assumptions"])


def test_adaptive_design_has_missing_justification_without_requiring_data(monkeypatch, tmp_path):
    def forbidden(*args, **kwargs):
        raise AssertionError("The fixed-sample backend must not certify this design.")

    monkeypatch.setattr("statclaim.report.certify_design", forbidden)
    report = verify_design_only(
        Design(100, 100, "data_dependent"), project=ROOT, output=tmp_path / "unused"
    )
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert report["backend_invoked"] is False
    assert "not evidence of inflated error" in report["verification"]["message"]
    assert not (tmp_path / "unused").exists()


def test_design_command_accepts_only_design_inputs(monkeypatch, capsys, tmp_path):
    def backend(design, **options):
        assert design == Design(100, 100, "fixed")
        assert options == {"project": ROOT, "output": tmp_path / "new", "timeout": 12}
        return {"status": "verified", "verification_scope": "design"}

    monkeypatch.setattr("statclaim.cli.verify_design_only", backend)
    code = main(
        [
            "verify-design",
            str(ROOT / "examples/fixed_sample.toml"),
            "--project",
            str(ROOT),
            "--output",
            str(tmp_path / "new"),
            "--timeout",
            "12",
        ]
    )
    assert code == 0
    assert json.loads(capsys.readouterr().out)["verification_scope"] == "design"


def test_design_command_rejects_observation_flags(capsys):
    with pytest.raises(SystemExit) as error:
        main(
            ["verify-design", str(ROOT / "examples/fixed_sample.toml"), "--control-successes", "10"]
        )
    assert error.value.code == 2
    assert "unrecognized arguments" in capsys.readouterr().err


def test_result_verification_has_an_explicit_alias(monkeypatch, capsys):
    monkeypatch.setattr(
        "statclaim.cli.verify_design",
        lambda *args, **kwargs: {"status": "verified", "verification_scope": "result"},
    )
    assert (
        main(
            [
                "verify-result",
                str(ROOT / "examples/fixed_sample.toml"),
                "--control-successes",
                "10",
                "--treatment-successes",
                "25",
            ]
        )
        == 0
    )
    assert json.loads(capsys.readouterr().out)["verification_scope"] == "result"


def test_design_proof_does_not_accept_unsupported_stopping():
    with pytest.raises(ValueError, match="stopping='fixed'"):
        render_design_proof(Design(100, 100, "data_dependent"), "a" * 64)
