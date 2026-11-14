import json
from pathlib import Path

import pytest

from statproof.cli import main
from statproof.design import Design
from statproof.report import test_design as run_design_test

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize(
    "control,treatment,decision", [(10, 25, "reject_null"), (10, 10, "do_not_reject_null")]
)
def test_cli_fixed_sample_computation(control, treatment, decision, capsys):
    code = main(
        [
            "test",
            str(ROOT / "examples/fixed_sample.toml"),
            "--control-successes",
            str(control),
            "--treatment-successes",
            str(treatment),
        ]
    )
    report = json.loads(capsys.readouterr().out)
    assert code == 0  # Completed computation, independent of rejection.
    assert report["decision"] == decision
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert report["backend_invoked"] is False
    assert report["established_properties"] == []
    assert report["evidence"][0]["kind"] == "exact_computation"
    assert report["evidence"][0]["formally_verified_implementation"] is False


def test_adaptive_stopping_does_not_receive_fixed_sample_decision(capsys):
    code = main(
        [
            "test",
            str(ROOT / "examples/data_dependent_stopping.toml"),
            "--control-successes",
            "10",
            "--treatment-successes",
            "25",
        ]
    )
    report = json.loads(capsys.readouterr().out)
    assert code == 1
    assert report["calculation"]["p_value_le_alpha"] is True
    assert report["decision"] is None
    assert report["certificate_issued"] is False
    assert "separate justification" in report["decision_scope"]


@pytest.mark.parametrize("control,treatment", [(101, 20), (-1, 20), (10, 101)])
def test_cli_rejects_out_of_range_data(control, treatment, capsys):
    with pytest.raises(SystemExit) as error:
        main(
            [
                "test",
                str(ROOT / "examples/fixed_sample.toml"),
                "--control-successes",
                str(control),
                "--treatment-successes",
                str(treatment),
            ]
        )
    assert error.value.code == 2
    output = capsys.readouterr()
    assert output.out == ""
    assert "must be an integer between" in output.err


def test_api_report_can_be_serialized_without_losing_exact_value():
    report = run_design_test(Design(10, 14, "fixed"), control_successes=1, treatment_successes=11)
    decoded = json.loads(json.dumps(report))
    p_value = decoded["calculation"]["p_value"]
    assert (p_value["numerator"], p_value["denominator"]) == (41, 14858)


@pytest.mark.parametrize("args", [(0, 10, "fixed"), (10, True, "fixed"), (10, 10, "unknown")])
def test_design_api_validates_direct_construction(args):
    with pytest.raises(ValueError):
        Design(*args)


def test_verify_command_withholds_adaptive_certificate(capsys, tmp_path):
    code = main(
        [
            "verify",
            str(ROOT / "examples/data_dependent_stopping.toml"),
            "--control-successes",
            "10",
            "--treatment-successes",
            "25",
            "--output",
            str(tmp_path / "unused"),
        ]
    )
    report = json.loads(capsys.readouterr().out)
    assert code == 1
    assert report["certificate_issued"] is False
    assert report["backend_invoked"] is False
    assert not (tmp_path / "unused").exists()


def test_check_certificate_command_handles_missing_bundle(capsys, tmp_path):
    code = main(["check-certificate", str(tmp_path / "missing")])
    report = json.loads(capsys.readouterr().out)
    assert code == 1
    assert report["status"] == "unresolved_obligation"


def test_verify_command_maps_backend_options(monkeypatch, capsys, tmp_path):
    def backend(design, **options):
        assert design == Design(100, 100, "fixed")
        assert options == {
            "control_successes": 10,
            "treatment_successes": 25,
            "project": ROOT,
            "output": tmp_path / "new",
            "timeout": 12.0,
        }
        return {"status": "verified", "certificate_issued": True}

    monkeypatch.setattr("statproof.cli.verify_design", backend)
    assert (
        main(
            [
                "verify",
                str(ROOT / "examples/fixed_sample.toml"),
                "--control-successes",
                "10",
                "--treatment-successes",
                "25",
                "--project",
                str(ROOT),
                "--output",
                str(tmp_path / "new"),
                "--timeout",
                "12",
            ]
        )
        == 0
    )
    assert json.loads(capsys.readouterr().out)["status"] == "verified"
