import json
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.design import Design
from statclaim.report import test_design as run_design_test

ROOT = Path(__file__).resolve().parents[1]


def test_api_report_can_be_serialized_without_losing_exact_value():
    report = run_design_test(Design(10, 14, "fixed"), control_successes=1, treatment_successes=11)
    decoded = json.loads(json.dumps(report))
    p_value = decoded["calculation"]["p_value"]
    assert (p_value["numerator"], p_value["denominator"]) == (41, 14858)


@pytest.mark.parametrize("args", [(0, 10, "fixed"), (10, True, "fixed"), (10, 10, "unknown")])
def test_design_api_validates_direct_construction(args):
    with pytest.raises(ValueError):
        Design(*args)


def test_check_certificate_command_handles_missing_bundle(capsys, tmp_path):
    code = main(["check-certificate", str(tmp_path / "missing")])
    report = json.loads(capsys.readouterr().out)
    assert code == 1
    assert report["status"] == "unresolved_obligation"


def test_doctor_outside_a_checkout_never_runs_lean(tmp_path, capsys, monkeypatch):
    """Outside a checkout, running lake could start a toolchain download."""
    import subprocess

    real = subprocess.run

    def only_uv(command, *args, **kwargs):
        assert "lake" not in command[0], "doctor ran lake outside a checkout"
        return real(command, *args, **kwargs)

    monkeypatch.setattr(subprocess, "run", only_uv)
    assert main(["doctor", "--project", str(tmp_path)]) == 1
    out = capsys.readouterr().out
    assert "is not a StatClaim checkout" in out and "make setup" in out
    assert "Ready without Lean" in out


def test_doctor_in_a_checkout_without_lake_says_it_is_missing(capsys, monkeypatch):
    import shutil

    monkeypatch.setattr(shutil, "which", lambda name: None)
    assert main(["doctor", "--project", str(ROOT)]) == 1
    out = capsys.readouterr().out
    assert "Lean: MISSING" in out and "uv: not found" in out


@pytest.mark.parametrize("path", sorted((ROOT / "examples").rglob("*.stat")), ids=lambda p: p.stem)
def test_report_renders_every_example_without_lean(path, capsys):
    """statclaim report needs no Lean and must work on every example."""
    code = main(["report", str(path)])
    out = capsys.readouterr().out
    assert code in (0, 1, 2), out  # 2: the example is invalid on purpose
    assert out.startswith("# Study contract report")
