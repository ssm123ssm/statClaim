import json
from pathlib import Path

import pytest

from statproof.cli import main
from statproof.design import Design, inspect_design, load_design

ROOT = Path(__file__).resolve().parents[1]


def test_fixed_sample_example_remains_unverified():
    report = inspect_design(load_design(ROOT / "examples/fixed_sample.toml"))
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert report["backend_invoked"] is False
    assert report["evidence"] == []
    assert report["established_properties"] == []


def test_stopping_modification_exposes_missing_justification():
    report = inspect_design(load_design(ROOT / "examples/data_dependent_stopping.toml"))
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert any("separate justification" in item for item in report["outstanding_obligations"])
    assert any(
        "not evidence of inflated error" in item for item in report["outstanding_obligations"]
    )


@pytest.mark.parametrize("value", ["0", "-1", "1.5", "true", '"100"'])
def test_invalid_sample_sizes_are_rejected(tmp_path, value):
    content = (ROOT / "examples/fixed_sample.toml").read_text()
    path = tmp_path / "invalid.toml"
    path.write_text(content.replace("n_control = 100", f"n_control = {value}"))
    with pytest.raises(ValueError, match="positive integer"):
        load_design(path)


@pytest.mark.parametrize(
    "before, after",
    [
        ('stopping = "fixed"', 'stopping = "optional"'),
        ('module = "two_arm_binomial"', 'module = "normal_approximation"'),
        ('stopping = "fixed"', 'stopping = "fixed"\nalpha = 0.10'),
        ("n_control = 100\n", ""),
        ("[design]", "unrecognized = true\n[design]"),
    ],
)
def test_unsupported_or_incomplete_declarations_are_rejected(tmp_path, before, after):
    content = (ROOT / "examples/fixed_sample.toml").read_text()
    path = tmp_path / "invalid.toml"
    path.write_text(content.replace(before, after))
    with pytest.raises(ValueError):
        load_design(path)


def test_cli_does_not_signal_success_for_unresolved_design(capsys):
    assert main(["inspect", str(ROOT / "examples/fixed_sample.toml")]) == 1
    assert json.loads(capsys.readouterr().out)["certificate_issued"] is False


def test_fixed_design_has_no_stopping_obligation():
    report = inspect_design(Design(10, 12, "fixed"))
    assert not any("separate justification" in item for item in report["outstanding_obligations"])
