"""Semantic equivalence with existing declarations and real certificate replay."""

import json
import shutil
from pathlib import Path

import pytest

from statproof.design import load_design
from statproof.family import load_family
from statproof.fisher import fisher_exact
from statproof.language_runner import check_source
from statproof.language_syntax import Source
from statproof.verification import (
    canonical_bytes,
    design_payload,
    digest,
    family_payload,
    recheck_certificate,
    result_payload,
)

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]


@pytest.fixture(scope="module")
def language_runs(tmp_path_factory):
    directory = tmp_path_factory.mktemp("language")
    reports = {}
    for name in ("fisher", "two_outcomes", "fisher_result"):
        path = ROOT / f"examples/{name}.stat"
        report = check_source(
            Source(path.read_text(), str(path)), project=ROOT, output=directory / name
        )
        assert report["status"] == "verified", report.get("diagnostics")
        reports[name] = report
    return reports


@pytest.mark.parametrize("name", ["fisher", "two_outcomes", "fisher_result"])
def test_language_produces_the_same_bound_inputs_as_existing_interface(language_runs, name):
    report = language_runs[name]
    request = report["requests"][-1]
    certificate_path = Path(request["report"]["certificate"]["file"])
    certificate = json.loads(certificate_path.read_text())
    if name == "fisher":
        expected = design_payload(load_design(ROOT / "examples/fixed_sample.toml"))
    elif name == "two_outcomes":
        expected = family_payload(load_family(ROOT / "examples/two_outcomes.toml"))
    else:
        design = load_design(ROOT / "examples/fixed_sample.toml")
        result = fisher_exact(
            n_control=100, n_treatment=100, control_successes=10, treatment_successes=25
        )
        expected = result_payload(design, result)
    assert canonical_bytes(certificate["inputs"]) == canonical_bytes(expected)
    assert certificate["input_sha256"] == digest(canonical_bytes(expected))
    assert recheck_certificate(certificate_path.parent, project=ROOT)["status"] == "verified"


def test_result_calculation_and_verification_remain_distinct(language_runs):
    first, second = language_runs["fisher_result"]["requests"]
    assert first["status"] == "calculated"
    assert first["report"]["certificate_issued"] is False
    assert first["report"]["backend_invoked"] is False
    assert second["status"] == "verified"
    assert second["report"]["certificate_issued"] is True
    assert first["report"]["calculation"] == second["report"]["calculation"]


def test_retained_source_and_receipt_match_checked_program(language_runs):
    report = language_runs["two_outcomes"]
    directory = Path(report["run_directory"])
    assert digest((directory / "Source.stat").read_bytes()) == report["source"]["sha256"]
    receipt = json.loads((directory / "run.json").read_text())
    assert receipt == report
    assert receipt["program"]["requests"][0]["claim"]["subject"]["alpha"] == "1/20"
    assert len(receipt["program"]["bindings"]) == 6


def test_editing_alpha_requires_new_evidence_and_retains_old_snapshot(language_runs, tmp_path):
    original_report = language_runs["fisher"]
    original_bundle = Path(original_report["requests"][0]["report"]["certificate"]["directory"])
    old_source = Path(original_report["run_directory"]) / "Source.stat"
    changed = old_source.read_text().replace("alpha=1/20", "alpha=1/40")
    edited = check_source(Source(changed, "edited.stat"), project=ROOT, output=tmp_path / "new")
    assert edited["status"] == "verified"
    new_bundle = Path(edited["requests"][0]["report"]["certificate"]["directory"])
    old_certificate = json.loads((original_bundle / "certificate.json").read_text())
    new_certificate = json.loads((new_bundle / "certificate.json").read_text())
    assert old_certificate["input_sha256"] != new_certificate["input_sha256"]
    assert new_certificate["inputs"]["analysis"]["alpha"] == "1/40"
    assert original_report["source"]["sha256"] != edited["source"]["sha256"]
    assert recheck_certificate(original_bundle, project=ROOT)["status"] == "verified"
