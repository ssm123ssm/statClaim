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
    for name in ("fisher", "two_outcomes", "fisher_result", "first_class"):
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


def test_first_class_results_retain_real_evidence_and_reuse_it(language_runs):
    report = language_runs["first_class"]
    values = report["values"]
    assert len(report["requests"]) == 3
    assert values["computation"]["status"] == "calculated"
    assert values["saved_verification"] == values["result_verification"]
    assert values["results"] == [
        values["design_verification"],
        values["computation"],
        values["result_verification"],
    ]
    assert all(value["source_sha256"] == report["source"]["sha256"] for value in values["results"])
    for name, reference in (
        ("design_verification", "fisher"),
        ("result_verification", "fisher_result"),
    ):
        value = values[name]
        assert value["status"] == "verified"
        evidence = value["evidence"]
        assert evidence["claim"] == value["claim"]
        assert evidence["required_assumptions"]
        certificate_path = Path(evidence["certificate"]["file"])
        certificate = json.loads(certificate_path.read_text())
        reference_path = Path(
            language_runs[reference]["requests"][-1]["report"]["certificate"]["file"]
        )
        expected = json.loads(reference_path.read_text())
        assert certificate["input_sha256"] == expected["input_sha256"]
        assert recheck_certificate(certificate_path.parent, project=ROOT)["status"] == "verified"
    directory = Path(report["run_directory"])
    assert json.loads((directory / "run.json").read_text()) == report
    assert not (directory / "request-004").exists()


def test_first_class_family_proof_uses_the_existing_bonferroni_inputs(language_runs, tmp_path):
    path = ROOT / "examples/two_outcomes.stat"
    text = path.read_text().replace(
        "verify familywise(outcomes)",
        "let guarantee = familywise(outcomes)\nlet checked = verify(guarantee)",
    )
    report = check_source(Source(text), project=ROOT, output=tmp_path / "family")
    value = report["values"]["checked"]
    assert value["status"] == "verified"
    actual = json.loads(Path(value["evidence"]["certificate"]["file"]).read_text())
    expected = family_payload(load_family(ROOT / "examples/two_outcomes.toml"))
    assert canonical_bytes(actual["inputs"]) == canonical_bytes(expected)
    bundle = Path(value["evidence"]["certificate"]["directory"])
    assert recheck_certificate(bundle, project=ROOT)["status"] == "verified"


def test_recompiling_edited_source_never_reuses_first_class_evidence(language_runs):
    previous = language_runs["first_class"]
    path = ROOT / "examples/first_class.stat"
    edited = path.read_text().replace("alpha=0.05", "alpha=0.025")
    report = check_source(Source(edited), project=ROOT, elaborate_only=True)
    value = report["values"]["result_verification"]
    assert value["status"] == "not_executed"
    assert value["evidence"] is None
    assert value["source_sha256"] != previous["values"]["result_verification"]["source_sha256"]
    assert previous["values"]["result_verification"]["evidence"] is not None
