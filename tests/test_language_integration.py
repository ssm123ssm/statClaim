"""Runs whose claims Lean proves in one program certificate, replayed for real."""

import json
import shutil
from pathlib import Path

import pytest

from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.verification import canonical_bytes, digest, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
PROGRAM = "statclaim_program_certificate"
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]


@pytest.fixture(scope="module")
def language_runs(tmp_path_factory):
    directory = tmp_path_factory.mktemp("language")
    reports = {}
    for name in (
        "fisher",
        "two_outcomes",
        "fisher_result",
        "first_class",
        "fields",
        "hypothesis_zero",
    ):
        path = ROOT / (
            "tests/fixtures/fisher.stat" if name == "fisher" else f"examples/{name}.stat"
        )
        report = check_source(
            Source(path.read_text(), str(path)), project=ROOT, output=directory / name
        )
        assert report["status"] == "verified", report.get("diagnostics")
        reports[name] = report
    return reports


@pytest.mark.parametrize("name", ["fisher", "two_outcomes", "fisher_result"])
def test_a_run_binds_its_source_in_one_program_certificate(language_runs, name):
    report = language_runs[name]
    request = report["requests"][-1]
    certificate_path = Path(request["report"]["certificate"]["file"])
    certificate = json.loads(certificate_path.read_text())
    assert certificate["kind"] == PROGRAM
    retained = (Path(report["run_directory"]) / "Source.stat").read_text()
    assert certificate["inputs"]["source"]["text"] == retained
    assert certificate["inputs"]["program"] == report["program"]
    assert certificate["input_sha256"] == digest(canonical_bytes(certificate["inputs"]))
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
    assert "alpha=1/40" in new_certificate["inputs"]["source"]["text"]
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
    files = set()
    for name in ("design_verification", "result_verification"):
        value = values[name]
        assert value["status"] == "verified"
        evidence = value["evidence"]
        assert evidence["claim"] == value["claim"]
        assert evidence["required_assumptions"]
        files.add(evidence["certificate"]["file"])
    (certificate_file,) = files  # both claims are proved in the one program certificate
    assert recheck_certificate(Path(certificate_file).parent, project=ROOT)["status"] == "verified"
    directory = Path(report["run_directory"])
    assert json.loads((directory / "run.json").read_text()) == report
    assert not list(directory.glob("request-*"))


def test_a_family_of_proved_tests_is_proved(language_runs, tmp_path):
    path = ROOT / "examples/two_outcomes.stat"
    text = path.read_text().replace(
        "verify familywise(outcomes)",
        "let guarantee = familywise(outcomes)\nlet checked = verify(guarantee)",
    )
    report = check_source(Source(text), project=ROOT, output=tmp_path / "family")
    value = report["values"]["checked"]
    assert value["status"] == "verified"
    bundle = Path(value["evidence"]["certificate"]["directory"])
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["assumptions"] == []  # no premise: every member is proved
    assert "familywise_of_members" in (bundle / "Proof.lean").read_text()
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


def test_real_verification_fields_match_checked_evidence_and_exact_calculation(language_runs):
    report = language_runs["fields"]
    values = report["values"]
    evidence = values["verification"]["evidence"]
    assert values["status"] == "verified"
    assert values["evidence"] == evidence
    assert values["certificate_file"] == evidence["certificate"]["file"]
    assert values["certificate_hash"] == digest(Path(values["certificate_file"]).read_bytes())
    assert values["checked_assumptions"] == evidence["required_assumptions"]
    assert values["grade"] == evidence["grade"] == "proved"
    assert values["scope"] == evidence["scope"] == "finite_sample"
    assert values["bound"] == evidence["guarantee"]["bound"] == "1/20"
    assert evidence["sources"] == ["lean_proof"] and evidence["machine_checked"] == "guarantee"
    text = render_report(report, Source((ROOT / "examples/fields.stat").read_text()))
    assert "Evidence: proved in Lean; guarantee: finite-sample bound" in text
    assert (
        values["p_value"] == report["requests"][1]["report"]["calculation"]["p_value"]["fraction"]
    )
    assert values["decision"] == "reject_null"
    assert values["declared_alpha"] == "1/20"
    assert values["control_size"] == 100
    assert len(report["requests"]) == 2
    assert (
        recheck_certificate(Path(values["certificate_file"]).parent, project=ROOT)["status"]
        == "verified"
    )


def test_zero_difference_alias_issues_only_the_existing_equality_guarantee(language_runs):
    report = language_runs["hypothesis_zero"]
    value = report["values"]["checked"]
    assert value["status"] == "verified"
    assert value["claim"]["subject"]["null"]["predicate"] == "equal_proportions"
    bundle = Path(value["evidence"]["certificate"]["directory"])
    proof = (bundle / "Proof.lean").read_text()
    # The declared null is Fisher's, which Lean decides: equality of the two proportions.
    assert "∀ parameter, null parameter ↔ analysis.hypothesis parameter" in proof
    assert recheck_certificate(bundle, project=ROOT)["status"] == "verified"
