"""Association-test certificates in the real kernel: issue, replay and tampering."""

import json
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.association import NOT_CAUSAL, AssociationTest, association_payload
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.report import run_association
from statclaim.verification import VerificationError, canonical_bytes, digest, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]
CASE_CONTROL = AssociationTest(
    "case_control", Fraction(1, 20), (240, 120), None, "smoking", "glioma"
)
SURVEY = AssociationTest("cross_sectional", Fraction(1, 40), None, 800, "night shifts", "insomnia")


def issue(test, directory):
    bundle = directory / "checked"
    report = run_association(test, stopping="fixed", project=ROOT, output=bundle, timeout=300)
    assert report["status"] == "verified", report.get("verification")
    return report, bundle


@pytest.fixture(scope="module")
def groups(tmp_path_factory):
    return issue(CASE_CONTROL, tmp_path_factory.mktemp("case_control"))


@pytest.fixture(scope="module")
def mixture(tmp_path_factory):
    return issue(SURVEY, tmp_path_factory.mktemp("survey"))


def test_fixed_groups_are_proved_with_fishers_theorem_and_replay(groups):
    report, bundle = groups
    assert report["evidence_grade"] == "proved"
    assert report["limitations"] == [NOT_CAUSAL]
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["kind"] == "statclaim_association_certificate"
    assert certificate["general_theorem"] == "StatClaim.Modules.Association.groups_typeI_le_alpha"
    assert any("cases (120) and controls (240)" in claim for claim in certificate["claims"])
    checked = recheck_certificate(bundle, project=ROOT, timeout=300)
    assert checked["status"] == "verified"
    assert checked["certificate_id"] == report["certificate"]["certificate_id"]


def test_a_random_number_exposed_is_proved_by_averaging_and_replays(mixture):
    report, bundle = mixture
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["general_theorem"] == "StatClaim.Modules.Association.mixture_typeI_le_alpha"
    assert any("averaged over the number exposed" in claim for claim in certificate["claims"])
    assert recheck_certificate(bundle, project=ROOT, timeout=300)["status"] == "verified"


@pytest.mark.parametrize("name", ["inputs.json", "Proof.lean"])
def test_changed_bundle_files_are_detected(groups, tmp_path, name):
    _, original = groups
    bundle = tmp_path / "changed"
    shutil.copytree(original, bundle)
    path = bundle / name
    path.write_text(path.read_text().replace("240", "241"))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT, timeout=300)


def test_a_rehashed_certificate_for_another_design_is_refused(groups, tmp_path):
    _, original = groups
    bundle = tmp_path / "rehashed"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    payload = association_payload(AssociationTest("case_control", Fraction(1, 20), (250, 125)))
    (bundle / "inputs.json").write_text(json.dumps(payload))
    certificate.update(inputs=payload, input_sha256=digest(canonical_bytes(payload)))
    certificate["files_sha256"]["inputs.json"] = digest((bundle / "inputs.json").read_bytes())
    certificate.pop("certificate_id")
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT, timeout=300)


@pytest.mark.parametrize(
    "fixture,before,after",
    [
        ("groups", "firstGroup = 240 ∧", "firstGroup = 241 ∧"),
        ("mixture", "sampleSize = 800 ∧", "sampleSize = 801 ∧"),
    ],
)
def test_the_kernel_rejects_false_statements(request, tmp_path, fixture, before, after):
    _, bundle = request.getfixturevalue(fixture)
    source = (bundle / "Proof.lean").read_text()
    assert before in source
    proof = tmp_path / "False.lean"
    proof.write_text(source.replace(before, after))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0
    assert "STATCLAIM_CHECKED" not in checked.stdout


def test_the_lesson_verifies_every_design(tmp_path):
    path = ROOT / "examples/tutorial/23_observational_studies.stat"
    report = check_source(
        Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "run", timeout=300
    )
    assert report["status"] == "verified"
    assert [request["value"]["status"] for request in report["requests"]] == ["verified"] * 3


def test_a_stronger_claim_than_proved_fails_the_check(mixture, tmp_path):
    """Lean reports the error and exits non-zero, which is what the verifier requires. The
    declaration can still exist, so the audit marker alone would not be enough."""
    _, bundle = mixture
    source = (bundle / "Proof.lean").read_text()
    before = "(Association.mixtureRejection sampleSize declaredLevel.value)"
    assert before in source
    proof = tmp_path / "Stronger.lean"
    proof.write_text(source.replace(before, "(Association.mixtureRejection sampleSize 1)"))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0
    assert "error" in checked.stdout
