"""Randomisation-test certificates in the real kernel: issue, replay and tampering."""

import json
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.randomisation import RandomisationTest, randomisation_payload
from statclaim.report import run_randomisation
from statclaim.verification import VerificationError, canonical_bytes, digest, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]
CLUSTERS = RandomisationTest(12, 6, Fraction(1, 20), "cluster", "two_arm_continuous", 120, 120)


@pytest.fixture(scope="module")
def issued(tmp_path_factory):
    bundle = tmp_path_factory.mktemp("randomisation") / "checked"
    report = run_randomisation(CLUSTERS, stopping="fixed", project=ROOT, output=bundle, timeout=300)
    assert report["status"] == "verified", report.get("verification")
    return report, bundle


def test_the_certificate_proves_the_bound_and_replays(issued):
    report, bundle = issued
    assert report["evidence_grade"] == "proved"
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["kind"] == "statclaim_randomisation_certificate"
    assert certificate["general_theorem"] == "StatClaim.Modules.Randomisation.typeI"
    assert certificate["inputs"]["analysis"]["splits"] == "924"
    assert any("12 clusters, 6 treated" in claim for claim in certificate["claims"])
    checked = recheck_certificate(bundle, project=ROOT, timeout=300)
    assert checked["status"] == "verified"
    assert checked["certificate_id"] == report["certificate"]["certificate_id"]


@pytest.mark.parametrize("name", ["inputs.json", "Proof.lean"])
def test_changed_bundle_files_are_detected(issued, tmp_path, name):
    _, original = issued
    bundle = tmp_path / "changed"
    shutil.copytree(original, bundle)
    path = bundle / name
    path.write_text(path.read_text().replace("924", "925"))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT, timeout=300)


def test_a_rehashed_certificate_for_other_inputs_is_refused(issued, tmp_path):
    _, original = issued
    bundle = tmp_path / "rehashed"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    # A consistent payload for another design, with every hash recomputed: the proof file
    # no longer matches what those inputs would generate.
    payload = randomisation_payload(
        RandomisationTest(14, 7, Fraction(1, 20), "cluster", "two_arm_continuous", 140, 140)
    )
    (bundle / "inputs.json").write_text(json.dumps(payload))
    certificate.update(inputs=payload, input_sha256=digest(canonical_bytes(payload)))
    certificate["files_sha256"]["inputs.json"] = digest((bundle / "inputs.json").read_bytes())
    certificate.pop("certificate_id")
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT, timeout=300)


@pytest.mark.parametrize(
    "before,after",
    [
        ("card = 924", "card = 925"),  # the wrong number of splits
        ("(1 : ℚ) / 924 ≤", "(1 : ℚ) / 10 ≤"),  # a level the test cannot reach
        ("treatedUnits = 6 ∧", "treatedUnits = 7 ∧"),
    ],
)
def test_the_kernel_rejects_false_statements(issued, tmp_path, before, after):
    _, bundle = issued
    source = (bundle / "Proof.lean").read_text()
    assert before in source
    proof = tmp_path / "False.lean"
    proof.write_text(source.replace(before, after))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0
    assert "STATCLAIM_CHECKED" not in checked.stdout


def test_the_example_verifies_both_claims(tmp_path):
    path = ROOT / "examples/randomisation.stat"
    report = check_source(
        Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "run", timeout=300
    )
    assert report["status"] == "verified"
    assert [request["value"]["status"] for request in report["requests"]] == [
        "verified",
        "verified",
    ]
    assert report["values"]["grade"] == "proved"


BLOCKED = RandomisationTest(
    48,
    24,
    Fraction(1, 20),
    "participant",
    "two_arm_continuous",
    24,
    24,
    "blocked",
    ((10, 10), (14, 14)),
    4,
)


@pytest.fixture(scope="module")
def grouped(tmp_path_factory):
    bundle = tmp_path_factory.mktemp("blocked") / "checked"
    report = run_randomisation(BLOCKED, stopping="fixed", project=ROOT, output=bundle, timeout=300)
    assert report["status"] == "verified", report.get("verification")
    return report, bundle


def test_a_blocked_design_within_strata_is_proved_and_replays(grouped):
    report, bundle = grouped
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["general_theorem"] == (
        "StatClaim.Modules.Randomisation.groupedTypeI_of_level"
    )
    assert certificate["inputs"]["analysis"]["splits"] == str(6**12)
    assert certificate["assumptions"][0].startswith("Within each stratum or block")
    assert recheck_certificate(bundle, project=ROOT, timeout=300)["status"] == "verified"


@pytest.mark.parametrize(
    "before,after",
    [
        (f"card = {6**12}", f"card = {6**12 + 1}"),
        ("(4, 2), (4, 2)]", "(4, 2), (4, 3)]"),  # one block with a different allocation
    ],
)
def test_the_kernel_rejects_false_grouped_statements(grouped, tmp_path, before, after):
    _, bundle = grouped
    source = (bundle / "Proof.lean").read_text()
    assert before in source
    proof = tmp_path / "FalseGrouped.lean"
    proof.write_text(source.replace(before, after))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0
    assert "STATCLAIM_CHECKED" not in checked.stdout
