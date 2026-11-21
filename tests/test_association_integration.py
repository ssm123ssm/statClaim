"""Association-test certificates in the real kernel: issue, replay and tampering."""

import json
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.association import (
    NOT_CAUSAL,
    AssociationResult,
    AssociationTable,
    AssociationTest,
    EffectInterval,
    association_payload,
)
from statclaim.incidence import (
    ObservedEvents,
    ProportionEstimate,
    RateRatioInterval,
    RateResult,
    RateTest,
)
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.matched import MatchedInterval, MatchedPairs, MatchedResult, MatchedTest
from statclaim.report import (
    run_association,
    run_association_result,
    run_effect_interval,
    run_incidence,
    run_matched,
)
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


# Observed tables and effect intervals ------------------------------------------------------
SURVEY_TABLE = AssociationTable(
    "cross_sectional", (40, 160, 30, 370), None, 600, "smoking", "wheeze"
)
CASE_TABLE = AssociationTable(
    "case_control", (90, 140, 60, 160), (300, 150), None, "smoking", "glioma"
)


@pytest.mark.parametrize(
    "table",
    [SURVEY_TABLE, CASE_TABLE],
    ids=["random number exposed", "fixed groups"],
)
def test_an_observed_tables_p_value_and_decision_are_proved_and_replay(table, tmp_path):
    test = AssociationTest(
        table.design, Fraction(1, 20), table.groups, table.n, table.exposure, table.outcome
    )
    result = AssociationResult(test, table)
    report = run_association_result(
        result, verify=True, stopping="fixed", project=ROOT, output=tmp_path / "result", timeout=300
    )
    assert report["status"] == "verified", report.get("verification")
    assert report["decision"] == ("reject_null" if result.fisher.reject_null else "do_not_reject")
    certificate = json.loads((tmp_path / "result/certificate.json").read_text())
    assert certificate["kind"] == "statclaim_association_result_certificate"
    assert "checked_decision" in " ".join(certificate["theorems"])
    assert (
        recheck_certificate(tmp_path / "result", project=ROOT, timeout=300)["status"] == "verified"
    )
    # A flipped decision is a false statement the kernel refuses.
    source = (tmp_path / "result/Proof.lean").read_text()
    truth = "True" if result.fisher.reject_null else "False"
    other = "False" if truth == "True" else "True"
    proof = tmp_path / "Flipped.lean"
    proof.write_text(source.replace(f"↔ {truth} := by", f"↔ {other} := by"))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0


@pytest.mark.parametrize(
    "measure,table",
    [
        ("prevalence_ratio", SURVEY_TABLE),
        ("odds_ratio", CASE_TABLE),
        ("risk_difference", AssociationTable("cohort", (30, 170, 25, 375), (400, 200))),
    ],
)
def test_effect_intervals_are_proved_and_replay(measure, table, tmp_path):
    interval = EffectInterval(measure, table, Fraction(19, 20))
    report = run_effect_interval(
        interval, verify=True, project=ROOT, output=tmp_path / "interval", timeout=300
    )
    assert report["status"] == "verified", report.get("verification")
    certificate = json.loads((tmp_path / "interval/certificate.json").read_text())
    assert certificate["kind"] == "statclaim_effect_interval_certificate"
    expected = (
        "StatClaim.Modules.BinomialInterval.joint_coverage"
        if table.fixed_groups
        else "StatClaim.Modules.Association.mixture_joint_coverage"
    )
    assert certificate["general_theorem"] == expected
    assert (
        recheck_certificate(tmp_path / "interval", project=ROOT, timeout=300)["status"]
        == "verified"
    )


def test_a_narrower_interval_than_proved_is_refused(tmp_path):
    interval = EffectInterval("odds_ratio", CASE_TABLE, Fraction(19, 20))
    report = run_effect_interval(
        interval, verify=True, project=ROOT, output=tmp_path / "interval", timeout=300
    )
    assert report["status"] == "verified"
    source = (tmp_path / "interval/Proof.lean").read_text()
    # Claim a lower end above the proved one: the odds of the cases' lower end, doubled.
    lower_n, lower_d = interval.groups.treatment.lower.as_integer_ratio()
    before = f"Association.odds ((({lower_n} : ℕ) : ℝ) / (({lower_d} : ℕ) : ℝ))"
    assert before in source
    proof = tmp_path / "Narrower.lean"
    proof.write_text(source.replace(before, f"(2 * {before})", 1))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0


# Matched pairs ----------------------------------------------------------------------------
PAIRED = MatchedTest(150, Fraction(1, 20), "smoking", "lung cancer")
OBSERVED_PAIRS = MatchedPairs(150, (40, 35, 15, 60), "smoking", "lung cancer")


@pytest.mark.parametrize(
    "subject",
    [
        PAIRED,
        MatchedResult(PAIRED, OBSERVED_PAIRS),
        MatchedInterval(OBSERVED_PAIRS, Fraction(19, 20)),
        MatchedInterval(MatchedPairs(150, (40, 20, 0, 90)), Fraction(19, 20)),
    ],
    ids=["design", "result", "interval", "unbounded interval"],
)
def test_matched_claims_are_proved_and_replay(subject, tmp_path):
    report = run_matched(
        subject, verify=True, stopping="fixed", project=ROOT, output=tmp_path / "m", timeout=300
    )
    assert report["status"] == "verified", report.get("verification")
    assert report["limitations"] == [NOT_CAUSAL]
    assert recheck_certificate(tmp_path / "m", project=ROOT, timeout=300)["status"] == "verified"


def test_a_flipped_mcnemar_decision_is_refused(tmp_path):
    result = MatchedResult(PAIRED, OBSERVED_PAIRS)
    report = run_matched(
        result, verify=True, stopping="fixed", project=ROOT, output=tmp_path / "m", timeout=300
    )
    assert report["status"] == "verified"
    source = (tmp_path / "m/Proof.lean").read_text()
    assert "↔ True := by" in source
    proof = tmp_path / "Flipped.lean"
    proof.write_text(source.replace("↔ True := by", "↔ False := by"))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0


# Prevalence, cumulative incidence and incidence rates --------------------------------------
NIGHT_SHIFTS = ObservedEvents(48, Fraction(12500), 61, Fraction(31000), "night shifts", "cancer")
RATE_TEST_OBJECT = RateTest(Fraction(1, 20), "night shifts", "cancer")


@pytest.mark.parametrize(
    "subject",
    [
        RATE_TEST_OBJECT,
        RateResult(RATE_TEST_OBJECT, NIGHT_SHIFTS),
        RateRatioInterval(NIGHT_SHIFTS, Fraction(19, 20)),
        ProportionEstimate("prevalence", "cross_sectional", 800, 152, Fraction(19, 20)),
    ],
    ids=["rate test", "rate result", "rate ratio", "prevalence"],
)
def test_incidence_claims_are_proved_and_replay(subject, tmp_path):
    report = run_incidence(
        subject, verify=True, stopping="fixed", project=ROOT, output=tmp_path / "i", timeout=300
    )
    assert report["status"] == "verified", report.get("verification")
    assert recheck_certificate(tmp_path / "i", project=ROOT, timeout=300)["status"] == "verified"


def test_a_flipped_rate_decision_is_refused(tmp_path):
    result = RateResult(RATE_TEST_OBJECT, NIGHT_SHIFTS)
    report = run_incidence(
        result, verify=True, stopping="fixed", project=ROOT, output=tmp_path / "i", timeout=300
    )
    assert report["status"] == "verified"
    source = (tmp_path / "i/Proof.lean").read_text()
    assert "↔ True := by" in source
    proof = tmp_path / "Flipped.lean"
    proof.write_text(source.replace("↔ True := by", "↔ False := by"))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=300
    )
    assert checked.returncode != 0


# Exact power for designs with fixed groups ---------------------------------------------------
@pytest.fixture(scope="module")
def smallest(tmp_path_factory):
    from statclaim.report import planning_report, run_association_search

    test = AssociationTest("case_control", Fraction(1, 20), (100, 50), None, "shifts", "cancer")
    bundle = tmp_path_factory.mktemp("planning") / "checked"
    report = run_association_search(
        planning_report("association_planning", "", []),
        test,
        (Fraction(1, 5), Fraction(3, 7), Fraction(4, 5), Fraction(1, 20)),
        (45, 60),
        minimal=True,
        ratio=2,
        verify=True,
        project=ROOT,
        output=bundle,
        timeout=600,
    )
    assert report["status"] == "verified", report.get("verification")
    return report, bundle


def test_power_and_the_smallest_design_are_proved_and_replay(smallest):
    report, bundle = smallest
    assert report["calculation"]["cases"] == 50
    assert report["limitations"] == [NOT_CAUSAL]
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["kind"] == "statclaim_association_planning_certificate"
    assert certificate["general_theorem"] == "StatClaim.Modules.AssociationPower.power_of_check"
    assert any("No candidate with 45 to 49 cases" in claim for claim in certificate["claims"])
    assert recheck_certificate(bundle, project=ROOT, timeout=600)["status"] == "verified"


@pytest.mark.parametrize(
    "before,after",
    [
        (
            "theorem checked_power :\n    (((4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ))",
            "theorem checked_power :\n    (((81 : ℕ) : ℝ) / ((100 : ℕ) : ℝ))",
        ),
        (
            "AssociationPower.FailsHinted (2 * 49) 49 1 20 1 5 3 7 4 5",
            "AssociationPower.FailsHinted (2 * 49) 49 1 20 1 5 3 7 3 5",
        ),
    ],
    ids=["stronger power", "a smaller candidate that passes"],
)
def test_the_kernel_rejects_false_power_claims(smallest, tmp_path, before, after):
    _, bundle = smallest
    source = (bundle / "Proof.lean").read_text()
    assert before in source
    proof = tmp_path / "False.lean"
    proof.write_text(source.replace(before, after))
    checked = subprocess.run(
        ["lake", "env", "lean", str(proof)], cwd=ROOT, capture_output=True, text=True, timeout=600
    )
    assert checked.returncode != 0
