"""Combinations checked in Lean as part of the whole program; members may stay assumed."""

import json
import shutil
from pathlib import Path

import pytest

from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.verification import VerificationError, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
PROGRAM = "statclaim_program_certificate"
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]
TWO_MEANS = """use models.two_arm_continuous
use sampling
use tests.t
use multiplicity.bonferroni
let study = two_arm_continuous(n_control=60, n_treatment=60)
let plan = fixed(model=study)
let null = equal_means(model=study)
let first = t_test(design=plan, null=null, alpha=1/40)
let second = welch_test(design=plan, null=null, alpha=1/40)
let family = verify(familywise(bonferroni(analyses=[first, second], alpha=1/20)))
"""


@pytest.fixture(scope="module")
def mixed(tmp_path_factory):
    path = ROOT / "examples/mixed_endpoints.stat"
    source = Source(path.read_text(), str(path))
    report = check_source(source, project=ROOT, output=tmp_path_factory.mktemp("mixed") / "run")
    return report, source


def test_mixed_family_is_conditional_and_its_fisher_member_is_verified(mixed):
    report, source = mixed
    # The family's own status is conditional, but one member is a cited test,
    # so the file as a whole is no stronger than cited.
    assert report["status"] == "cited", report["diagnostics"]
    assert report["requests"][0]["weakest_link"] == {"grade": "cited", "parts": ["symptoms"]}
    family, primary = report["values"]["family"], report["values"]["primary"]
    assert family["status"] == "conditional" and primary["status"] == "verified"
    evidence = family["evidence"]
    assert evidence["grade"] == "conditional" and evidence["machine_checked"] == "composition"
    assert evidence["sources"] == ["lean_proof", "member_guarantees"]
    assert evidence["scope"] == "finite_sample" and evidence["guarantee"]["bound"] == "1/20"
    ids = [item["id"] for item in evidence["assumptions"]]
    assert ids[:3] == [
        "prespecified_family",
        "member_guarantee:response",
        "member_guarantee:symptoms",
    ]
    assert "normal_outcomes" in ids and evidence["references"]
    text = render_report(report, source)
    assert "conditional [family]" in text and "verified [primary]" in text
    assert "Program status: cited" in text
    assert "Weakest part: cited from the literature; not machine-checked (symptoms)" in text


def test_the_combination_is_certified_with_its_members_premises_listed(mixed):
    report, _ = mixed
    bundle = Path(report["values"]["family"]["evidence"]["certificate"]["directory"])
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["kind"] == PROGRAM
    assert certificate["status"] == "program_checked_under_premises"
    # The cited member's level is a premise the combination rests on.
    assert certificate["assumptions"] == ["cited_symptoms_level"]
    # The combination is proved by the semantics' soundness theorem, from that premise.
    proof = (bundle / "Proof.lean").read_text()
    assert "theorem claim_0 : program.Claim 0 :=" in proof
    assert "StatClaim.Semantics.Program.sound program contracts 0" in proof
    checked = recheck_certificate(bundle, project=ROOT)
    assert checked["certificate_status"] == "program_checked_under_premises"


def test_a_cited_member_cannot_be_relabelled_as_proved(mixed, tmp_path):
    from statclaim.verification import canonical_bytes, digest

    report, _ = mixed
    original = Path(report["values"]["family"]["evidence"]["certificate"]["directory"])
    bundle = tmp_path / "forged"
    shutil.copytree(original, bundle)
    certificate = json.loads((bundle / "certificate.json").read_text())
    certificate.pop("certificate_id")
    claims = certificate["claims"]
    assert "familywise(endpoints), line 26: conditional" in claims
    certificate["claims"] = [c.replace(": conditional", ": proved") for c in claims]
    certificate["certificate_id"] = digest(canonical_bytes(certificate))
    (bundle / "certificate.json").write_text(json.dumps(certificate))
    # The grades are what the program's premises give; a relabelled one does not replay.
    with pytest.raises(VerificationError, match="claims"):
        recheck_certificate(bundle, project=ROOT)


def test_large_sample_members_make_the_family_approximate(tmp_path):
    report = check_source(Source(TWO_MEANS, "means.stat"), project=ROOT, output=tmp_path / "run")
    evidence = report["values"]["family"]["evidence"]
    assert report["status"] == "cited" and evidence["scope"] == "asymptotic"
    assert any("sum of the slacks" in claim for claim in evidence["established_properties"])


def test_interim_look_design_gets_a_conditional_overall_error_bound(tmp_path):
    path = ROOT / "examples/interim_look.stat"
    report = check_source(
        Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "run"
    )
    value = report["values"]["overall"]
    assert value["status"] == "conditional"
    assert value["evidence"]["guarantee"]["quantity"] == "type_I_error"
    bundle = Path(value["evidence"]["certificate"]["directory"])
    # Lean's contracts decide that the looks ask one question at growing sizes, and the
    # soundness theorem proves the union bound over them.
    proof = (bundle / "Proof.lean").read_text()
    assert '.typeI (.looks "trial"' in proof
    assert "theorem contracts : program.Contracts := by decide +kernel" in proof
    assert "StatClaim.Semantics.Program.sound program contracts 0" in proof
    assert recheck_certificate(bundle, project=ROOT)["status"] == "verified"


def test_confirmatory_trial_with_looks_and_a_fixed_sequence(tmp_path):
    path = ROOT / "examples/confirmatory_trial.stat"
    report = check_source(
        Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "run"
    )
    values = report["values"]
    assert [values[name]["status"] for name in ("overall", "primary", "exact_secondary")] == [
        "conditional",
        "conditional",
        "verified",
    ]
    assert report["status"] == "cited"
    bundle = Path(values["overall"]["evidence"]["certificate"]["directory"])
    proof = (bundle / "Proof.lean").read_text()
    assert ".familywise (.sequence" in proof and ".looks" in proof
    assert "StatClaim.Semantics.Program.sound program contracts" in proof
    assert recheck_certificate(bundle, project=ROOT)["status"] == "verified"


def test_a_sequence_whose_levels_were_altered_does_not_replay(tmp_path):
    path = ROOT / "examples/confirmatory_trial.stat"
    report = check_source(
        Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "run"
    )
    original = Path(report["values"]["overall"]["evidence"]["certificate"]["directory"])
    bundle = tmp_path / "forged"
    shutil.copytree(original, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["source"]["text"] = inputs["source"]["text"].replace("alpha=1/20", "alpha=1/10", 1)
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_recycling_graph_gating_a_sequence(tmp_path):
    path = ROOT / "examples/recycling.stat"
    report = check_source(
        Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "run"
    )
    values = report["values"]
    assert values["primary_error"]["status"] == "cited"
    assert values["overall_error"]["status"] == "conditional"
    assert report["status"] == "cited"  # the weakest status in the file
    bundle = Path(values["overall_error"]["evidence"]["certificate"]["directory"])
    certificate = json.loads((bundle / "certificate.json").read_text())
    # The graph's cited rule and the exact member's level are premises.
    assert "cited_primary_rule" in certificate["assumptions"]
    assert any(name.startswith("member_onset") for name in certificate["assumptions"])
    assert recheck_certificate(bundle, project=ROOT)["status"] == "verified"


def test_declared_member_in_a_proved_combination_makes_the_file_declared(tmp_path):
    path = ROOT / "examples/declared_test.stat"
    source = Source(path.read_text(), str(path))
    report = check_source(source, project=ROOT, output=tmp_path / "run")
    values = report["values"]
    assert values["family"]["status"] == "conditional"  # the combination itself is proved
    assert values["alone"]["status"] == "declared"
    assert report["status"] == "declared"
    assert report["requests"][0]["weakest_link"] == {"grade": "declared", "parts": ["pain"]}
    bundle = Path(values["family"]["evidence"]["certificate"]["directory"])
    assumptions = json.loads((bundle / "certificate.json").read_text())["assumptions"]
    assert any(name.startswith("declared_") for name in assumptions)
    assert "Weakest part: declared by the author" in render_report(report, source)
