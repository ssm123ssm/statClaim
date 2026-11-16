"""Planning and policy certificates checked and replayed by the real Lean backend."""

import json
import shutil
from pathlib import Path

import pytest

from statproof.language_runner import check_source
from statproof.language_syntax import Source
from statproof.verification import VerificationError, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [
    pytest.mark.lean,
    pytest.mark.skipif(not shutil.which("lake"), reason="Lean required"),
]


@pytest.fixture(scope="module")
def runs(tmp_path_factory):
    directory = tmp_path_factory.mktemp("planning")
    reports = {}
    for name in (
        "planning",
        "two_stage",
        "two_stage_posterior",
        "one_sample",
        "one_sample_result",
        "confidence_interval",
        "unequal_allocation",
        "two_stage_search",
        "two_stage_result",
        "difference_interval",
        "one_sided",
        "non_inferiority",
    ):
        path = ROOT / f"examples/{name}.stat"
        reports[name] = check_source(
            Source(path.read_text(), str(path)), project=ROOT, output=directory / name
        )
    return reports


def test_planning_example_components(runs):
    report = runs["planning"]
    values = report["values"]
    # The unmet feasibility claim keeps the program unresolved; sizing is verified.
    assert report["status"] == "unresolved_obligation"
    assert values["verification"]["evidence"] is None
    assert values["recommended_size"] == 36
    evidence = values["sizing_evidence"]
    assert "smallest sufficient candidate" in evidence["established_properties"][-1]
    replay = recheck_certificate(Path(evidence["certificate"]["directory"]), project=ROOT)
    assert replay["kind"] == "statproof_planning_certificate"


@pytest.mark.parametrize("name", ["two_stage", "two_stage_posterior", "one_sample"])
def test_policy_certificates_replay(runs, name):
    report = runs[name]
    assert report["values"]["verification"]["status"] == "verified", report["diagnostics"]
    certificate = report["values"]["verification"]["evidence"]["certificate"]
    replay = recheck_certificate(Path(certificate["directory"]), project=ROOT)
    assert replay["kind"] == "statproof_policy_certificate"


def test_one_sample_result_certificate_replays_and_resists_tampering(runs, tmp_path):
    evidence = runs["one_sample_result"]["values"]["verification"]["evidence"]
    source = Path(evidence["certificate"]["directory"])
    assert recheck_certificate(source, project=ROOT)["kind"] == (
        "statproof_binomial_result_certificate"
    )
    bundle = tmp_path / "tampered"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["result"]["p_value"] = "1/1000"
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_interval_certificate_replays_and_rejects_a_narrower_interval(runs, tmp_path):
    evidence = runs["confidence_interval"]["values"]["verification"]["evidence"]
    source = Path(evidence["certificate"]["directory"])
    assert recheck_certificate(source, project=ROOT)["kind"] == (
        "statproof_binomial_interval_certificate"
    )
    bundle = tmp_path / "narrow"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["result"]["lower"] = "3/10"
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_unequal_allocation_is_verified(runs):
    report = runs["unequal_allocation"]
    assert report["status"] == "verified", report["diagnostics"]
    evidence = report["values"]["verification"]["evidence"]
    assert "(26, 52) is the smallest" in evidence["established_properties"][-1]


def test_searched_two_stage_design_is_verified(runs):
    report = runs["two_stage_search"]
    assert report["status"] == "verified", report["diagnostics"]
    claims = report["values"]["verification"]["evidence"]["established_properties"]
    assert "stages 13 and 30" in claims[0]


def test_two_stage_result_certificate_replays_and_resists_tampering(runs, tmp_path):
    report = runs["two_stage_result"]
    assert report["status"] == "verified", report["diagnostics"]
    source = Path(report["values"]["verification"]["evidence"]["certificate"]["directory"])
    assert recheck_certificate(source, project=ROOT)["kind"] == (
        "statproof_two_stage_result_certificate"
    )
    bundle = tmp_path / "tampered"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["result"]["typeI_bound"] = "1/100"
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_difference_interval_certificate_replays_and_rejects_a_narrower_interval(runs, tmp_path):
    report = runs["difference_interval"]
    assert report["status"] == "verified", report["diagnostics"]
    source = Path(report["values"]["verification"]["evidence"]["certificate"]["directory"])
    assert recheck_certificate(source, project=ROOT)["kind"] == (
        "statproof_difference_interval_certificate"
    )
    bundle = tmp_path / "narrow"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["result"]["lower"] = "1/20"
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_one_sided_certificates_replay_and_resist_tampering(runs, tmp_path):
    report = runs["one_sided"]
    assert report["status"] == "verified", report["diagnostics"]
    kinds = {}
    for name in ("guarantee", "sizing", "outcome"):
        directory = Path(report["values"][name]["evidence"]["certificate"]["directory"])
        kinds[name] = recheck_certificate(directory, project=ROOT)["kind"]
    assert kinds == {
        "guarantee": "statproof_design_certificate",
        "sizing": "statproof_planning_certificate",
        "outcome": "statproof_per_result_certificate",
    }
    source = Path(report["values"]["outcome"]["evidence"]["certificate"]["directory"])
    bundle = tmp_path / "tampered"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["result"]["p_value"]["numerator"] += 1
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_margin_certificates_replay_and_resist_tampering(runs, tmp_path):
    report = runs["non_inferiority"]
    assert report["status"] == "verified", report["diagnostics"]
    source = Path(report["values"]["outcome"]["evidence"]["certificate"]["directory"])
    assert recheck_certificate(source, project=ROOT)["kind"] == "statproof_margin_test_certificate"
    bundle = tmp_path / "tampered"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["analysis"]["thresholds"] = [max(0, t - 4) for t in inputs["analysis"]["thresholds"]]
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_ten_endpoint_family_is_verified(tmp_path):
    lines = [
        "use models.two_arm_binomial",
        "use sampling",
        "use tests.fisher",
        "use multiplicity.bonferroni",
        "let study = two_arm_binomial(n_control=40, n_treatment=40)",
        "let null = equal_proportions(model=study)",
    ]
    names = [f"outcome_{index}" for index in range(10)]
    lines += [f"let {n} = fisher(design=fixed(model=study), null=null, alpha=1/200)" for n in names]
    lines.append(
        f"let family = bonferroni(analyses=[{', '.join(names)}], alpha=1/20, "
        'joint_law="binomial_marginals")'
    )
    lines.append("let verification = verify(familywise(family))")
    report = check_source(
        Source("\n".join(lines) + "\n", "ten.stat"), project=ROOT, output=tmp_path / "ten"
    )
    assert report["status"] == "verified", report["diagnostics"]


def test_strengthened_claim_is_rejected(runs, tmp_path):
    source = Path(runs["two_stage"]["values"]["evidence"]["certificate"]["directory"])
    bundle = tmp_path / "tampered"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    inputs["target"]["maximum_typeI"] = "1/25"
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)
