"""Planning claims, results and intervals checked in Lean and replayed."""

import json
import shutil
from pathlib import Path

import pytest

from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.verification import VerificationError, recheck_certificate

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


PROGRAM = "statclaim_program_certificate"


def bundle_of(report: dict, name: str) -> Path:
    return Path(report["values"][name]["evidence"]["certificate"]["directory"])


def refuses_tampering(source: Path, tmp_path: Path, old: str, new: str) -> None:
    """A copy whose inputs say something else no longer replays."""
    bundle = tmp_path / "tampered"
    shutil.copytree(source, bundle)
    inputs = json.loads((bundle / "inputs.json").read_text())
    assert old in inputs["source"]["text"]
    inputs["source"]["text"] = inputs["source"]["text"].replace(old, new, 1)
    (bundle / "inputs.json").write_text(json.dumps(inputs))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_planning_example_components(runs):
    report = runs["planning"]
    values = report["values"]
    # The unmet feasibility claim keeps the program unresolved; sizing is verified.
    assert report["status"] == "unresolved_obligation"
    assert values["verification"]["evidence"] is None
    assert values["recommended_size"] == 36
    evidence = values["sizing_evidence"]
    assert "no smaller design meets the targets" in " ".join(evidence["established_properties"])
    replay = recheck_certificate(Path(evidence["certificate"]["directory"]), project=ROOT)
    assert replay["kind"] == PROGRAM


@pytest.mark.parametrize("name", ["two_stage", "two_stage_posterior", "one_sample"])
def test_policy_claims_are_proved_and_replay(runs, name):
    report = runs[name]
    assert report["values"]["verification"]["status"] == "verified", report["diagnostics"]
    assert recheck_certificate(bundle_of(report, "verification"), project=ROOT)["kind"] == PROGRAM


def test_one_sample_result_replays_and_resists_tampering(runs, tmp_path):
    report = runs["one_sample_result"]
    source = bundle_of(report, "verification")
    assert recheck_certificate(source, project=ROOT)["kind"] == PROGRAM
    parts = " ".join(report["values"]["verification"]["evidence"]["established_properties"])
    assert "the p-value reported" in parts and "the critical value" in parts
    refuses_tampering(source, tmp_path, "count=", "count=1")


def test_interval_replays_and_resists_tampering(runs, tmp_path):
    report = runs["confidence_interval"]
    source = bundle_of(report, "verification")
    assert recheck_certificate(source, project=ROOT)["kind"] == PROGRAM
    assert "the interval reported" in " ".join(
        report["values"]["verification"]["evidence"]["established_properties"]
    )
    refuses_tampering(source, tmp_path, "level=", "level=1")


def test_unequal_allocation_is_verified(runs):
    report = runs["unequal_allocation"]
    assert report["status"] == "verified", report["diagnostics"]
    claims = report["values"]["verification"]["evidence"]["established_properties"]
    assert "1:2 allocation" in claims[0]
    assert "no smaller design meets the targets" in claims[1]


def test_searched_two_stage_design_is_verified(runs):
    report = runs["two_stage_search"]
    assert report["status"] == "verified", report["diagnostics"]
    claims = report["values"]["verification"]["evidence"]["established_properties"]
    assert "two-stage design with at most 45 participants" in claims[0]


def test_two_stage_result_replays_and_resists_tampering(runs, tmp_path):
    report = runs["two_stage_result"]
    assert report["status"] == "verified", report["diagnostics"]
    source = bundle_of(report, "verification")
    assert recheck_certificate(source, project=ROOT)["kind"] == PROGRAM
    refuses_tampering(source, tmp_path, "stage1_responses=", "stage1_responses=1")


def test_difference_interval_replays_and_resists_tampering(runs, tmp_path):
    report = runs["difference_interval"]
    assert report["status"] == "verified", report["diagnostics"]
    source = bundle_of(report, "verification")
    assert recheck_certificate(source, project=ROOT)["kind"] == PROGRAM
    refuses_tampering(source, tmp_path, "level=", "level=1")


def test_one_sided_claims_share_one_certificate(runs, tmp_path):
    report = runs["one_sided"]
    assert report["status"] == "verified", report["diagnostics"]
    bundles = {bundle_of(report, name) for name in ("guarantee", "sizing", "outcome")}
    assert len(bundles) == 1, "one Lean build for the whole program"
    (source,) = bundles
    assert recheck_certificate(source, project=ROOT)["kind"] == PROGRAM
    refuses_tampering(source, tmp_path, "alpha=", "alpha=1")


def test_margin_test_replays_and_resists_tampering(runs, tmp_path):
    report = runs["non_inferiority"]
    assert report["status"] == "verified", report["diagnostics"]
    source = bundle_of(report, "outcome")
    assert recheck_certificate(source, project=ROOT)["kind"] == PROGRAM
    refuses_tampering(source, tmp_path, "value=", "value=1")


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
    report = runs["two_stage"]
    refuses_tampering(
        bundle_of(report, "verification"), tmp_path, "maximum_typeI=", "maximum_typeI=1"
    )
