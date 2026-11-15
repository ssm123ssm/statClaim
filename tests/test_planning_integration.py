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
    for name in ("planning", "two_stage", "two_stage_posterior", "one_sample"):
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
