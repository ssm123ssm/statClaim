"""A family with cited members: Lean checks the combination, the members stay assumed."""

import json
import shutil
from pathlib import Path

import pytest

from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.verification import VerificationError, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
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
    assert report["status"] == "conditional", report["diagnostics"]
    family, primary = report["values"]["family"], report["values"]["primary"]
    assert family["status"] == "conditional" and primary["status"] == "verified"
    evidence = family["evidence"]
    assert evidence["grade"] == "conditional" and evidence["machine_checked"] == "composition"
    assert evidence["sources"] == ["lean_proof", "literature"]
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
    assert "Program status: conditional" in text


def test_composition_certificate_replays_and_states_what_it_leaves_assumed(mixed):
    report, _ = mixed
    bundle = Path(report["values"]["family"]["evidence"]["certificate"]["directory"])
    certificate = json.loads((bundle / "certificate.json").read_text())
    assert certificate["kind"] == "statclaim_composition_certificate"
    assert certificate["status"] == "combination_verified_members_assumed"
    assert "hypothesis `marginal`" in (bundle / "Proof.lean").read_text()
    checked = recheck_certificate(bundle, project=ROOT)
    assert checked["certificate_status"] == "combination_verified_members_assumed"


def test_a_cited_member_cannot_be_relabelled_as_proved(mixed, tmp_path):
    report, _ = mixed
    original = Path(report["values"]["family"]["evidence"]["certificate"]["directory"])
    bundle = tmp_path / "forged"
    shutil.copytree(original, bundle)
    text = (bundle / "inputs.json").read_text()
    assert '"grade": "cited"' in text
    (bundle / "inputs.json").write_text(text.replace('"grade": "cited"', '"grade": "proved"'))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


def test_large_sample_members_make_the_family_approximate(tmp_path):
    report = check_source(Source(TWO_MEANS, "means.stat"), project=ROOT, output=tmp_path / "run")
    evidence = report["values"]["family"]["evidence"]
    assert report["status"] == "conditional" and evidence["scope"] == "asymptotic"
    assert any("sum of the slacks" in claim for claim in evidence["established_properties"])


def test_lean_rejects_an_overallocated_composition(tmp_path):
    from fractions import Fraction

    from statclaim.composition import Component, Composition, render_composition_proof

    members = tuple(
        Component(name, Fraction(1, 20), "finite_sample", "cited", "tests.t/t_test version 1", "x")
        for name in ("a", "b")
    )
    with pytest.raises(ValueError, match="exceeds"):
        render_composition_proof(Composition(Fraction(1, 20), members), "0" * 64)
