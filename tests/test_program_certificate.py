"""The compatibility certificate of a whole program (`statclaim report --lean`)."""

import json
import shutil
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.contract_reports import lean_markdown
from statclaim.language_syntax import Source
from statclaim.lean_translation import certificate
from statclaim.verification import (
    PROGRAM_KIND,
    VerificationError,
    _profile,
    _proof_for_payload,
    canonical_bytes,
    certify_program,
    digest,
    recheck_certificate,
)

ROOT = Path(__file__).resolve().parents[1]
MIXED = ROOT / "examples/mixed_endpoints.stat"


def inputs(path: Path = MIXED) -> dict:
    return certificate.payload(Source(path.read_text(), str(path.relative_to(ROOT))))


def test_the_proof_is_the_translation_then_an_audit_bound_to_the_inputs():
    payload = inputs()
    input_id = digest(canonical_bytes(payload))
    proof = _proof_for_payload(PROGRAM_KIND, payload)
    assert proof.startswith("import StatClaim\n")
    assert f'logInfo "STATCLAIM_CHECKED {input_id}"' in proof
    # Every contract fact, every claim and the program theorem are audited.
    for name in ("response_contract", "family_claim", "primary_claim", "program"):
        assert f"``StatClaimProgram.{name}" in proof
    assert proof == _proof_for_payload(PROGRAM_KIND, inputs())


def test_the_profile_lists_each_claim_with_its_grade_and_line():
    profile = _profile(PROGRAM_KIND, inputs())
    assert profile["status"] == "program_checked_under_premises"
    assert profile["claims"][1:] == [
        "familywise(endpoints), line 26: conditional",
        "typeI(response), line 27: proved",
    ]
    assert profile["assumptions"] == ["cited_symptoms_level"]
    assert profile["general_theorem"] == "StatClaimProgram.program"


def test_inputs_that_no_longer_match_their_source_are_refused():
    payload = inputs()
    edited = json.loads(json.dumps(payload))
    edited["source"]["text"] = edited["source"]["text"].replace("alpha=1/40", "alpha=1/50", 1)
    with pytest.raises(VerificationError, match="no longer compiles to the program"):
        _proof_for_payload(PROGRAM_KIND, edited)
    other = {**payload, "translation_version": certificate.TRANSLATION_VERSION + 1}
    with pytest.raises(VerificationError, match="another version of the translator"):
        _proof_for_payload(PROGRAM_KIND, other)
    with pytest.raises(certificate.Unchecked, match="does not compile"):
        certificate.payload(Source((ROOT / "examples/hypothesis_mismatch.stat").read_text()))


def test_a_grade_the_proof_does_not_support_is_refused():
    payload = inputs()
    honest = (
        "STATCLAIM_PREMISES program family_claim: cited_symptoms_level\n"
        "STATCLAIM_PREMISES program primary_claim: \n"
    )
    certificate.check_grades(payload, honest)
    overstated = honest.replace("primary_claim: ", "primary_claim: cited_symptoms_level")
    with pytest.raises(certificate.Unchecked, match="primary_claim"):
        certificate.check_grades(payload, overstated)
    with pytest.raises(certificate.Unchecked, match="listed no premises"):
        certificate.check_grades(payload, honest.splitlines()[0])


def test_the_report_says_what_lean_checked_or_why_not():
    checked = {
        "status": "checked",
        "certificate_id": "a" * 64,
        "certificate_directory": "bundle",
        "contract_facts": ["response_contract"],
        "premises": ["cited_symptoms_level"],
        "claims": [
            {
                "claim": "familywise(family)",
                "source": {"line": 9},
                "grade": "proved",
                "python": "conditional",
            }
        ],
        "not_translated": {"request_2": "Not yet."},
        "refuted": {},
    }
    text = "\n".join(lean_markdown(checked))
    assert "its 1 contract facts hold" in text
    assert "| `familywise(family)` | 9 | proved: uses no premise | conditional |" in text
    assert "Lean's grade stands" in text and "`request_2`: Not yet." in text
    failed = {"status": "failed", "message": "Lean (proof): it failed."}
    assert lean_markdown(failed) == ["## Lean check", "", "Lean (proof): it failed.", ""]


def test_report_lean_without_a_checkout_says_lean_is_unavailable(tmp_path, capsys):
    code = main(["report", str(MIXED), "--lean", "--project", str(tmp_path), "--json"])
    report = json.loads(capsys.readouterr().out)
    assert code == 1
    assert report["lean"]["status"] == "unavailable"
    assert "make setup" in report["lean"]["message"]


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_a_program_certificate_is_issued_replayed_and_bound(tmp_path):
    payload = inputs()
    issued, bundle = certify_program(payload, project=ROOT, output=tmp_path / "checked")
    assert issued["kind"] == PROGRAM_KIND
    replayed = recheck_certificate(bundle, project=ROOT)
    assert replayed["status"] == "verified"
    assert replayed["certificate_id"] == issued["certificate_id"]
    # A proof edited after the fact no longer matches what the inputs state.
    proof = bundle / "Proof.lean"
    proof.chmod(0o644)
    proof.write_text(proof.read_text().replace("primary_claim", "primary_claim'", 1))
    with pytest.raises(VerificationError):
        recheck_certificate(bundle, project=ROOT)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_report_lean_checks_a_program_and_records_refutations(tmp_path, capsys):
    path = ROOT / "examples/paper/fisher_adaptive.stat"
    code = main(
        ["report", str(path), "--lean", "--project", str(ROOT), "--json"]
        + ["--certificate", str(tmp_path / "checked")]
    )
    report = json.loads(capsys.readouterr().out)
    assert code == 0
    lean = report["lean"]
    assert lean["status"] == "checked" and lean["claims"] == []
    assert lean["refuted"] == {"verification": "design_no_law"}
    assert "design_no_law" in lean["contract_facts"]


def test_claims_lean_rejects_are_found_by_where_its_errors_fall():
    payload = inputs()
    stated = certificate.denotation(payload)
    proof = _proof_for_payload(PROGRAM_KIND, payload)
    lines = proof.splitlines()
    at = {
        name: lines.index(next(x for x in lines if x.startswith(f"theorem {name} "))) + 1
        for name in ("primary_claim", "response_contract")
    }
    error = "/b/Proof.lean:{}:3: error: unsolved goals"
    assert certificate.failing_claims(proof, error.format(at["primary_claim"] + 1), stated) == {
        "primary_claim"
    }
    # An error in a contract fact is the declarations failing, not one claim.
    assert certificate.failing_claims(proof, error.format(at["response_contract"]), stated) is None
    # The audit after the program fails whenever a claim does; it names no claim of its own.
    assert certificate.failing_claims(proof, error.format(len(lines) - 1), stated) == set()


def test_a_certificate_may_leave_out_claims_lean_did_not_prove():
    payload = {**inputs(), "omitted": ["primary_claim"]}
    assert [c.name for c in certificate.denotation(payload).claims] == ["family_claim"]
    assert (
        "Not proved in Lean, so left out: primary_claim."
        in _profile(PROGRAM_KIND, payload)["claims"]
    )
    with pytest.raises(certificate.Unchecked, match="does not state"):
        certificate.denotation({**inputs(), "omitted": ["no_such_claim"]})


def test_outside_a_run_no_request_takes_program_evidence():
    from statclaim.program_evidence import attach

    assert attach({"status": "unresolved_obligation"}) is None


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_check_proves_every_claim_in_one_lean_build(tmp_path):
    from statclaim.language_runner import check_source

    report = check_source(
        Source(MIXED.read_text(), str(MIXED)), project=ROOT, output=tmp_path / "run"
    )
    statuses = {r["subject"]: r["status"] for r in report["requests"]}
    assert statuses == {"endpoints": "conditional", "response": "verified"}
    bundles = {r["report"]["certificate"]["directory"] for r in report["requests"]}
    assert bundles == {str(tmp_path / "run/lean")}, "one certificate for the whole program"
    assert not list((tmp_path / "run").glob("request-*/certificate.json"))
    assert recheck_certificate(tmp_path / "run/lean", project=ROOT)["status"] == "verified"


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_a_claim_lean_does_not_prove_stays_open_and_the_rest_is_certified(tmp_path, monkeypatch):
    from statclaim import program_evidence
    from statclaim.lean_translation import prove

    honest = prove.claim
    # A broken proof of one claim, as a translator bug would give.
    monkeypatch.setattr(
        prove,
        "claim",
        lambda statement: (
            "by\n  exact absurd" if statement.name == "primary_claim" else honest(statement)
        ),
    )
    source = Source(MIXED.read_text(), str(MIXED))
    run = program_evidence.build(source, project=ROOT, output=tmp_path / "lean", timeout=600)
    assert set(run.claims) == {1} and set(run.failures) == {2}
    assert "Lean did not prove this claim" in run.failures[2]
    assert run.bundle == tmp_path / "lean-proved"
