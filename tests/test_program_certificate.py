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
# Stated through the semantics of compiled programs.
MIXED = ROOT / "examples/mixed_endpoints.stat"
# A cited cluster test beside a randomisation test, and one-sided Fisher.
CLUSTERS = ROOT / "examples/cluster_trial.stat"
ONE_SIDED = ROOT / "examples/one_sided.stat"


def inputs(path: Path = MIXED) -> dict:
    return certificate.payload(Source(path.read_text(), str(path.relative_to(ROOT))))


def test_a_covered_program_is_its_data_and_the_soundness_theorem():
    payload = inputs()
    input_id = digest(canonical_bytes(payload))
    proof = _proof_for_payload(PROGRAM_KIND, payload)
    assert proof.startswith("import StatClaim\n")
    assert "def program : StatClaim.Semantics.Program where" in proof
    assert "theorem claim_1 : program.Claim 1 :=" in proof
    assert "StatClaim.Semantics.Program.sound program contracts 1" in proof
    assert f'logInfo "STATCLAIM_CHECKED {input_id}"' in proof
    # The contracts and every claim are audited.
    for name in ("contracts", "claim_0", "claim_1"):
        assert f"``StatClaimProgram.{name}" in proof
    assert proof == _proof_for_payload(PROGRAM_KIND, inputs())


def test_a_randomisation_test_uses_the_same_soundness_theorem():
    proof = _proof_for_payload(PROGRAM_KIND, inputs(CLUSTERS))
    assert '.randomised "permuted"' in proof
    for name in ("contracts", "claim_0", "claim_1"):
        assert f"``StatClaimProgram.{name}" in proof


def test_the_profile_lists_each_claim_with_its_grade_and_line():
    profile = _profile(PROGRAM_KIND, inputs())
    assert profile["status"] == "program_checked_under_premises"
    assert profile["claims"][1:] == [
        "familywise(endpoints), line 26: conditional",
        "typeI(response), line 27: proved",
    ]
    assert profile["assumptions"] == ["cited_symptoms_level"]
    assert profile["general_theorem"] == "StatClaim.Semantics.Program.sound"
    assert "StatClaim/Semantics" in profile["trusted_components"][-1]
    translated = _profile(PROGRAM_KIND, inputs(CLUSTERS))
    assert translated["claims"][1:] == [
        "typeI(summaries), line 33: cited",
        "typeI(permuted), line 34: proved",
    ]
    assert translated["general_theorem"] == profile["general_theorem"]


def test_inputs_that_no_longer_match_their_source_are_refused():
    payload = inputs()
    edited = json.loads(json.dumps(payload))
    edited["source"]["text"] = edited["source"]["text"].replace("alpha=1/40", "alpha=1/50", 1)
    with pytest.raises(VerificationError, match="no longer compiles to the program"):
        _proof_for_payload(PROGRAM_KIND, edited)
    other = {**payload, "translation_version": certificate.TRANSLATION_VERSION + 1}
    with pytest.raises(VerificationError, match="version that issued it"):
        _proof_for_payload(PROGRAM_KIND, other)
    with pytest.raises(certificate.Unchecked, match="does not compile"):
        certificate.payload(Source((ROOT / "examples/hypothesis_mismatch.stat").read_text()))


def test_semantic_grades_and_binding_must_be_what_lean_prints():
    from statclaim.lean_translation import data

    payload = inputs()
    program = payload["program"]
    printed = {"claims": data.verify_claims(program), "declarations": data.declarations(program)}
    honest = (
        f"STATCLAIM_PROGRAM program {json.dumps(printed)}\n"
        "STATCLAIM_GRADES program [conditional, proved]\n"
    )
    certificate.check_grades(payload, honest)
    with pytest.raises(certificate.Unchecked, match="grade"):
        certificate.check_grades(payload, honest.replace("conditional,", "proved,"))
    other = json.dumps(printed).replace('"1/20"', '"1/40"', 1)
    with pytest.raises(certificate.Unchecked, match="not its canonical program"):
        certificate.check_grades(payload, honest.replace(json.dumps(printed), other))


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
    assert "contracts of 1 declared tests and combinations" in text
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
    proof.write_text(proof.read_text().replace("claim_1", "claim_1'", 1))
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
    assert lean["status"] == "checked" and lean["claims"] == [] and lean["semantics"]
    # The design stops by a rule that depends on the data: the claim is False, unproved.
    assert lean["refuted"] == {"typeI(analysis)": "no sampling law"}
    assert lean["contract_facts"] == ["analysis"]


def test_claims_lean_rejects_are_found_by_where_its_errors_fall():
    proof = _proof_for_payload(PROGRAM_KIND, inputs(ONE_SIDED))
    lines = proof.splitlines()
    at = {
        name: lines.index(next(x for x in lines if x.startswith(f"theorem {name} "))) + 1
        for name in ("claim_0", "contracts")
    }
    error = "/b/Proof.lean:{}:3: error: unsolved goals"
    assert certificate.failing_claims(proof, error.format(at["claim_0"] + 1)) == {0}
    assert certificate.failing_claims(proof, error.format(at["contracts"])) is None
    assert certificate.failing_claims(proof, error.format(len(lines) - 1)) == set()


def test_a_certificate_may_leave_out_claims_lean_did_not_prove():
    payload = {**inputs(), "omitted": [1]}
    assert [c["claim"] for c in certificate.claims(payload)] == ["familywise(endpoints)"]
    assert certificate.summary(payload)["unproved"] == ["typeI(response)"]
    with pytest.raises(certificate.Unchecked, match="unknown verification request"):
        certificate.checked({**inputs(), "omitted": [2]})


def test_run_evidence_requires_the_reported_p_value_and_decision():
    from statclaim.language_compiler import compile_source
    from statclaim.language_runner import _run_request
    from statclaim.program_evidence import ProgramRun, bind_report

    path = ROOT / "examples/fisher_result.stat"
    source = Source(path.read_text(), str(path))
    compiled = compile_source(source).program
    verification = next(r for r in compiled.requests if r.operation == "verify")
    calculation = next(r for r in compiled.requests if r.operation == "calculate")
    inputs = certificate.payload(source)
    agreed = _run_request(calculation, ROOT, ROOT, 120)
    agreed["certificate_issued"] = True
    run = ProgramRun({"inputs": inputs}, None, {}, {})
    request_id = compiled.requests.index(verification) + 1

    assert bind_report(run, request_id, verification, agreed.copy())["certificate_issued"]
    changed = json.loads(json.dumps(agreed))
    changed["calculation"]["p_value"]["fraction"] = "1"
    rejected = bind_report(run, request_id, verification, changed)
    assert not rejected["certificate_issued"]
    assert rejected["verification"]["stage"] == "binding"
    changed = {**agreed, "decision": "do_not_reject_null"}
    assert not bind_report(run, request_id, verification, changed)["certificate_issued"]


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
    from statclaim.lean_translation import material

    honest = material.material

    def missing_hint(*args, **kwargs):
        reported, hints = honest(*args, **kwargs)
        return reported, {**hints, 0: "[]"}

    monkeypatch.setattr(material, "material", missing_hint)
    source = Source(ONE_SIDED.read_text(), str(ONE_SIDED.relative_to(ROOT)))
    run = program_evidence.build(source, project=ROOT, output=tmp_path / "lean", timeout=600)
    assert set(run.claims) == {2, 3} and set(run.failures) == {1}
    assert "Lean did not prove this claim" in run.failures[1]
    assert run.bundle == tmp_path / "lean-proved"


COPD_POWER = ROOT / "replication/copd/power.stat"


def test_a_check_that_only_calculates_still_builds_the_program_in_lean(tmp_path, monkeypatch):
    from statclaim.language_runner import check_source, render_report

    built = []

    def issue(inputs, *, project, output, timeout):
        built.append(output)
        return {"certificate_id": "issued", "claims": []}, output

    monkeypatch.setattr("statclaim.language_runner.lean_available", lambda project: True)
    monkeypatch.setattr("statclaim.program_evidence.certify_program", issue)
    source = Source(COPD_POWER.read_text(), "power.stat")
    report = check_source(source, project=ROOT, output=tmp_path / "run")
    assert built == [tmp_path / "run/lean"]
    assert report["lean"] == {
        "status": "checked",
        "certificate_directory": str(tmp_path / "run/lean"),
        "contract_facts": 4,
    }
    # Lean checked the declarations; the values are still only calculated.
    assert report["status"] == "calculated" and report["backend_invoked"]
    text = render_report(report, source)
    assert (
        "Whole program in Lean: the declarations meet 4 contract facts, each decided by Lean.\n"
        "  Calculated and simulated values are not proved in Lean.\n"
        f"  Certificate: {tmp_path / 'run/lean'}\n"
        "Program status: calculated"
    ) in text
    # Recalculating alone builds nothing.
    again = check_source(source, project=ROOT, output=tmp_path / "again", operations={"calculate"})
    assert built == [tmp_path / "run/lean"] and "lean" not in again


def test_a_build_lean_rejects_is_reported_once_with_or_without_claims(tmp_path, monkeypatch):
    from statclaim.language_runner import check_source, render_report

    def fail(*args, **kwargs):
        raise VerificationError("proof", "tdi_ni_contract: decide failed")

    monkeypatch.setattr("statclaim.language_runner.lean_available", lambda project: True)
    monkeypatch.setattr("statclaim.program_evidence.certify_program", fail)
    source = Source(COPD_POWER.read_text(), "power.stat")
    report = check_source(source, project=ROOT, output=tmp_path / "power")
    lean = report["lean"]
    assert (lean["status"], lean["stage"], lean["error"]) == (
        "failed",
        "proof",
        "tdi_ni_contract: decide failed",
    )
    assert "This disagreement is a defect" in lean["message"]
    assert report["status"] == "calculated"
    assert render_report(report, source).count(lean["message"]) == 1
    # With claims, each unresolved claim already carries the message.
    mixed = Source(MIXED.read_text(), "mixed.stat")
    report = check_source(mixed, project=ROOT, output=tmp_path / "mixed")
    assert report["lean"]["status"] == "failed"
    assert report["status"] == "unresolved_obligation"
    assert render_report(report, mixed).count(report["lean"]["message"]) == 2


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_checks_the_declarations_of_a_program_that_only_calculates(tmp_path):
    from statclaim.language_runner import check_source

    source = Source(COPD_POWER.read_text(), str(COPD_POWER))
    report = check_source(source, project=ROOT, output=tmp_path / "run")
    assert report["status"] == "calculated"
    assert report["lean"]["status"] == "checked" and report["lean"]["contract_facts"] == 4
    issued = json.loads((tmp_path / "run/lean/certificate.json").read_text())
    assert issued["claims"] == [
        "Lean checks the contract facts of 4 test and combination declarations."
    ]
    assert recheck_certificate(tmp_path / "run/lean", project=ROOT)["status"] == "verified"
