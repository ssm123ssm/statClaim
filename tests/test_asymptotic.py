import shutil
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_printer import program_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.lean_translation.certificate import payload
from statclaim.lean_translation.data import declarations, verify_claims
from statclaim.verification import VerificationError, certify_program, recheck_certificate

ROOT = Path(__file__).resolve().parents[1]
TUTORIAL = ROOT / "examples/tutorial"
CASES = (
    ("48_asymptotic_mcnemar", "mcnemar_asymptotic", "1", "9/128"),
    ("49_farrington_manning", "farrington_manning", "3/5", "361176064/6103515625"),
)


def lesson(stem):
    file = TUTORIAL / f"{stem}.stat"
    return Source(file.read_text(), str(file))


@pytest.mark.parametrize(("stem", "test", "rate", "risk"), CASES)
def test_asymptotic_claims_round_trip(stem, test, rate, risk):
    source = lesson(stem)
    compiled = compile_source(source)
    assert not compiled.diagnostics
    assert len(compiled.derivations) == 2
    assert all(not check_derivation(d.to_dict()) for d in compiled.derivations)
    assert [request.claim.guarantee.bound for request in compiled.program.requests] == [
        Fraction(1, 20),
        Fraction(1, 10),
    ]
    canonical = compiled.program.to_dict()
    printed = compile_source(Source(program_source(canonical)))
    assert not printed.diagnostics
    assert declarations(printed.program.to_dict()) == declarations(canonical)
    assert verify_claims(printed.program.to_dict()) == verify_claims(canonical)
    inputs = payload(source, ROOT)
    assert inputs[f"{test}_counterexamples"] == {"0": {"p": rate, "typeI_error": risk}}


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
@pytest.mark.parametrize(("stem", "test", "rate", "risk"), CASES)
def test_lean_checks_both_claims_and_rejects_tampered_witness(tmp_path, stem, test, rate, risk):
    source = lesson(stem)
    report = check_source(source, project=ROOT, output=tmp_path / "audit")
    failed, proved = report["requests"]
    assert failed["status"] == "refuted"
    assert proved["status"] == "verified"
    counterexample = failed["value"]["counterexample"]
    assert (counterexample["p"], counterexample["typeI_error"]) == (rate, risk)
    replay = recheck_certificate(Path(report["lean"]["certificate_directory"]), project=ROOT)
    assert replay["status"] == "verified"
    assert replay["counterexamples"][0]["typeI_error"] == risk

    inputs = payload(source, ROOT)
    inputs[f"{test}_counterexamples"]["0"]["typeI_error"] = "1/10"
    with pytest.raises(VerificationError, match="decide"):
        certify_program(inputs, project=ROOT, output=tmp_path / "bad-witness")


def test_one_sample_score_binds_a_point_null():
    source = lesson("50_one_sample_score")
    compiled = compile_source(source)
    assert not compiled.diagnostics
    assert len(compiled.derivations) == 3
    assert all(not check_derivation(d.to_dict()) for d in compiled.derivations)
    quarter, half, wider = (req.claim.guarantee for req in compiled.program.requests)
    assert quarter.null == wider.null == "response rate = 1/4"
    assert half.null == "response rate = 1/2"
    canonical = compiled.program.to_dict()
    printed = compile_source(Source(program_source(canonical)))
    assert not printed.diagnostics
    assert declarations(printed.program.to_dict()) == declarations(canonical)
    assert verify_claims(printed.program.to_dict()) == verify_claims(canonical)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_checks_one_sample_score_at_the_declared_null(tmp_path):
    source = lesson("50_one_sample_score")
    report = check_source(source, project=ROOT, output=tmp_path / "score")
    quarter, half, wider = report["requests"]
    assert quarter["status"] == "refuted"
    assert half["status"] == wider["status"] == "verified"
    witness = quarter["value"]["counterexample"]
    assert witness["p"] == "1/4"
    assert witness["typeI_error"] == "71729711503/1099511627776"

    inputs = payload(source, ROOT)
    inputs["binomial_score_counterexamples"]["0"]["p"] = "1/2"
    with pytest.raises(VerificationError, match="decide"):
        certify_program(inputs, project=ROOT, output=tmp_path / "wrong-null")


def test_pearson_distinguishes_the_declared_correction():
    source = lesson("51_pearson_unequal_arms")
    compiled = compile_source(source)
    assert not compiled.diagnostics
    assert len(compiled.derivations) == 2
    assert all(not check_derivation(d.to_dict()) for d in compiled.derivations)
    canonical = compiled.program.to_dict()
    plain, corrected = verify_claims(canonical)
    assert plain["subject"]["correction"] == "none"
    assert corrected["subject"]["correction"] == "yates"
    printed = compile_source(Source(program_source(canonical)))
    assert not printed.diagnostics
    assert declarations(printed.program.to_dict()) == declarations(canonical)
    assert verify_claims(printed.program.to_dict()) == verify_claims(canonical)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_checks_pearson_with_and_without_the_correction(tmp_path):
    source = lesson("51_pearson_unequal_arms")
    report = check_source(source, project=ROOT, output=tmp_path / "pearson")
    plain, corrected = report["requests"]
    assert plain["status"] == "refuted"
    assert corrected["status"] == "verified"
    assert plain["value"]["counterexample"]["typeI_error"] == "135/2048"
    replay = recheck_certificate(Path(report["lean"]["certificate_directory"]), project=ROOT)
    assert replay["status"] == "verified"


def test_likelihood_ratio_rule_and_null_round_trip():
    source = lesson("52_likelihood_ratio")
    compiled = compile_source(source)
    assert not compiled.diagnostics
    assert len(compiled.derivations) == 2
    assert all(not check_derivation(d.to_dict()) for d in compiled.derivations)
    canonical = compiled.program.to_dict()
    printed = compile_source(Source(program_source(canonical)))
    assert not printed.diagnostics
    assert declarations(printed.program.to_dict()) == declarations(canonical)
    assert verify_claims(printed.program.to_dict()) == verify_claims(canonical)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_audits_an_unequal_arm_likelihood_ratio_test(tmp_path):
    source = lesson("52_likelihood_ratio")
    report = check_source(source, project=ROOT, output=tmp_path / "likelihood-ratio")
    nominal, certified = report["requests"]
    assert nominal["status"] == "refuted"
    assert certified["status"] == "verified"
    witness = nominal["value"]["counterexample"]
    assert witness["typeI_error"] == "263/4096"
    assert witness["p"] == "1/2"
    replay = recheck_certificate(Path(report["lean"]["certificate_directory"]), project=ROOT)
    assert replay["status"] == "verified"
