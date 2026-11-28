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
from statclaim.wald import GRID, find_certificate, find_counterexample

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/wald_bound.stat"
TEXT = EXAMPLE.read_text()
SCORE_TEXT = (ROOT / "examples/score_bound.stat").read_text()


@pytest.mark.parametrize(("source", "ceiling"), ((TEXT, "103/1250"), (SCORE_TEXT, "27/500")))
def test_wald_and_score_claim_and_cutoff_round_trip(source, ceiling):
    compilation = compile_source(Source(source))
    assert compilation.diagnostics == ()
    [derivation] = compilation.derivations
    assert check_derivation(derivation.to_dict()) == []
    [request] = compilation.program.requests
    assert request.claim.guarantee.bound == Fraction(ceiling)
    program = compilation.program.to_dict()
    respelled = compile_source(Source(program_source(program)))
    assert respelled.diagnostics == ()
    assert declarations(respelled.program.to_dict()) == declarations(program)
    assert verify_claims(respelled.program.to_dict()) == verify_claims(program)


@pytest.mark.parametrize(
    ("original", "replacement", "diagnostic"),
    (
        ("2401/625", "0", "domain"),
        ("fixed(model=study)", "adaptive(model=study)", "sampling_scope"),
        (
            "equal_proportions(model=study)",
            "proportion_difference_at_most(model=study, value=0)",
            "hypothesis_mismatch",
        ),
    ),
)
@pytest.mark.parametrize("source", (TEXT, SCORE_TEXT), ids=("wald", "score"))
def test_proportion_z_requires_its_declared_fixed_equality_design(
    source, original, replacement, diagnostic
):
    compiled = compile_source(Source(source.replace(original, replacement)))
    assert diagnostic in {item.code for item in compiled.diagnostics}


def test_pooled_score_requires_equal_arm_sizes():
    compiled = compile_source(Source(SCORE_TEXT.replace("n_treatment=20", "n_treatment=21")))
    assert "unequal_arm_sizes" in {item.code for item in compiled.diagnostics}


def test_wald_search_covers_the_null_for_824_percent():
    cutoff = Fraction(2401, 625)
    certificate = find_certificate(20, cutoff, Fraction(103, 1250))
    assert certificate is not None
    assert len(certificate.weights) == 41
    assert 0 < certificate.cells[0] <= certificate.cells[-1] == GRID
    assert tuple(sorted(set(certificate.cells))) == certificate.cells
    assert find_certificate(20, cutoff, Fraction(1, 20)) is None


def test_wald_counterexample_search_can_leave_the_midpoint():
    cutoff = Fraction(2401, 625)
    assert find_counterexample(20, cutoff, Fraction(1, 20)) == (
        Fraction(1, 2),
        Fraction(22195551235, 274877906944),
    )
    rate, risk = find_counterexample(37, cutoff, Fraction(1, 20))
    assert rate == Fraction(1, 4)
    assert Fraction(1, 20) < risk
    assert find_counterexample(20, cutoff, Fraction(101, 1250)) is None


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_wald_verification_refutation_and_unresolved_claim_share_one_program(tmp_path):
    text = (
        TEXT
        + """
let tighter = wald_test(design=design, null=null, squared_cutoff=2401/625, alpha=101/1250)
let unresolved = verify(typeI(tighter))
let study37 = two_arm_binomial(n_control=37, n_treatment=37)
let design37 = fixed(model=study37)
let null37 = equal_proportions(model=study37)
let wald37 = wald_test(design=design37, null=null37, squared_cutoff=2401/625, alpha=1/20)
let refuted = verify(typeI(wald37))
"""
    )
    report = check_source(Source(text), project=ROOT, output=tmp_path / "checked")
    assert report["status"] == "refuted", report["diagnostics"]
    proved, open_claim, refuted = report["requests"]
    assert proved["status"] == "verified"
    assert open_claim["value"]["status"] == "unresolved_obligation"
    assert "wald_bound_unproved" in {item["code"] for item in report["diagnostics"]}
    assert refuted["value"]["status"] == "refuted"
    witness = refuted["value"]["counterexample"]
    assert witness["p"] == "1/4"
    assert Fraction(witness["typeI_error"]) > Fraction(witness["alpha"])
    assert witness["certificate"]["directory"] == report["lean"]["certificate_directory"]
    replay = recheck_certificate(Path(report["lean"]["certificate_directory"]), project=ROOT)
    assert replay["status"] == "verified"
    assert replay["counterexamples"][0]["request_id"] == refuted["request_id"]
    assert replay["counterexamples"][0]["typeI_error"] == witness["typeI_error"]


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_rejects_an_incorrect_wald_rejection_probability(tmp_path):
    inputs = payload(Source(TEXT.replace("103/1250", "1/20")), ROOT)
    inputs["wald_counterexamples"]["0"]["typeI_error"] = "1/10"
    with pytest.raises(VerificationError, match="decide"):
        certify_program(inputs, project=ROOT, output=tmp_path / "bad-witness")


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_pooled_score_certifies_54_percent_and_refutes_five_percent(tmp_path):
    text = (
        SCORE_TEXT
        + """
let smaller = score_test(design=design, null=null, squared_cutoff=2401/625, alpha=1/20)
let counterexample = verify(typeI(smaller))
"""
    )
    report = check_source(Source(text), project=ROOT, output=tmp_path / "score")
    assert report["status"] == "refuted", report["diagnostics"]
    verified, refuted = report["requests"]
    assert verified["status"] == "verified"
    witness = refuted["value"]["counterexample"]
    assert witness["p"] == "1/4"
    assert Fraction("0.0514") < Fraction(witness["typeI_error"]) < Fraction("0.05141")
    replay = recheck_certificate(Path(report["lean"]["certificate_directory"]), project=ROOT)
    assert replay["status"] == "verified"
    assert replay["counterexamples"][0]["typeI_error"] == witness["typeI_error"]


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_wald_certifies_a_ceiling_for_unequal_arms_and_refutes_nominal_level(tmp_path):
    example = ROOT / "examples/tutorial/54_unequal_arm_wald.stat"
    source = Source(example.read_text(), str(example))
    compiled = compile_source(source)
    assert not compiled.diagnostics
    assert len(compiled.derivations) == 2
    assert all(not check_derivation(d.to_dict()) for d in compiled.derivations)
    report = check_source(source, project=ROOT, output=tmp_path / "unequal")
    nominal, audited = report["requests"]
    assert nominal["status"] == "refuted"
    assert audited["status"] == "verified"
    witness = nominal["value"]["counterexample"]
    assert witness["p"] == "1/2"
    assert witness["typeI_error"] == "357887/4194304"
