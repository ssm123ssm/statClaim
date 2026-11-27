import shutil
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_printer import program_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.lean_translation.data import declarations, verify_claims
from statclaim.verification import recheck_certificate
from statclaim.wald import GRID, find_certificate

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/wald_bound.stat"
TEXT = EXAMPLE.read_text()


def test_wald_claim_and_cutoff_round_trip():
    compilation = compile_source(Source(TEXT))
    assert compilation.diagnostics == ()
    [derivation] = compilation.derivations
    assert check_derivation(derivation.to_dict()) == []
    [request] = compilation.program.requests
    assert request.claim.guarantee.bound == Fraction(103, 1250)
    program = compilation.program.to_dict()
    respelled = compile_source(Source(program_source(program)))
    assert respelled.diagnostics == ()
    assert declarations(respelled.program.to_dict()) == declarations(program)
    assert verify_claims(respelled.program.to_dict()) == verify_claims(program)


@pytest.mark.parametrize(
    ("original", "replacement", "diagnostic"),
    (
        ("n_treatment=20", "n_treatment=21", "unequal_arm_sizes"),
        ("2401/625", "0", "domain"),
        ("fixed(model=study)", "adaptive(model=study)", "sampling_scope"),
        (
            "equal_proportions(model=study)",
            "proportion_difference_at_most(model=study, value=0)",
            "hypothesis_mismatch",
        ),
    ),
)
def test_wald_requires_its_declared_fixed_balanced_equality_design(
    original, replacement, diagnostic
):
    compiled = compile_source(Source(TEXT.replace(original, replacement)))
    assert diagnostic in {item.code for item in compiled.diagnostics}


def test_wald_search_covers_the_null_for_824_percent():
    cutoff = Fraction(2401, 625)
    certificate = find_certificate(20, cutoff, Fraction(103, 1250))
    assert certificate is not None
    assert len(certificate.weights) == 41
    assert 0 < certificate.cells[0] <= certificate.cells[-1] == GRID
    assert tuple(sorted(set(certificate.cells))) == certificate.cells
    assert find_certificate(20, cutoff, Fraction(1, 20)) is None


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_checked_wald_bound_replays_and_does_not_certify_five_percent(tmp_path):
    report = check_source(Source(TEXT, str(EXAMPLE)), project=ROOT, output=tmp_path / "valid")
    assert report["status"] == "verified", report["diagnostics"]
    bundle = Path(report["lean"]["certificate_directory"])
    assert recheck_certificate(bundle, project=ROOT)["status"] == "verified"

    too_small = Source(TEXT.replace("103/1250", "1/20"), "wald_005.stat")
    report = check_source(too_small, project=ROOT, output=tmp_path / "too-small")
    assert report["status"] == "unresolved_obligation"
    assert report["requests"][0]["value"]["status"] == "unresolved_obligation"
    assert "wald_bound_unproved" in {item["code"] for item in report["diagnostics"]}
