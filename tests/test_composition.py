import json
from dataclasses import replace
from fractions import Fraction
from pathlib import Path

import pytest

from statproof.cli import main
from statproof.design import Design, load_design
from statproof.family import Endpoint, FisherFamily, load_family
from statproof.fisher import fisher_exact, parse_alpha
from statproof.proof import render_family_proof, render_proof
from statproof.report import verify_family
from statproof.verification import (
    VerificationError,
    _parse_family_payload,
    _profile,
    design_payload,
    family_payload,
)

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize("value", ["-0.1", "1.01", "1/0", "NaN", 0.05, True])
def test_invalid_alpha_is_rejected(value):
    with pytest.raises(ValueError):
        parse_alpha(value)


def test_exact_alpha_normalizes_and_changes_decision():
    assert parse_alpha("0.025") == Fraction(1, 40)
    args = dict(n_control=4, n_treatment=4, control_successes=0, treatment_successes=4)
    loose = fisher_exact(**args)
    strict = fisher_exact(**args, alpha=Fraction(1, 40))
    assert loose.p_value == strict.p_value == Fraction(1, 35)
    assert loose.reject_null and not strict.reject_null
    assert strict.to_dict()["alpha"]["fraction"] == "1/40"
    with pytest.raises(ValueError, match="alpha"):
        render_proof(Design(4, 4, "fixed"), strict, "a" * 64)


def test_alpha_declaration_and_claims_are_bound():
    design = load_design(ROOT / "examples/fixed_sample_alpha.toml")
    assert design.alpha == Fraction(1, 40)
    payload = design_payload(design)
    assert "at most 1/40" in _profile("statproof_design_certificate", payload)["claims"][-1]
    assert payload["analysis"]["alpha"] == "1/40"


def test_family_round_trip_preserves_names_and_allocation():
    family = load_family(ROOT / "examples/two_outcomes.toml")
    assert family.allocated_alpha == family.alpha == Fraction(1, 20)
    assert _parse_family_payload(family_payload(family)) == family
    source = render_family_proof(family, "a" * 64)
    assert "MarginalContract" in source
    assert "checked_allocation" in source
    assert "checked_family" in source
    assert "checked_p_value" not in source


@pytest.mark.parametrize("change", ["method", "joint_law", "null", "alpha", "extra"])
def test_family_canonical_scope_rejects_changed_metadata(change):
    payload = family_payload(load_family(ROOT / "examples/two_outcomes.toml"))
    if change == "null":
        payload["analyses"][0]["analysis"]["null"] = "different_null"
    elif change == "alpha":
        payload["alpha"] = "0.05"  # canonical form must be 1/20
    else:
        payload[change] = "unrecognized"
    with pytest.raises(ValueError):
        _parse_family_payload(payload)


def test_overallocated_family_never_invokes_backend(monkeypatch, tmp_path):
    monkeypatch.setattr("statproof.report.certify_family", lambda *a, **k: pytest.fail("backend"))
    family = load_family(ROOT / "examples/two_outcomes_overallocated.toml")
    report = verify_family(family, project=ROOT, output=tmp_path / "unused")
    assert report["status"] == "unresolved_obligation"
    assert report["verification"]["stage"] == "allocation"
    assert report["certificate_issued"] is False
    assert report["backend_invoked"] is False
    assert not (tmp_path / "unused").exists()
    with pytest.raises(ValueError, match="allocated alpha"):
        family_payload(family)


def test_adaptive_family_has_no_fixed_certificate(monkeypatch, tmp_path):
    family = load_family(ROOT / "examples/two_outcomes.toml")
    first, second = family.endpoints
    adaptive = replace(
        family,
        endpoints=(replace(first, design=replace(first.design, stopping="data_dependent")), second),
    )
    monkeypatch.setattr("statproof.report.certify_family", lambda *a, **k: pytest.fail("backend"))
    report = verify_family(adaptive, project=ROOT, output=tmp_path / "unused")
    assert report["verification"]["stage"] == "sampling_scope"
    assert report["certificate_issued"] is False
    assert "not evidence of inflated error" in report["verification"]["message"]


def test_family_failed_proof_remains_unresolved(monkeypatch):
    def failed(*args, **kwargs):
        raise VerificationError("proof", "Failed")

    monkeypatch.setattr("statproof.report.certify_family", failed)
    report = verify_family(load_family(ROOT / "examples/two_outcomes.toml"), project=ROOT)
    assert report["status"] == "unresolved_obligation"
    assert report["established_properties"] == []


def test_family_cli_inspection_and_overallocation(capsys):
    assert main(["inspect-family", str(ROOT / "examples/two_outcomes.toml")]) == 1
    assert json.loads(capsys.readouterr().out)["verification_scope"] == "family"
    assert main(["verify-family", str(ROOT / "examples/two_outcomes_overallocated.toml")]) == 1
    assert json.loads(capsys.readouterr().out)["verification"]["stage"] == "allocation"


def test_duplicate_names_and_wrong_family_size_are_rejected():
    endpoint = Endpoint("same", Design(4, 4, "fixed"))
    with pytest.raises(ValueError, match="distinct"):
        FisherFamily(Fraction(1, 10), (endpoint, endpoint))
    with pytest.raises(ValueError, match="between 2 and"):
        FisherFamily(Fraction(1, 10), (endpoint,))


def test_families_of_several_endpoints_are_supported():
    endpoints = tuple(Endpoint(f"e{i}", Design(4, 5, "fixed", Fraction(1, 200))) for i in range(10))
    family = FisherFamily(Fraction(1, 20), endpoints)
    assert family.allocated_alpha == Fraction(1, 20)
    proof = render_family_proof(family, "0" * 64)
    assert "Fin 10 → FixedSampleDesign" in proof and "FisherFamilyN" in proof
