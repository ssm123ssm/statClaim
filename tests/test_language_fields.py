"""Typed public fields, staging, and optional evidence without implicit proof."""

import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.language import FieldIR, elaborate
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import FieldAccess, Source, parse
from statclaim.verification import VerificationError

ROOT = Path(__file__).resolve().parents[1]
BASE = (ROOT / "tests/fixtures/fisher.stat").read_text().replace("verify typeI(analysis)\n", "")
CLAIM = "let claim = typeI(analysis)\nlet checked = verify(claim)\n"
OBSERVATION = "let data = observe(analysis, 10, 25)\nlet computation = calculate(result(data))\n"


def report(tail, tmp_path, *, fast=True, base=BASE):
    return check_source(
        Source(base + tail, "fields.stat"),
        project=ROOT,
        elaborate_only=fast,
        output=None if fast else tmp_path / "run",
    )


def test_static_projections_reuse_exact_typed_statistical_inputs(tmp_path):
    text = (
        "let level = analysis.alpha\nlet size = analysis.design.model.n_control\n"
        "let reused = fisher(analysis.design, analysis.null, alpha=level)\n"
        "let kind = typeI(reused).kind\nlet subject_level = typeI(reused).subject.alpha\n"
    )
    result = report(text, tmp_path)
    assert result["status"] == "elaborated"
    assert result["values"]["level"] == result["values"]["subject_level"] == "1/20"
    assert result["values"]["size"] == 100
    assert result["values"]["kind"] == "typeI"
    assert result["requests"] == []
    program, _ = elaborate(Source(BASE + text))
    assert program.bindings[-2].dependencies == ("reused",)
    assert next(b.value for b in program.bindings if b.name == "level") == Fraction(1, 20)


def test_fields_preserve_family_endpoint_names():
    source = (ROOT / "examples/two_outcomes.stat").read_text()
    source += "\nlet copied = bonferroni(outcomes.analyses, outcomes.alpha, outcomes.joint_law)\n"
    compilation = compile_source(Source(source))
    assert compilation.diagnostics == ()
    assert compilation.program.bindings[-1].value == compilation.program.bindings[-2].value


def test_parser_tracks_each_field_span_and_call_postfixes():
    statements, errors = parse(Source("let x = verify(claim).evidence.certificate.file\n"))
    assert errors == []
    value = statements[0].expression
    assert isinstance(value, FieldAccess)
    assert value.name == "file"
    assert value.name_span.column == 44
    assert value.subject.name == "certificate"


def test_runtime_projections_remain_deferred_during_compile(monkeypatch, tmp_path):
    monkeypatch.setattr(
        subprocess, "Popen", lambda *a, **k: pytest.fail("compiler invoked process")
    )
    monkeypatch.setattr(
        "statclaim.language_runner.test_design", lambda *a, **k: pytest.fail("calculation")
    )
    tail = (
        CLAIM
        + OBSERVATION
        + (
            "let status = checked.status\nlet evidence = checked.evidence\n"
            "let certificate = evidence.certificate.file\nlet p = computation.calculation.p_value\n"
            "let claim_again = checked.claim\n"
        )
    )
    result = report(tail, tmp_path)
    for name, kind in (
        ("status", "string"),
        ("evidence", "Option[Evidence]"),
        ("certificate", "Option[string]"),
        ("p", "Option[exact number]"),
    ):
        value = result["values"][name]
        assert value["type"] == "DeferredValue"
        assert value["status"] == "not_executed"
        assert value["value_type"] == kind
    assert result["values"]["claim_again"] == result["values"]["claim"]
    assert result["backend_invoked"] is False
    assert not list(tmp_path.iterdir())


@pytest.mark.parametrize("suffix", ["__class__", "lower", "not_a_field"])
def test_only_published_fields_are_accessible(suffix, tmp_path):
    result = report(f"let bad = analysis.{suffix}\n", tmp_path)
    assert result["status"] == "invalid"
    diagnostic = result["diagnostics"][0]
    assert diagnostic["code"] == "unknown_field"
    assert diagnostic["source"]["column"] == len("let bad = analysis.") + 1


@pytest.mark.parametrize(
    "tail,code",
    [
        (CLAIM + "let bad = two_arm_binomial(checked.request_id, 100)\n", "runtime_dependency"),
        (CLAIM + "let bad = fisher(plan, null, checked.evidence.certificate.file)\n", "type"),
        (CLAIM + "let bad = verify(checked.evidence.claim)\n", "type"),
        ("let bad = study.alpha\n", "unknown_field"),
        ("let bad = analysis.alpha.missing\n", "unknown_field"),
        ("let bad = analysis.\n", "syntax"),
        ("let bad = analysis..alpha\n", "syntax"),
    ],
)
def test_invalid_and_optional_fields_cannot_configure_statistical_objects(tail, code, tmp_path):
    result = report(tail, tmp_path)
    assert result["status"] == "invalid"
    assert result["diagnostics"][0]["code"] == code
    assert result["backend_invoked"] is False


def test_known_failures_yield_no_evidence_even_through_chained_aliases(tmp_path):
    tail = CLAIM + (
        "let status = checked.status\nlet proof = checked.evidence\n"
        "let path = proof.certificate.file\nlet properties = proof.established_properties\n"
        "let messages = checked.diagnostics\n"
        "let collected = [status, proof, [path]]\n"
    )
    result = report(tail, tmp_path, fast=False, base=BASE.replace("fixed(", "adaptive("))
    assert result["status"] == "unresolved_obligation"
    assert result["values"]["status"] == "unresolved_obligation"
    assert result["values"]["proof"] is None
    assert result["values"]["path"] is None
    assert result["values"]["properties"] is None
    assert result["values"]["messages"][0]["code"] == "sampling_scope"
    assert json.loads(json.dumps(result))["values"]["messages"][0]["severity"] == "obligation"
    assert result["values"]["collected"] == ["unresolved_obligation", None, [None]]
    assert result["certificate_issued"] is False
    assert result["backend_invoked"] is False
    assert len(result["requests"]) == 1
    assert not (tmp_path / "run").exists()


def test_backend_errors_produce_status_but_never_evidence(monkeypatch, tmp_path):
    def failed(*args, **kwargs):
        raise VerificationError("proof", "Controlled verification failure")

    monkeypatch.setattr("statclaim.report.certify_design", failed)
    result = report(
        CLAIM + "let state = checked.status\nlet path = checked.evidence.certificate.file\n",
        tmp_path,
        fast=False,
    )
    assert result["values"]["state"] == "backend_error"
    assert result["values"]["path"] is None
    assert result["certificate_issued"] is False


def test_exact_calculation_fields_are_values_without_evidence(monkeypatch, tmp_path):
    monkeypatch.setattr(
        subprocess, "Popen", lambda *a, **k: pytest.fail("calculation invoked Lean")
    )
    result = report(
        OBSERVATION
        + (
            "let p = computation.calculation.p_value\nlet level = computation.calculation.alpha\n"
            "let comparison = computation.calculation.p_value_le_alpha\n"
            "let state = computation.status\nlet decision = computation.decision\n"
        ),
        tmp_path,
        fast=False,
    )
    assert result["values"]["p"] == "19912805355158606332329/2341699062001756564467919"
    assert result["values"]["level"] == "1/20"
    assert result["values"]["comparison"] is True
    assert result["values"]["state"] == "calculated"
    assert result["values"]["decision"] == "reject_null"
    assert result["certificate_issued"] is False
    program, errors = elaborate(
        Source(BASE + OBSERVATION + "let p = computation.calculation.p_value\n")
    )
    assert errors == []
    assert isinstance(program.bindings[-1].value, FieldIR)
    assert program.bindings[-1].value.value_type.optional


def test_static_field_values_still_undergo_constructor_domain_checks(tmp_path):
    result = report(
        "let data = observe(analysis, 0, 1)\n"
        "let invalid = two_arm_binomial(data.control_successes, 10)\n",
        tmp_path,
    )
    assert result["status"] == "invalid"
    assert result["diagnostics"][0]["code"] == "domain"
