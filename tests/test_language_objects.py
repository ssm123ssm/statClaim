"""First-class claims/results and the boundary between compilation and execution."""

import json
import subprocess
from dataclasses import FrozenInstanceError
from pathlib import Path

import pytest

from statproof.cli import main
from statproof.language import (
    CalculationResultIR,
    ClaimIR,
    VerificationResultIR,
    elaborate,
)
from statproof.language_compiler import compile_source
from statproof.language_runner import check_source, render_report
from statproof.language_syntax import Source, Span
from statproof.language_values import (
    CalculationResult,
    Evidence,
    VerificationResult,
    resolve,
)
from statproof.verification import VerificationError

ROOT = Path(__file__).resolve().parents[1]
BASE = (ROOT / "examples/fisher.stat").read_text().replace("verify typeI(analysis)\n", "")
OBSERVATION = "let data = observe(analysis, 10, 25)\nlet observed = result(data)\n"


def first_class(tail="let checked = verify(claim)\n", base=BASE):
    return Source(base + "let claim = typeI(analysis)\n" + tail, "objects.stat")


def forbid_execution(monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("compilation must not calculate, invoke processes, or verify")

    monkeypatch.setattr(subprocess, "Popen", forbidden)
    for operation in ("test_design", "verify_design", "verify_design_only", "verify_family"):
        monkeypatch.setattr(f"statproof.language_runner.{operation}", forbidden)
    monkeypatch.setattr("statproof.fisher.fisher_exact", forbidden)


def test_first_class_claims_and_result_slots_have_types_sources_and_dependencies():
    program, diagnostics = elaborate(first_class("let checked = verify(claim=claim)\n"))
    assert diagnostics == []
    claim, checked = program.bindings[-2:]
    assert isinstance(claim.value, ClaimIR)
    assert isinstance(checked.value, VerificationResultIR)
    assert checked.value.request_id == 1
    assert checked.dependencies == ("claim",)
    assert checked.argument_sources == (("claim", Span("objects.stat", 12, 28, 12, 33)),)
    assert program.requests[0].claim is claim.value
    assert program.to_dict()["bindings"][-1]["value"] == {"request_id": 1}


@pytest.mark.parametrize("spelling", ["verify claim", "verify(claim)", "verify(claim=claim)"])
def test_old_and_new_unnamed_operation_spellings_share_the_plan(spelling):
    compilation = compile_source(first_class(spelling + "\n"))
    assert compilation.diagnostics == ()
    assert len(compilation.program.requests) == 1
    assert compilation.program.requests[0].operation == "verify"


def test_compile_and_fast_reports_never_execute_even_with_nested_operations(monkeypatch, tmp_path):
    forbid_execution(monkeypatch)
    text = BASE + OBSERVATION + "let results = [verify(typeI(analysis)), calculate(observed)]\n"
    source = Source(text)
    compilation = compile_source(source)
    assert compilation.status == "elaborated"
    assert len(compilation.program.requests) == 2
    values = compilation.program.bindings[-1].value
    assert isinstance(values[0].value, VerificationResultIR)
    assert isinstance(values[1].value, CalculationResultIR)
    report = check_source(source, project=tmp_path / "no-lean-project", elaborate_only=True)
    assert report["backend_invoked"] is False
    assert report["certificate_issued"] is False
    assert all(value["status"] == "not_executed" for value in report["values"]["results"])
    assert report["values"]["results"][0]["evidence"] is None
    assert report["values"]["results"][1]["calculation"] is None
    assert list(tmp_path.iterdir()) == []


def test_claim_declarations_alone_do_not_request_verification(monkeypatch, tmp_path):
    forbid_execution(monkeypatch)
    report = check_source(first_class("let claims = [claim, claim]\n"), project=tmp_path)
    assert report["status"] == "elaborated"
    assert report["requests"] == []
    assert report["values"]["claims"] == [report["values"]["claim"]] * 2
    assert list(tmp_path.iterdir()) == []


def test_named_operations_expose_known_blockers_before_execution(monkeypatch, tmp_path):
    forbid_execution(monkeypatch)
    source = first_class(base=BASE.replace("fixed(model=study)", "adaptive(model=study)"))
    compilation = compile_source(source)
    assert compilation.status == "unresolved_obligation"
    assert compilation.request_diagnostics[0][0].code == "sampling_scope"
    for fast in (True, False):
        report = check_source(source, project=tmp_path, elaborate_only=fast)
        checked = report["values"]["checked"]
        assert checked["status"] == ("not_executed" if fast else "unresolved_obligation")
        assert checked["evidence"] is None
        assert checked["diagnostics"][0]["code"] == "sampling_scope"
        assert report["requests"][0]["status"] == ("blocked" if fast else "unresolved_obligation")
    assert list(tmp_path.iterdir()) == []


def test_compilation_reports_all_family_requirements_and_follows_aliases():
    text = (ROOT / "examples/overallocated.stat").read_text()
    text = text.replace("fixed(model=study)", "adaptive(model=study)")
    text = text.replace(
        "verify familywise(outcomes)",
        "let alias = outcomes\nlet claim = familywise(alias)\nlet checked = verify(claim)",
    )
    compilation = compile_source(Source(text))
    assert compilation.status == "unresolved_obligation"
    blockers = compilation.request_diagnostics[0]
    assert [d.code for d in blockers] == ["allocation", "sampling_scope"]
    assert blockers[0].span.line == 13
    assert blockers[1].span.line == 7
    assert "does not prove excessive actual error" in blockers[0].message


@pytest.mark.parametrize(
    "tail,code",
    [
        ("let x = verify(analysis)", "type"),
        ("let x = verify()", "arguments"),
        ("let x = verify(claim, claim)", "arguments"),
        ("let x = verify(typo=claim)", "arguments"),
        ("let x = calculate(claim)", "type"),
        ("let x = verify(verify(claim))", "type"),
        ("let x = [verify(claim), unknown]", "unknown_name"),
        ("let verify = claim", "reserved_name"),
        ("let calculate = claim", "reserved_name"),
        ("typeI(analysis)", "type"),
    ],
)
def test_invalid_operation_expressions_are_diagnosed_without_leaking_requests(tail, code):
    compilation = compile_source(first_class(tail + "\n"))
    assert compilation.status == "invalid"
    assert compilation.diagnostics[0].code == code
    assert compilation.program.requests == ()


def test_results_cannot_be_used_as_claims_or_statistical_inputs():
    for tail in ("let again = verify(checked)", "let wrong = fisher(checked, null, 0.05)"):
        compilation = compile_source(first_class("let checked = verify(claim)\n" + tail + "\n"))
        assert compilation.status == "invalid"
        assert compilation.diagnostics[0].code == "type"
        assert len(compilation.program.requests) == 1


def test_result_aliases_and_nested_lists_reuse_an_immutable_runtime_value():
    compilation = compile_source(
        first_class(
            "let checked = verify(claim)\nlet alias = checked\nlet grouped = [[alias], checked]\n"
        )
    )
    assert compilation.status == "elaborated"
    assert len(compilation.program.requests) == 1
    value = VerificationResult(1, compilation.program.requests[0].claim, "snapshot", "not_executed")
    bindings = {
        binding.name: resolve(binding.value, {1: value}) for binding in compilation.program.bindings
    }
    assert bindings["checked"] is bindings["alias"] is bindings["grouped"][0][0]
    assert bindings["grouped"][1] is value
    with pytest.raises(FrozenInstanceError):
        value.status = "verified"


def test_calculation_bindings_and_aliases_execute_once_without_formal_evidence(
    monkeypatch, tmp_path
):
    import statproof.language_runner as runner

    original = runner.test_design
    calls = []

    def counted(*args, **kwargs):
        calls.append(1)
        return original(*args, **kwargs)

    monkeypatch.setattr(runner, "test_design", counted)
    monkeypatch.setattr(
        subprocess, "Popen", lambda *a, **k: pytest.fail("calculation invoked Lean")
    )
    text = (
        BASE
        + OBSERVATION
        + (
            "let computation = calculate(claim=observed)\n"
            "let alias = computation\nlet grouped = [alias, [computation]]\n"
        )
    )
    report = check_source(Source(text), project=ROOT, output=tmp_path / "run")
    assert calls == [1]
    value = report["values"]["computation"]
    assert value["type"] == "CalculationResult"
    assert value["status"] == "calculated"
    assert value == report["values"]["alias"] == report["values"]["grouped"][1][0]
    assert value["source_sha256"] == report["source"]["sha256"]
    assert value["calculation"]["p_value"]["fraction"] == (
        "19912805355158606332329/2341699062001756564467919"
    )
    assert report["certificate_issued"] is False
    assert json.loads((tmp_path / "run/run.json").read_text()) == report
    assert "calculated [computation, alias]" in render_report(report, Source(text))


def test_backend_failure_produces_a_named_error_value_and_other_requests_continue(
    monkeypatch, tmp_path
):
    def fail(*args, **kwargs):
        raise VerificationError("proof", "Controlled proof failure.")

    monkeypatch.setattr("statproof.report.certify_design", fail)
    text = first_class().text + OBSERVATION + "let computation = calculate(observed)\n"
    report = check_source(Source(text), project=ROOT, output=tmp_path / "run")
    value = report["values"]["checked"]
    assert value["status"] == "backend_error"
    assert value["evidence"] is None
    assert value["diagnostics"][0]["message"] == "Controlled proof failure."
    assert report["values"]["computation"]["status"] == "calculated"
    assert report["status"] == "unresolved_obligation"
    assert "backend_error [checked]" in render_report(report, Source(text))


def test_separate_operation_calls_are_not_deduplicated(monkeypatch, tmp_path):
    import statproof.language_runner as runner

    original = runner.test_design
    calls = []

    def counted(*args, **kwargs):
        calls.append(1)
        return original(*args, **kwargs)

    monkeypatch.setattr(runner, "test_design", counted)
    text = BASE + OBSERVATION + "let attempts = [calculate(observed), calculate(observed)]\n"
    report = check_source(Source(text), project=ROOT, output=tmp_path / "run")
    assert len(calls) == 2
    assert [value["request_id"] for value in report["values"]["attempts"]] == [1, 2]


def test_named_results_remain_bound_to_the_original_snapshot_after_an_edit(monkeypatch, tmp_path):
    import statproof.language_runner as runner

    original = runner.test_design
    text = BASE + OBSERVATION + "let computation = calculate(observed)\n"
    path = tmp_path / "study.stat"
    path.write_text(text)

    def mutate(*args, **kwargs):
        result = original(*args, **kwargs)
        path.write_text(text.replace("alpha=1/20", "alpha=1/40"))
        return result

    monkeypatch.setattr(runner, "test_design", mutate)
    report = check_source(Source(text, str(path)), project=ROOT, output=tmp_path / "run")
    value = report["values"]["computation"]
    assert report["status"] == "stale_source"
    assert value["status"] == "calculated"
    assert value["source_sha256"] == report["source"]["sha256"]
    edited = check_source(Source(path.read_text(), str(path)), project=ROOT, elaborate_only=True)
    assert edited["values"]["computation"]["status"] == "not_executed"
    assert edited["source"]["sha256"] != value["source_sha256"]


def test_execution_values_cannot_change_evidence_or_numeric_payloads():
    compilation = compile_source(first_class())
    claim = compilation.program.requests[0].claim
    certificate = {"certificate_id": "checked", "dependencies": ["a"]}
    evidence = Evidence(claim, certificate, ("claim checked",), ("model assumed",))
    certificate["dependencies"].append("changed")
    assert evidence.to_dict()["certificate"]["dependencies"] == ["a"]
    with pytest.raises(TypeError):
        evidence.certificate["certificate_id"] = "changed"
    with pytest.raises(ValueError, match="Only a successful"):
        VerificationResult(1, claim, "snapshot", "verified")
    with pytest.raises(ValueError, match="Only a successful"):
        VerificationResult(1, claim, "snapshot", "backend_error", evidence)
    other_claim = (
        elaborate(Source(BASE + OBSERVATION + "let claim = result(data)\n"))[0].bindings[-1].value
    )
    with pytest.raises(ValueError, match="must establish"):
        VerificationResult(1, other_claim, "snapshot", "verified", evidence)
    data = {"p_value": {"fraction": "1/20"}}
    calculation = CalculationResult(1, claim, "snapshot", "calculated", data)
    data["p_value"]["fraction"] = "1/2"
    assert calculation.to_dict()["calculation"]["p_value"]["fraction"] == "1/20"


@pytest.mark.parametrize("name,exit_code", [("first_class.stat", 0), ("overallocated.stat", 1)])
def test_compile_cli_checks_requirements_without_execution(name, exit_code, monkeypatch, capsys):
    forbid_execution(monkeypatch)
    assert main(["compile", str(ROOT / "examples" / name), "--json"]) == exit_code
    report = json.loads(capsys.readouterr().out)
    assert report["backend_invoked"] is False
    assert report["certificate_issued"] is False
    assert "run_directory" not in report


def test_compile_cli_invalid_program_returns_two_without_executing(monkeypatch, tmp_path, capsys):
    forbid_execution(monkeypatch)
    path = tmp_path / "invalid.stat"
    path.write_text(first_class("let checked = verify(analysis)\n").text)
    assert main(["compile", str(path), "--json"]) == 2
    assert json.loads(capsys.readouterr().out)["status"] == "invalid"
