"""Contract derivations: structure, independent checking, silence, reports and impact."""

import copy
import json
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.contract_reports import (
    explain,
    explanation_markdown,
    impact,
    report_markdown,
    study_report,
)
from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source
from statclaim.lsp import Server

ROOT = Path(__file__).resolve().parents[1]
BASE = """use models.two_arm_binomial
use sampling
use tests.fisher
let study = two_arm_binomial(n_control=50, n_treatment=50)
let design = fixed(model=study)
let null = equal_proportions(model=study)
let analysis = fisher(design=design, null=null, alpha=1/20)
let verification = verify(typeI(analysis))
"""
URI = "file:///study.stat"


def compiled(text: str):
    return compile_source(Source(text, "study.stat"))


def derivation(text: str = BASE, name: str = "analysis") -> dict:
    (entry,) = explain(compiled(text), name)
    return entry["derivation"]


def test_passing_contract_keeps_a_structured_derivation():
    compilation = compiled(BASE)
    assert [d.name for d in compilation.derivations] == ["analysis"]
    record = derivation()
    assert record["scope"] == "compatibility"
    assert [step["rule"] for step in record["steps"]] == [
        "same-model",
        "supported-null",
        "level-range",
        "analysis-contract",
        "fixed-sampling",
    ]
    assert record["steps"][3]["uses"] == [0, 1, 2]
    assert record["steps"][0]["facts"]["design_model"] == {"n_control": 50, "n_treatment": 50}
    assert record["assumptions"] and not record["obligations"]
    assert "No statistical guarantee" in record["not_established"]
    assert check_derivation(record) == []


def test_failed_contract_has_a_diagnostic_and_no_derivation():
    text = BASE.replace(
        "equal_proportions(model=study)", "proportion_difference(model=study, value=1/10)"
    )
    compilation = compiled(text)
    assert "hypothesis_mismatch" in [d.code for d in compilation.diagnostics]
    assert compilation.derivations == ()


def test_unresolved_obligation_is_recorded_and_distinct_from_assumptions():
    record = derivation(BASE.replace("fixed(model=study)", "adaptive(model=study)"))
    assert [item["code"] for item in record["obligations"]] == ["sampling_scope"]
    assert "fixed-sampling" not in [step["rule"] for step in record["steps"]]
    assert all("sampling depends" not in assumption for assumption in record["assumptions"])
    assert check_derivation(record) == []


def tamper(change):
    record = copy.deepcopy(derivation())
    change(record)
    return check_derivation(record)


@pytest.mark.parametrize(
    "change",
    [
        lambda d: d["steps"].pop(1),
        lambda d: d["steps"][1].update(rule="same-model"),
        lambda d: d["steps"][0]["facts"]["null_model"].update(n_control=51),
        lambda d: d["subject"]["null"].update(predicate="proportion_difference", value="1/10"),
        lambda d: d["subject"]["null"]["model"].update(n_treatment=40),
        lambda d: d["subject"].update(alpha="3/2"),
        lambda d: d["steps"][3].update(uses=[0, 1]),
        lambda d: d["steps"][3].update(uses=[0, 1, 3]),
        lambda d: d["steps"][2].update(conclusion="analysis: Type I error is at most 1/20."),
        lambda d: d.update(conclusion="analysis: Type I error is at most 1/20."),
        lambda d: d["assumptions"].pop(),
        lambda d: d.update(scope="guarantee"),
        lambda d: d.update(not_established=""),
        lambda d: d["subject"]["design"].update(stopping="data_dependent"),
        lambda d: d.update(steps=[{"rule": "analysis-contract"}]),
        lambda d: d.update(steps=[]),
    ],
)
def test_checker_rejects_altered_derivations(change):
    assert tamper(change)


def test_a_rule_name_or_flag_alone_is_not_a_proof():
    assert check_derivation({"name": "analysis", "contract": "tests.fisher/fisher", "ok": True})
    hidden = copy.deepcopy(derivation(BASE.replace("fixed(model=study)", "adaptive(model=study)")))
    hidden["obligations"] = []
    assert check_derivation(hidden)


def test_checker_does_not_use_the_contract_or_builder_code(monkeypatch):
    record = derivation()
    import statclaim.derivations as builder
    import statclaim.language_contracts as contracts

    def forbidden(*args, **kwargs):
        raise AssertionError("the checker must not call the code that built the derivation")

    for name in ("derive_analysis", "derive_family", "derive_program", "conclude", "oblige"):
        monkeypatch.setattr(builder, name, forbidden)
    monkeypatch.setattr(contracts.HypothesisContract, "check", forbidden)
    monkeypatch.setattr(contracts.HypothesisContract, "accepts", forbidden)
    assert check_derivation(record) == []


def test_family_derivation_and_allocation_obligation():
    good = compiled((ROOT / "examples/three_outcomes.stat").read_text())
    (family,) = [e for e in explain(good) if e["name"] == "endpoints"]
    assert family["checked"] and not family["derivation"]["obligations"]
    rules = [step["rule"] for step in family["derivation"]["steps"]]
    assert rules.count("analysis-contract") == 3 and "allocation" in rules
    over = compiled((ROOT / "examples/overallocated.stat").read_text())
    (family,) = [e for e in explain(over) if e["name"] == "outcomes"]
    assert family["checked"]
    assert [o["code"] for o in family["derivation"]["obligations"]] == ["allocation"]
    altered = copy.deepcopy(family["derivation"])
    altered["subject"]["alpha"] = "1/5"
    assert check_derivation(altered)


@pytest.mark.parametrize("path", sorted((ROOT / "examples").rglob("*.stat")), ids=lambda p: p.stem)
def test_every_example_derivation_passes_the_checker(path):
    for entry in explain(compile_source(Source(path.read_text(), str(path)))):
        assert entry["checked"], entry["problems"]


def server():
    sent = []
    instance = Server(sent.append)

    def send(method, params=None, identifier=None):
        message = {"jsonrpc": "2.0", "method": method, "params": params or {}}
        if identifier is not None:
            message["id"] = identifier
        before = len(sent)
        instance.handle(message)
        return sent[before:]

    send("initialize", {}, 1)
    send("initialized")
    return send


def open_document(send, text=BASE):
    return send(
        "textDocument/didOpen",
        {"textDocument": {"uri": URI, "languageId": "statclaim", "version": 1, "text": text}},
    )


def test_success_is_silent_and_explanations_are_on_request():
    send = server()
    messages = open_document(send)
    # Only the usual diagnostics notification, and it is empty for a valid file.
    assert [m["method"] for m in messages] == ["textDocument/publishDiagnostics"]
    assert messages[0]["params"]["diagnostics"] == []
    position = {"line": 6, "character": 6}
    (reply,) = send("statclaim/explain", {"textDocument": {"uri": URI}, "position": position}, 2)
    result = reply["result"]
    assert [c["name"] for c in result["contracts"]] == ["analysis"]
    assert result["contracts"][0]["checked"]
    assert result["contracts"][0]["range"]["start"]["line"] == 6
    assert "Why it passed" in result["markdown"] and "Unresolved obligations" in result["markdown"]
    # Without a position, or away from a contract, every contract in the file is returned.
    (reply,) = send("statclaim/explain", {"textDocument": {"uri": URI}}, 3)
    assert len(reply["result"]["contracts"]) == 1


def test_editor_impact_is_measured_against_the_saved_text():
    send = server()
    open_document(send)
    changed = BASE.replace("n_control=50", "n_control=60")
    send(
        "textDocument/didChange",
        {"textDocument": {"uri": URI, "version": 2}, "contentChanges": [{"text": changed}]},
    )
    (reply,) = send("statclaim/impact", {"textDocument": {"uri": URI}}, 4)
    result = reply["result"]
    kinds = {item["name"]: item["change"] for item in result["declarations"]}
    assert kinds["study"] == "changed directly"
    assert kinds["analysis"] == "affected through a dependency"
    assert [c["name"] for c in result["contracts"]] == ["analysis"]
    assert result["claims"][0]["change"].startswith("must be re-run")
    send("textDocument/didSave", {"textDocument": {"uri": URI}})
    (reply,) = send("statclaim/impact", {"textDocument": {"uri": URI}}, 5)
    assert reply["result"]["declarations"] == []


def test_impact_reports_contracts_that_stop_passing():
    broken = BASE.replace(
        "equal_proportions(model=study)", "proportion_difference(model=study, value=1/10)"
    )
    result = impact(compiled(BASE), compiled(broken))
    contract = {c["name"]: c for c in result["contracts"]}["analysis"]
    assert (contract["before"], contract["after"]) == ("satisfied", "no contract")
    assert "hypothesis_mismatch" in [d["code"] for d in result["new_diagnostics"]]
    untouched = impact(compiled(BASE), compiled(BASE + "\n# a comment\n"))
    assert not untouched["declarations"] and not untouched["contracts"]


def test_study_report_separates_established_assumed_and_open():
    compilation = compiled((ROOT / "examples/overallocated.stat").read_text())
    report = study_report(compilation, "overallocated.stat")
    assert report["all_derivations_checked"]
    assert [o["code"] for o in report["obligations"]] == ["allocation"]
    assert report["assumptions"] and report["claims"][0]["verification_requested"]
    text = report_markdown(report)
    for heading in (
        "## Assumptions to meet in the real study",
        "## Outstanding obligations",
        "## Requested claims",
        "## Justifications",
        "not a proof of any statistical guarantee",
    ):
        assert heading in text
    assert "Why it passed" in explanation_markdown(report["contracts"][0])


def test_cli_explain_report_and_impact(tmp_path, capsys):
    source = tmp_path / "study.stat"
    source.write_text(BASE)
    assert main(["explain", str(source), "--json"]) == 0
    assert json.loads(capsys.readouterr().out)[0]["checked"] is True
    assert main(["explain", str(source), "--name", "study"]) == 1
    capsys.readouterr()
    target = tmp_path / "report.md"
    assert main(["report", str(source), "--output", str(target)]) == 0
    assert "# Study contract report" in target.read_text()
    capsys.readouterr()
    other = tmp_path / "changed.stat"
    other.write_text(BASE.replace("alpha=1/20", "alpha=1/40"))
    assert main(["impact", str(source), str(other), "--json"]) == 0
    result = json.loads(capsys.readouterr().out)
    assert {item["name"] for item in result["declarations"]} == {"analysis"}


def named(path: str, name: str) -> dict:
    (entry,) = explain(compiled((ROOT / path).read_text()), name)
    assert entry["checked"], entry["problems"]
    return entry["derivation"]


def test_one_sample_and_two_stage_contracts_have_derivations():
    one = named("examples/one_sample.stat", "analysis")
    assert one["contract"] == "tests.binomial/binomial_test"
    assert [s["rule"] for s in one["steps"]][-1] == "one-sample-contract"
    two = named("examples/two_stage_posterior.stat", "analysis")
    assert two["contract"] == "designs.two_stage/two_stage_test"
    assert two["steps"][2]["facts"]["rule"]["kind"] == "posterior"
    for record, change in (
        (one, lambda d: d["subject"].update(null_rate="1")),
        (one, lambda d: d["subject"]["model"].update(n=0)),
        (two, lambda d: d["subject"]["rule"].update(prior_a=0)),
        (two, lambda d: d["subject"]["design"].update(n_stage2=500)),
        (two, lambda d: d.update(contract="tests.binomial/binomial_test")),
    ):
        altered = copy.deepcopy(record)
        change(altered)
        assert check_derivation(altered)


def test_planning_claims_rest_on_their_analysis_and_record_obligations():
    sizing = named("examples/planning.stat", "sizing")
    rules = [step["rule"] for step in sizing["steps"]]
    assert rules[:4] == ["same-model", "supported-null", "level-range", "analysis-contract"]
    assert "search-range" in rules and "error-budget" in rules
    assert sizing["steps"][rules.index("planning-contract")]["uses"] == [3, 4, 5, 6, 7]
    assert (
        "planning input" in sizing["assumptions"][-1]
        or "input for planning" in (sizing["assumptions"][-1])
    )
    searched = named("examples/two_stage_search.stat", "sizing")
    assert [s["rule"] for s in searched["steps"]][0] == "planning-point"
    strict = BASE.replace("let verification = verify(typeI(analysis))\n", "") + (
        "use planning\n"
        "let target = power_target(at=binomial_rates(p_control=1/10, p_treatment=2/5), "
        "minimum=4/5, maximum_typeI=1/100)\n"
        "let claim = meets(analysis=analysis, target=target)\n"
    )
    record = derivation(strict, "claim")
    assert [o["code"] for o in record["obligations"]] == ["typeI_target_not_established"]
    assert check_derivation(record) == []
    for change in (
        lambda d: d["subject"]["subject"]["target"]["at"].update(p_treatment="1/10"),
        lambda d: d["subject"]["subject"]["target"].update(minimum_power="0"),
        lambda d: d["subject"]["subject"]["target"].update(maximum_typeI="1/20"),
        lambda d: d["subject"]["subject"]["analysis"]["null"]["model"].update(n_control=7),
        lambda d: d["obligations"].clear(),
    ):
        altered = copy.deepcopy(record)
        change(altered)
        assert check_derivation(altered)


def test_the_checker_imports_data_and_no_function_from_statclaim():
    """The independent checker re-derives every fact with its own code: it may read rule
    statements, registries, assumption texts and limits, never call StatClaim's functions."""
    import ast
    import importlib
    import inspect

    source = (ROOT / "src/statclaim/derivation_checker.py").read_text()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.ImportFrom) and (node.module or "").startswith("statclaim"):
            module = importlib.import_module(node.module)
            for alias in node.names:
                value = getattr(module, alias.name)
                assert not inspect.isfunction(value), f"{node.module}.{alias.name} is a function"
        if isinstance(node, ast.Import):
            assert not any(a.name.startswith("statclaim") for a in node.names)
