"""Hypothesis semantics, analysis contracts, guidance, and backend-free rejection."""

import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.language import (
    MODULES,
    AnalysisIR,
    HypothesisIR,
    LocatedValue,
    ModelIR,
    PlanIR,
    elaborate,
    module_catalog,
)
from statclaim.language_compiler import compile_source
from statclaim.language_contracts import FISHER_CONTRACT, HypothesisContract
from statclaim.language_runner import check_source
from statclaim.language_syntax import LanguageError, Source, Span
from statclaim.lsp_features import Document

ROOT = Path(__file__).resolve().parents[1]
BASE = (ROOT / "tests/fixtures/fisher.stat").read_text()


def replace_null(expression):
    return BASE.replace("equal_proportions(model=study)", expression)


@pytest.mark.parametrize("value", ["0.10", "1/10", "-0.10", "-1/10", "1", "-1"])
def test_shifted_nulls_are_valid_objects_with_exact_meaning(value):
    text = replace_null(f"proportion_difference(model=study, value={value})")
    text = text[: text.index("let analysis")]
    text += "let meaning = null.statement\nlet bound = null.value\n"
    result = check_source(Source(text), project=ROOT, elaborate_only=True)
    assert result["status"] == "elaborated"
    assert result["requests"] == []
    assert result["values"]["null"]["predicate"] == "proportion_difference"
    assert result["values"]["bound"] == str(Fraction(value))
    assert result["values"]["meaning"] == f"p_treatment - p_control = {Fraction(value)}"
    assert result["certificate_issued"] is False


@pytest.mark.parametrize(
    "constructor,value",
    [
        ("proportion_difference", "0.10"),
        ("proportion_difference", "-0.1"),
        ("proportion_difference_at_most", "0"),
        ("proportion_difference_at_most", "0.10"),
    ],
)
def test_same_model_different_null_is_rejected_before_execution(
    constructor, value, monkeypatch, tmp_path
):
    def forbidden(*args, **kwargs):
        pytest.fail("a hypothesis mismatch must not execute calculations, processes, or Lean")

    monkeypatch.setattr(subprocess, "Popen", forbidden)
    monkeypatch.setattr("statclaim.language_runner.verify_design_only", forbidden)
    monkeypatch.setattr("statclaim.language_runner.test_design", forbidden)
    text = replace_null(f"{constructor}(model=study, value={value})")
    for fast in (True, False):
        report = check_source(
            Source(text, "mismatch.stat"),
            project=ROOT,
            elaborate_only=fast,
            output=None if fast else tmp_path / "unused",
        )
        assert report["status"] == "invalid"
        assert report["backend_invoked"] is False
        assert report["certificate_issued"] is False
        assert "run_directory" not in report
        diagnostic = report["diagnostics"][0]
        assert diagnostic["code"] == "hypothesis_mismatch"
        assert diagnostic["source"]["line"] == 9
        assert diagnostic["related"][0]["source"]["line"] == 8
        assert "Declared null:" in diagnostic["message"]
        assert "Supported null:" in diagnostic["message"]
        assert "replacing the null changes the statistical question" in diagnostic["message"]
        assert "not a proof that your null is false" in diagnostic["message"]
    assert not (tmp_path / "unused").exists()


@pytest.mark.parametrize("value", ["0", "0.00", "0/17"])
def test_zero_difference_alias_matches_the_existing_canonical_null(value):
    expected = compile_source(Source(BASE))
    actual = compile_source(Source(replace_null(f"proportion_difference(study, {value})")))
    assert actual.diagnostics == ()
    assert actual.program.requests[0].claim.subject == expected.program.requests[0].claim.subject
    assert (
        actual.program.to_dict()["requests"][0]["claim"]
        == expected.program.to_dict()["requests"][0]["claim"]
    )


@pytest.mark.parametrize("value,code", [('"0.1"', "type"), ("1.01", "domain"), ("-1.01", "domain")])
def test_difference_values_are_exact_and_within_the_declared_domain(value, code):
    compilation = compile_source(Source(replace_null(f"proportion_difference(study, {value})")))
    assert compilation.diagnostics[0].code == code


def test_zero_inequality_stays_distinct_and_model_mismatch_is_a_separate_error():
    text = replace_null("proportion_difference_at_most(study, 0)")
    compilation = compile_source(Source(text))
    null = next(b.value for b in compilation.program.bindings if b.name == "null")
    assert null.predicate == "proportion_difference_at_most"
    assert null.statement == "p_treatment - p_control <= 0"
    assert compilation.diagnostics[0].code == "hypothesis_mismatch"
    text = text.replace("let null", "let other = two_arm_binomial(20, 30)\nlet null")
    compilation = compile_source(
        Source(
            text.replace(
                "proportion_difference_at_most(study", "proportion_difference_at_most(other"
            )
        )
    )
    assert compilation.diagnostics[0].code == "model_mismatch"
    assert "(100, 100)" in compilation.diagnostics[0].message
    assert "(20, 30)" in compilation.diagnostics[0].message


def test_alias_and_field_projection_diagnostics_keep_original_hypothesis_location():
    text = replace_null("proportion_difference(study, 0.10)")
    text = text.replace("let analysis", "let alias = null\nlet analysis").replace(
        "null=null", "null=alias"
    )
    compilation = compile_source(Source(text))
    diagnostic = compilation.diagnostics[0]
    assert diagnostic.related[0].span.line == 8
    # A projected null from a valid analysis still needs the receiving design's model.
    text = BASE + "let other = two_arm_binomial(20, 30)\nlet other_plan = fixed(other)\n"
    text += "let invalid = fisher(other_plan, analysis.null, 0.05)\n"
    diagnostic = compile_source(Source(text)).diagnostics[0]
    assert diagnostic.code == "model_mismatch"
    assert diagnostic.related[0].span.line == 8


def test_contracts_are_registry_metadata_and_can_describe_other_supported_nulls():
    constructor = next(c for c in MODULES["tests.fisher"].constructors if c.name == "fisher")
    assert constructor.hypothesis_contract is FISHER_CONTRACT
    catalog = next(m for m in module_catalog() if m["module"] == "tests.fisher")
    assert catalog["contracts"]["fisher"]["supported_predicates"] == ["equal_proportions"]
    model = ModelIR(100, 100)
    plan = PlanIR(model, "fixed")
    null = HypothesisIR(model, "proportion_difference", Fraction(1, 10))
    span = Span("test.stat", 1, 1, 1, 2)
    arguments = {"design": LocatedValue(plan, span), "null": LocatedValue(null, span)}
    contract = HypothesisContract(
        ("proportion_difference",), "A shifted null", "Use the matching contract."
    )
    contract.check("example_analysis", arguments)
    with pytest.raises(LanguageError):
        FISHER_CONTRACT.check("fisher", arguments)
    with pytest.raises(ValueError, match="equal-proportions"):
        AnalysisIR(plan, null, Fraction(1, 20))


def test_lsp_hovers_related_locations_and_claims_view_share_the_semantics(monkeypatch):
    monkeypatch.setattr(
        subprocess, "Popen", lambda *a, **k: pytest.fail("editing invoked a process")
    )
    text = replace_null("proportion_difference(study, 0.10)")
    document = Document("file:///mismatch.stat", 1, text)
    diagnostic = document.diagnostics()[0]
    assert diagnostic["code"] == "hypothesis_mismatch"
    assert diagnostic["relatedInformation"][0]["location"]["range"]["start"]["line"] == 7
    position = document.mapping.position(text.index("null =") + 1)
    assert "p_treatment - p_control = 1/10" in document.hover(position)["contents"]["value"]
    position = document.mapping.position(text.index("fisher(design"))
    assert "Supported null:" in document.hover(position)["contents"]["value"]
    inspection = document.inspection()
    assert inspection["status"] == "invalid"
    assert inspection["diagnostics"][0]["relatedInformation"]
    completions = Document(
        "file:///mismatch.stat", 1, "use models.two_arm_binomial\nlet x = proportion_"
    )
    assert {
        item["label"]
        for item in completions.completion(completions.mapping.position(len(completions.text)))[
            "items"
        ]
    } == {"proportion_difference", "proportion_difference_at_most"}


def test_standalone_hypotheses_do_not_assert_truth_or_trigger_proofs():
    text = replace_null("proportion_difference(study, 0.10)")
    text = text[: text.index("let analysis")]
    program, errors = elaborate(Source(text))
    assert errors == [] and program.requests == ()
    assert (
        compile_source(Source(text + "let checked = verify(null)\n")).diagnostics[0].code == "type"
    )
