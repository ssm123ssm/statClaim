import json
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.design import load_design
from statclaim.family import load_family
from statclaim.language import (
    MODULES,
    OPERATION_BACKENDS,
    OPERATIONS,
    AnalysisIR,
    AssignmentIR,
    Constructor,
    FamilyIR,
    ModelIR,
    Module,
    OutcomeIR,
    Parameter,
    elaborate,
    module_catalog,
    two_arm_model,
)
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source, parse
from statclaim.verification import VerificationError, design_payload, family_payload

ROOT = Path(__file__).resolve().parents[1]


def binomial(n_control, n_treatment):
    return two_arm_model(AssignmentIR(n_control, n_treatment), OutcomeIR("binary"))


def source(name="fisher.stat"):
    folder = "tests/fixtures" if name == "fisher.stat" else "examples"
    return Source((ROOT / folder / name).read_text(), name)


def test_fisher_language_lowers_to_existing_canonical_design():
    program, diagnostics = elaborate(source())
    assert diagnostics == []
    analysis = program.requests[0].claim.subject
    assert isinstance(analysis, AnalysisIR)
    assert design_payload(analysis.lower()) == design_payload(
        load_design(ROOT / "examples/fixed_sample.toml")
    )
    assert program.bindings[-1].dependencies == ("plan", "null")
    assert program.to_dict()["bindings"][-1]["argument_sources"]["alpha"]["line"] == 9


def test_family_language_lowers_to_existing_canonical_family():
    program, diagnostics = elaborate(source("two_outcomes.stat"))
    assert diagnostics == []
    family = program.requests[0].claim.subject
    assert isinstance(family, FamilyIR)
    assert family_payload(family.lower()) == family_payload(
        load_family(ROOT / "examples/two_outcomes.toml")
    )


def test_module_registry_extends_vocabulary_without_parser_changes(monkeypatch):
    constructor = Constructor(
        "copy_model",
        (Parameter("model", ModelIR),),
        "Model",
        lambda args, span: args["model"].value,
    )
    monkeypatch.setitem(MODULES, "example.reuse", Module("example.reuse", (constructor,)))
    code = source().text + "use example.reuse\nlet copied = copy_model(study)\n"
    program, diagnostics = elaborate(Source(code))
    assert diagnostics == []
    assert program.bindings[-1].value == binomial(100, 100)
    assert "copy_model(model) -> Model" in module_catalog()[-1]["constructors"]


@pytest.mark.parametrize("value", ["0.025", "1 / 40", "1/40"])
def test_exact_levels_and_constant_references(value):
    code = source().text.replace("let study", f"let threshold = {value}\nlet study")
    code = code.replace("alpha=1/20", "alpha=threshold")
    program, diagnostics = elaborate(Source(code))
    assert diagnostics == []
    assert program.requests[0].claim.subject.alpha == Fraction(1, 40)


@pytest.mark.parametrize(
    "before,after,code,line",
    [
        ("use tests.fisher\n", "", "unknown_constructor", 8),
        ("models.two_arm_binomial", "models.missing", "unknown_module", 2),
        ("n_control=100", "n_control=0", "domain", 6),
        ("n_control=100", "n_control=1.5", "type", 6),
        ("n_control=100", 'n_control="100"', "type", 6),
        ("n_control=100", "n_control=unknown", "unknown_name", 6),
        ("alpha=1/20", "alpha=-1/20", "domain", 9),
        ("alpha=1/20", "alpha=2", "domain", 9),
        ("alpha=1/20", 'alpha="0.05"', "domain", 9),
        ("null=null", "null=study", "type", 9),
        ("design=plan", "design=study", "type", 9),
        ("alpha=1/20", "alpha=1/20, alpha=1/40", "arguments", 9),
        ("alpha=1/20", "typo=1/20", "arguments", 9),
        (", alpha=1/20", "", "arguments", 9),
        ("verify typeI(analysis)", "verify analysis", "type", 11),
        ("verify typeI(analysis)", "calculate typeI(analysis)", "type", 11),
    ],
)
def test_source_located_semantic_errors(before, after, code, line):
    _, diagnostics = elaborate(Source(source().text.replace(before, after), "invalid.stat"))
    assert diagnostics[0].code == code
    assert diagnostics[0].span.path == "invalid.stat"
    assert diagnostics[0].span.line == line
    assert diagnostics[0].span.column > 0


def test_null_from_incompatible_model_is_rejected():
    code = source().text.replace("let null", "let other = two_arm_binomial(4, 4)\nlet null")
    code = code.replace("equal_proportions(model=study)", "equal_proportions(model=other)")
    _, diagnostics = elaborate(Source(code))
    assert diagnostics[0].code == "model_mismatch"


@pytest.mark.parametrize(
    "tail",
    [
        "let repeated = two_arm_binomial(",
        "let repeated = [study,",
        'let repeated = "unterminated',
        "let repeated = 1/0",
        "let repeated = two_arm_binomial(1, n_treatment=2, 3)",
        "let repeated = 1 + 2",
        "let repeated = study; verify typeI(analysis)",
    ],
)
def test_incomplete_or_unsupported_syntax_has_diagnostics(tail):
    _, diagnostics = elaborate(Source(source().text + tail))
    assert diagnostics


def test_bindings_cannot_be_redefined_and_dependencies_are_invalidated():
    _, diagnostics = elaborate(Source(source().text + "let study = two_arm_binomial(4,4)\n"))
    assert diagnostics[-1].code == "redefinition"
    program, diagnostics = elaborate(Source(source().text.replace("n_control=100", "n_control=0")))
    assert program.requests == ()
    assert any(d.code == "dependency" for d in diagnostics)


def test_multiline_calls_comments_trailing_commas_and_positional_arguments():
    code = """use models.two_arm_binomial
let model = two_arm_binomial(
    4, # control size
    n_treatment=8,
)
"""
    program, diagnostics = elaborate(Source(code))
    assert diagnostics == []
    assert program.bindings[0].value == binomial(4, 8)


def test_invalid_observation_points_to_the_count():
    code = source("fisher_result.stat").text.replace(
        "control_successes=10", "control_successes=101"
    )
    _, diagnostics = elaborate(Source(code))
    assert diagnostics[0].code == "domain"
    assert diagnostics[0].span.line == 9
    assert "between 0 and 100" in diagnostics[0].message


@pytest.mark.parametrize(
    "before,after,code",
    [
        ("[primary_outcome, secondary_outcome]", "[primary_outcome]", "family_size"),
        (
            "[primary_outcome, secondary_outcome]",
            "[primary_outcome, primary_outcome]",
            "duplicate_analysis",
        ),
        ("[primary_outcome, secondary_outcome]", "[study, secondary_outcome]", "type"),
        ('"binomial_marginals"', '"assume_independent"', "sampling_contract"),
    ],
)
def test_family_type_and_contract_diagnostics(before, after, code):
    _, diagnostics = elaborate(Source(source("two_outcomes.stat").text.replace(before, after)))
    assert diagnostics[0].code == code


def test_entire_file_is_checked_before_backend_or_artifact_writes(monkeypatch, tmp_path):
    monkeypatch.setattr(
        "statclaim.language_runner.verify_design_only",
        lambda *a, **k: pytest.fail("backend must not run"),
    )
    report = check_source(
        Source(source().text + "let bad = unknown\n"), project=ROOT, output=tmp_path / "unused"
    )
    assert report["status"] == "invalid"
    assert report["backend_invoked"] is False
    assert report["certificate_issued"] is False
    assert not (tmp_path / "unused").exists()


@pytest.mark.parametrize(
    "name,code,line",
    [("overallocated.stat", "allocation", 13), ("adaptive.stat", "sampling_scope", 6)],
)
def test_known_obligations_have_source_locations_without_backend(
    name, code, line, monkeypatch, tmp_path
):
    monkeypatch.setattr(
        "statclaim.language_runner.verify_design_only", lambda *a, **k: pytest.fail("backend")
    )
    monkeypatch.setattr(
        "statclaim.language_runner.verify_family", lambda *a, **k: pytest.fail("backend")
    )
    for fast in (True, False):
        report = check_source(source(name), project=ROOT, elaborate_only=fast)
        assert report["status"] == "unresolved_obligation"
        assert report["diagnostics"][0]["code"] == code
        assert report["diagnostics"][0]["source"]["line"] == line
        assert report["backend_invoked"] is False
        assert report["certificate_issued"] is False
        assert "run_directory" not in report


def test_fast_mode_displays_planned_claim_and_writes_nothing(monkeypatch):
    monkeypatch.setattr(
        "statclaim.language_runner.verify_design_only", lambda *a, **k: pytest.fail("backend")
    )
    report = check_source(source(), project=ROOT, elaborate_only=True)
    assert report["status"] == "elaborated"
    assert report["requests"][0]["status"] == "planned"
    assert "<= 1/20" in render_report(report, source())
    assert "run_directory" not in report


def test_a_run_can_recalculate_without_building_proofs(monkeypatch, tmp_path):
    import statclaim.language_runner as runner

    original = runner._run_request

    def calculations_only(request, *args, **kwargs):
        if request.operation != "calculate":
            pytest.fail("a proof was built")
        return original(request, *args, **kwargs)

    monkeypatch.setattr(runner, "_run_request", calculations_only)
    text = (ROOT / "examples/one_sample.stat").read_text()
    report = check_source(
        Source(text, "one_sample.stat"),
        project=ROOT,
        output=tmp_path / "run",
        operations={"calculate"},
    )
    statuses = {r["operation"]: r["status"] for r in report["requests"]}
    assert statuses == {"calculate": "calculated", "verify": "not_executed"}
    assert report["values"]["recommended_n"] == 35
    assert not report["certificate_issued"]


def test_source_code_and_shell_commands_are_never_executed(tmp_path):
    marker = tmp_path / "unexpected"
    code = source().text + f'let malicious = __import__("os").system("touch {marker}")\n'
    report = check_source(Source(code), project=ROOT, output=tmp_path / "output")
    assert report["status"] == "invalid"
    assert not marker.exists()
    assert not (tmp_path / "output").exists()


def test_calculation_has_no_formal_status_and_retains_source(tmp_path):
    original = source("fisher_result.stat")
    code = Source(original.text.replace("verify result(data)\n", ""), original.path)
    report = check_source(code, project=ROOT, output=tmp_path / "run")
    assert report["status"] == "calculated"
    assert report["certificate_issued"] is False
    assert report["backend_invoked"] is False
    assert report["requests"][0]["report"]["calculation"]["p_value"]["fraction"] == (
        "19912805355158606332329/2341699062001756564467919"
    )
    assert (tmp_path / "run/Source.stat").read_text() == code.text
    assert (tmp_path / "run/run.json").is_file()


def test_backend_failure_is_a_source_located_unresolved_claim(monkeypatch, tmp_path):
    def failed(*args, **kwargs):
        raise VerificationError("proof", "Controlled backend failure.")

    monkeypatch.setattr("statclaim.report.certify_design", failed)
    report = check_source(source(), project=ROOT, output=tmp_path / "run")
    assert report["status"] == "unresolved_obligation"
    assert report["certificate_issued"] is False
    assert report["diagnostics"][0]["source"]["line"] == 11


def test_changed_source_during_execution_is_marked_stale(monkeypatch, tmp_path):
    path = tmp_path / "study.stat"
    original = source("fisher_result.stat").text.replace("verify result(data)\n", "")
    path.write_text(original)
    import statclaim.language_runner as runner

    original_calculation = runner.test_design

    def mutate(*args, **kwargs):
        result = original_calculation(*args, **kwargs)
        path.write_text(original.replace("alpha=1/20", "alpha=1/40"))
        return result

    monkeypatch.setattr(runner, "test_design", mutate)
    report = check_source(Source(original, str(path)), project=ROOT, output=tmp_path / "run")
    assert report["status"] == "stale_source"
    assert report["diagnostics"][-1]["code"] == "source_changed"
    assert (tmp_path / "run/Source.stat").read_text() == original


def test_cli_fast_mode_and_module_discovery(capsys):
    assert (
        main(["check", str(ROOT / "tests/fixtures/fisher.stat"), "--elaborate-only", "--json"]) == 0
    )
    report = json.loads(capsys.readouterr().out)
    assert report["status"] == "elaborated"
    assert report["certificate_issued"] is False
    assert main(["modules", "--json"]) == 0
    assert len(json.loads(capsys.readouterr().out)) == len(MODULES)


def test_cli_invalid_syntax_returns_two_and_a_readable_location(tmp_path, capsys):
    path = tmp_path / "bad.stat"
    path.write_text("let broken = [\n")
    assert main(["check", str(path)]) == 2
    output = capsys.readouterr().out
    assert str(path) + ":2:1:" in output
    assert "error [syntax]" in output


def test_existing_output_directory_is_preserved(tmp_path):
    output = tmp_path / "run"
    output.mkdir()
    (output / "keep").write_text("keep")
    with pytest.raises(FileExistsError):
        check_source(source(), project=ROOT, output=output)
    assert (output / "keep").read_text() == "keep"


def test_fast_mode_rejects_output_argument(tmp_path):
    with pytest.raises(ValueError, match="does not write"):
        check_source(source(), project=ROOT, output=tmp_path / "run", elaborate_only=True)


def test_new_source_has_new_semantics_and_no_cached_evidence():
    first = check_source(source(), project=ROOT, elaborate_only=True)
    edited = Source(source().text.replace("alpha=1/20", "alpha=1/40"))
    second = check_source(edited, project=ROOT, elaborate_only=True)
    assert first["source"]["sha256"] != second["source"]["sha256"]
    assert second["requests"][0]["report"]["analysis"]["alpha"] == "1/40"
    assert second["certificate_issued"] is False


def test_parse_error_recovery_preserves_later_declarations():
    statements, diagnostics = parse(Source("let bad = @\nlet good = 1\n"))
    assert diagnostics
    assert statements[-1].name == "good"


def test_crlf_source_snapshot_preserves_exact_bytes(tmp_path):
    original = source("fisher_result.stat").text.replace("verify result(data)\n", "")
    text = original.replace("\n", "\r\n")
    path = tmp_path / "study.stat"
    path.write_bytes(text.encode())
    report = check_source(Source(text, str(path)), project=ROOT, output=tmp_path / "run")
    assert report["status"] == "calculated"
    assert (tmp_path / "run/Source.stat").read_bytes() == path.read_bytes()


def test_deleting_source_during_execution_marks_the_run_stale(monkeypatch, tmp_path):
    path = tmp_path / "study.stat"
    text = source("fisher_result.stat").text.replace("verify result(data)\n", "")
    path.write_text(text)
    import statclaim.language_runner as runner

    original = runner.test_design

    def remove(*args, **kwargs):
        result = original(*args, **kwargs)
        path.unlink()
        return result

    monkeypatch.setattr(runner, "test_design", remove)
    report = check_source(Source(text, str(path)), project=ROOT, output=tmp_path / "run")
    assert report["status"] == "stale_source"


def test_edited_archive_during_execution_is_detected(monkeypatch, tmp_path):
    text = source("fisher_result.stat").text.replace("verify result(data)\n", "")
    import statclaim.language_runner as runner

    original = runner.test_design

    def mutate(*args, **kwargs):
        result = original(*args, **kwargs)
        (tmp_path / "run/Source.stat").write_text("changed\n")
        return result

    monkeypatch.setattr(runner, "test_design", mutate)
    report = check_source(Source(text), project=ROOT, output=tmp_path / "run")
    assert report["status"] == "stale_source"
    assert report["diagnostics"][-1]["code"] == "snapshot_changed"


def test_every_operation_says_whether_it_needs_lean():
    """The web studio runs what needs no Lean and says when a check needs it; a new
    operation must say which it is."""
    assert set(OPERATION_BACKENDS) == set(OPERATIONS)
    assert set(OPERATION_BACKENDS.values()) <= {"lean", "python"}
