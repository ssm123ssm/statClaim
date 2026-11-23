"""Round trips and socket contracts used by the browser against the Python engine."""

import json
import sys
from pathlib import Path

import pytest

from statclaim.language import MODULES, OPERATIONS
from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "studio"))
import api as editor  # noqa: E402
import server  # noqa: E402


@pytest.mark.parametrize(
    "path",
    sorted([*(ROOT / "examples").rglob("*.stat"), *(ROOT / "playground").glob("*.stat")]),
    ids=lambda p: p.stem,
)
def test_example_matches_compiler(path):
    document = editor.tutorial(path)
    source = Source(document["source"], path.name)
    compiled = compile_source(source)
    visual = editor.compile_document(source)
    assert visual["diagnostics"] == [d.to_dict() for d in compiled.diagnostics]
    assert visual["status"] == compiled.status
    assert not document["parse_errors"]
    assert document["imports"] == [statement["name"] for statement in document["uses"]]
    for statement in document["statements"]:
        node = statement["expression"]
        assert statement["start"] <= node["start"] < node["end"] == statement["end"]
    json.dumps(visual)


def test_every_module_the_pages_import_is_served():
    """A module the editor imports but the server does not serve breaks the page, not the tests."""
    import re

    pages = [name for name in editor.ASSETS if name.endswith((".js", ".html"))]
    for page in pages:
        text = (ROOT / "studio" / page).read_text(encoding="utf-8")
        for imported in re.findall(
            r"""from ['"]\./([\w.-]+\.js)['"]|import\(['"]\./([\w.-]+\.js)['"]\)"""
            r"""|new URL\(['"]([\w.-]+\.js)['"], import\.meta\.url\)""",
            text,
        ):
            name = next(filter(None, imported))
            assert name in editor.ASSETS, f"{page} imports {name}, which the server does not serve"


def test_manifest_includes_all_registry_entries_and_nominal_socket_types():
    manifest = editor.manifest()
    assert set(manifest["modules"]) == MODULES.keys()
    assert set(manifest["operations"]) == OPERATIONS.keys()
    for name, module in MODULES.items():
        assert set(manifest["modules"][name]) == {c.name for c in module.constructors}
    fisher = manifest["modules"]["tests.fisher"]["fisher"]
    assert fisher["accepted_results"]["design"] == ["StudyDesign"]
    assert fisher["accepted_results"]["null"] == ["Hypothesis"]
    assert "OutcomeModel" in manifest["modules"]["sampling"]["fixed"]["accepted_results"]["model"]


def test_actual_bindings_obey_domain_inheritance_and_staging():
    text = (ROOT / "examples/fields.stat").read_text()
    bindings = editor.compile_document(Source(text + "\nlet over = 2\n"))["bindings"]
    assert "design" in bindings["plan"]["accepts"]["tests.fisher"]["fisher"]
    assert "alpha" in bindings["declared_alpha"]["accepts"]["tests.fisher"]["fisher"]
    assert "fisher" not in bindings["over"]["accepts"].get("tests.fisher", {})
    assert bindings["decision"]["accepts"] == {}
    assert "level" in bindings["analysis"]["field_inputs"]["alpha"]
    assert bindings["verification"]["field_inputs"]["status"] == []
    assert "ClaimIR" in bindings["verification"]["field_inputs"]["claim"]
    assert bindings["evidence"]["fields"]["grade"] == "Option[string]"


def test_spans_preserve_unicode_comments_multiline_and_named_arguments():
    text = '# 🌍\r\nuse sampling # comment\r\nlet thing = f(\n["🌍", -1/2], x=g.a\n).b\n'
    document = editor.parse_document(Source(text, "work.stat"))
    assert not document["parse_errors"]
    (use,) = document["uses"]
    assert text[use["start"] : use["end"]] == "use sampling"
    outer = document["statements"][0]["expression"]
    pos, named = outer["children"][0]["children"]
    assert [v["literal"] for v in pos["children"]] == ['"🌍"', "-1/2"]
    assert named["argument"] == "x"
    assert text[named["start"] : named["end"]] == "g.a"
    extent = named["argument_span"]
    assert text[extent["start"] : extent["end"]] == "x=g.a"


def test_invalid_source_stays_editable_with_diagnostics():
    text = "let a = 3\nlet broken = ?\nlet b = a\n"
    doc = editor.parse_document(Source(text, "work.stat"))
    assert doc["source"] == text
    assert doc["parse_errors"][0]["source"]["path"] == "work.stat"
    assert [s["name"] for s in doc["statements"]] == ["a", "b"]


def test_run_reports_each_request_with_its_span(tmp_path):
    text = (ROOT / "examples/tutorial/04_observed_data.stat").read_text()
    text = "\n".join(line for line in text.splitlines() if "verify(" not in line) + "\n"
    result = editor.run_document(Source(text, "04.stat"), editor.Backend.local(tmp_path))
    (request,) = result["requests"]
    assert result["status"] == "calculated"
    assert (request["operation"], request["status"], request["decision"]) == (
        "calculate",
        "calculated",
        "reject_null",
    )
    assert request["source"]["line"] == 11
    assert request["name"] == "calculation"
    assert request["calculation"]["p_value"]
    json.dumps(result)


def test_run_returns_the_values_it_fills_in(tmp_path):
    text = (ROOT / "examples/one_sample.stat").read_text()
    text = "\n".join(line for line in text.splitlines() if "verify(" not in line) + "\n"
    result = editor.run_document(Source(text, "one_sample.stat"), editor.Backend.local(tmp_path))
    # Only fields read from a check's result; declared values are known without a run.
    assert result["values"] == {"recommended_n": 35, "critical_value": 12}


def test_a_recalculation_runs_no_proofs_and_leaves_nothing_behind(tmp_path):
    text = (ROOT / "examples/one_sample.stat").read_text()
    # A checkout with Lean: the proof is not run now, and keeps its last result in the page.
    with_lean = editor.Backend("server", tmp_path, True)
    result = editor.run_document(Source(text, "one_sample.stat"), with_lean, only="calculate")
    statuses = [(r["name"], r["status"]) for r in result["requests"]]
    assert statuses == [
        ("calculation", "calculated"),
        ("recommendation", "calculated"),
        ("verification", "not_executed"),
    ]
    assert result["values"]["recommended_n"] == 35
    assert result["run_directory"] is None
    assert not list(tmp_path.iterdir())


def test_run_does_nothing_for_an_invalid_file(tmp_path):
    result = editor.run_document(
        Source("let broken = ?\n", "x.stat"), editor.Backend.local(tmp_path)
    )
    assert result["status"] == "invalid"
    assert result["requests"] == []
    assert not list(tmp_path.iterdir())


def test_language_features_complete_and_hover():
    text = (ROOT / "examples/tutorial/01_first_claim.stat").read_text()
    items = editor.language_feature("complete", Source(text + "let z = fi", "x.stat"), 12, 10)
    assert {"fixed", "fisher"} <= {item["label"] for item in items["items"]}
    hover = editor.language_feature("hover", Source(text, "x.stat"), 7, 20)["markdown"]
    assert "equal_proportions(model: Model) -> Hypothesis" in hover
    assert editor.language_feature("hover", Source(text, "x.stat"), 0, 3)["markdown"] is None


def test_manifest_carries_choices_and_the_registry_wording_for_grades():
    manifest = editor.manifest()
    model = manifest["modules"]["models.two_arm_binomial"]["two_arm_binomial"]
    assert model["choices"]["better"] == ["higher", "lower"]
    assert manifest["parameter_choices"]["criterion"]
    assert manifest["evidence_grades"]["cited"]["meaning"].startswith("cited")
    assert "weakest" in manifest["program_statuses"]["cited"]


def test_each_value_reads_in_words():
    text = (ROOT / "examples/tutorial/01_first_claim.stat").read_text()
    bindings = editor.compile_document(Source(text, "x.stat"))["bindings"]
    assert bindings["study"]["reading"] == (
        "Two arms of 50 (control) and 50 (treatment), with a yes-or-no outcome"
    )
    assert bindings["analysis"]["reading"] == (
        "Fisher's exact test of p_treatment = p_control, at level 1/20 (5%)"
    )
    assert bindings["verification"]["reading"] == "Checks claim"
    cited = editor.compile_document(Source((ROOT / "examples/t_test.stat").read_text(), "t.stat"))
    assert cited["bindings"]["analysis"]["reading"].startswith("Two-sided pooled-variance t-test")


@pytest.mark.parametrize("path", sorted((ROOT / "examples").rglob("*.stat")), ids=lambda p: p.stem)
def test_reading_never_fails(path):
    editor.compile_document(Source(path.read_text(), path.name))


def test_explain_returns_checked_derivations():
    text = (ROOT / "examples/tutorial/01_first_claim.stat").read_text()
    entries = editor.explain_document(Source(text, "x.stat"), "analysis")["entries"]
    assert [entry["name"] for entry in entries] == ["analysis"]
    assert entries[0]["checked"]
    assert entries[0]["derivation"]["steps"][0]["rule"] == "same-model"
    assert editor.explain_document(Source("let x = 1 +", "x.stat"))["entries"] == []


def test_hints_follow_the_compiler_not_only_the_types():
    text = (ROOT / "examples/cited_power.stat").read_text()

    def fits(name):
        return editor.fits_document(Source(text), name)["fits"]

    # A continuous study is taken by its nulls and designs, and by t-tests through a design.
    measured = fits("measured")
    assert measured["sampling"]["fixed"] == {"inputs": ["model"]}
    assert measured["tests.t"]["t_test"] == {"inputs": ["design"], "via": "fixed"}
    assert not {"tests.fisher", "tests.survival", "tests.logistic"} & measured.keys()
    assert "equal_survival" not in measured.get("models.two_arm_survival", {})
    # A yes-or-no study is taken by Fisher's test, but not by the exact difference test,
    # which supports up to 120 per arm; this study has 150.
    responders = fits("responders")
    assert "fisher" in responders["tests.fisher"]
    assert not {"tests.t", "tests.difference"} & responders.keys()
    assert fits("pain")["multiplicity.bonferroni"]["bonferroni"] == {"inputs": ["analyses"]}
    assert fits("pain_power") == {} and fits("missing") == {}

    table = editor.block_fits()
    continuous = table["models.two_arm_continuous"]["two_arm_continuous"]
    assert "t_test" in continuous["tests.t"] and "tests.fisher" not in continuous
    assert "familywise" in table["multiplicity.bonferroni"]["bonferroni"]["multiplicity.bonferroni"]
    json.dumps(table)


def test_observational_studies_read_in_words_and_hint_their_own_test():
    path = ROOT / "examples/tutorial/23_observational_studies.stat"
    source = Source(path.read_text(), path.name)
    bindings = editor.compile_document(source)["bindings"]
    assert bindings["sampled"]["reading"] == (
        "150 cases of lung cancer and 300 controls, asked about smoking"
    )
    assert bindings["by_survey"]["reading"].startswith("Fisher's exact test of association")
    fits = editor.fits_document(source, "followed")["fits"]
    assert fits["tests.association"]["fisher_exact"] == {"inputs": ["design"], "via": "fixed"}
    assert not {"tests.fisher", "tests.t", "tests.randomisation"} & fits.keys()
    table = editor.block_fits()
    assert "fisher_exact" in table["models.observational"]["cohort"]["tests.association"]
    assert "tests.association" not in table["models.two_arm_binomial"]["two_arm_binomial"]


def test_cluster_planning_reads_in_words_and_is_hinted():
    path = ROOT / "examples/tutorial/31_cluster_power.stat"
    source = Source(path.read_text(), path.name)
    bindings = editor.compile_document(source)["bindings"]
    assert bindings["practice"]["reading"].endswith(
        "outcome, in 6 and 6 clusters; higher is better"
    )
    assert bindings["expected"]["reading"] == (
        "A mean difference of 5, with standard deviation 10 and intracluster correlation 1/20"
    )
    assert bindings["more_clinics"]["reading"] == (
        "From 4 to 40 clusters per arm, each of 20 participants"
    )
    assert bindings["bigger_clinics"]["reading"] == (
        "The declared clusters, with 2 to 500 participants in each"
    )
    fits = editor.fits_document(source, "analysis")["fits"]["planning"]
    assert fits["cluster_counts"] == {"inputs": ["analysis"]}
    assert fits["cluster_sizes"] == {"inputs": ["analysis"]}
    assert "equal_arm_sizes" not in fits
    table = editor.block_fits()
    for test in ("cluster_t_test", "cluster_proportion_t_test"):
        hinted = table["tests.cluster"][test]["planning"]
        assert {"cluster_counts", "cluster_sizes"} <= set(hinted), test
        assert "equal_arm_sizes" not in hinted, test
    assert "cluster_counts" not in table["tests.t"]["t_test"]["planning"]


def test_survival_times_read_in_words():
    path = ROOT / "examples/tutorial/32_survival_power.stat"
    bindings = editor.compile_document(Source(path.read_text(), path.name))["bindings"]
    assert bindings["expected"]["reading"] == (
        "Hazard ratio 7/10, control median 12; entry over 24, then 12 of follow-up; "
        "1/10 drop out by 12"
    )
    table = editor.block_fits()
    assert "power_target" in table["planning"]["exponential_survival"]["planning"]


def test_correlation_and_slope_read_in_words_and_are_hinted():
    path = ROOT / "examples/tutorial/33_correlation_power.stat"
    source = Source(path.read_text(), path.name)
    bindings = editor.compile_document(source)["bindings"]
    assert bindings["rho_target"]["reading"].startswith("Power of at least 4/5")
    assert bindings["expected"]["reading"] == (
        "A slope of 1/2 per unit of exposure, exposure SD 4, residual SD 15; covariates "
        "explain 1/10 of the exposure"
    )
    assert bindings["rho_sizes"]["reading"] == "Totals from 4 to 5000 participants"
    fits = editor.fits_document(source, "rho")["fits"]["planning"]
    assert fits["total_sizes"] == {"inputs": ["analysis"]}


def test_regression_planning_reads_in_words():
    path = ROOT / "examples/tutorial/34_regression_power.stat"
    bindings = editor.compile_document(Source(path.read_text(), path.name))["bindings"]
    assert bindings["trend_target"]["reading"].startswith("Power of at least 4/5")
    assert bindings["cohort_sizes_"]["reading"] == "From 10 to 5000 exposed, 2 unexposed for each"
    table = editor.block_fits()
    assert "power_target" in table["planning"]["odds_per_sd"]["planning"]


def test_two_means_read_in_words():
    path = ROOT / "examples/tutorial/33_correlation_power.stat"
    bindings = editor.compile_document(Source(path.read_text(), path.name))["bindings"]
    assert bindings["means"]["reading"] == (
        "Outcome mean 125 with exposure and 120 without, SD 15; 1/3 of participants exposed"
    )


def test_precision_reads_in_words():
    path = ROOT / "examples/tutorial/36_precision.stat"
    bindings = editor.compile_document(Source(path.read_text(), path.name))["bindings"]
    assert bindings["estimate"]["reading"] == "The exact interval for the prevalence"
    assert bindings["target"]["reading"] == "A 95% interval with a margin of error of at most 3/100"
    assert bindings["sure"]["reading"].endswith("with assurance 4/5")
    assert bindings["survey_point"]["reading"] == (
        "A proportion of 1/2; design effect 2; a population of 50000"
    )
    assert (
        bindings["ratio_sizes"]["reading"] == "Sizes from 10 to 5000, 2 of the other group for each"
    )
    table = editor.block_fits()
    assert "interval_sizes" in table["planning"]["planned_interval"]["planning"]


def test_survey_planning_reads_in_words():
    path = ROOT / "examples/tutorial/35_survey_power.stat"
    bindings = editor.compile_document(Source(path.read_text(), path.name))["bindings"]
    assert bindings["expected"]["reading"].endswith("1/5 of participants exposed; design effect 2")


def test_observational_planning_reads_in_words_and_is_hinted():
    path = ROOT / "examples/tutorial/30_pairs_and_rates_power.stat"
    source = Source(path.read_text(), path.name)
    bindings = editor.compile_document(source)["bindings"]
    assert bindings["expected"]["reading"] == "Rate ratio 2, with 1/4 of person-time exposed"
    assert bindings["pair_counts"]["reading"] == "From 150 to 400 pairs"
    assert bindings["pairs_target"]["reading"].startswith("Power of at least 4/5 at that point")
    fits = editor.fits_document(source, "pairs_test")["fits"]["planning"]
    assert fits["matched_sizes"] == {"inputs": ["analysis"]}
    assert fits["smallest_sample_size"] == {"inputs": ["candidates"], "via": "matched_sizes"}
    lesson = ROOT / "examples/tutorial/29_observational_power.stat"
    bindings = editor.compile_document(Source(lesson.read_text(), lesson.name))["bindings"]
    assert (
        bindings["expected"]["reading"]
        == "Exposed: 1/3 of cases and 1/5 of controls (odds ratio 2)"
    )
    assert bindings["sizes"]["reading"] == "From 50 to 200 cases, 2 controls for each"
    assert bindings["totals"]["reading"] == "Totals from 60 to 150 participants"
    table = editor.block_fits()
    assert "matched_sizes" in table["tests.association"]["mcnemar"]["planning"]
    assert "event_counts" in table["tests.association"]["rate_test"]["planning"]
    assert "total_sizes" in table["tests.association"]["fisher_exact"]["planning"]
    for point in ("risks", "exposure_prevalence", "outcome_prevalence", "discordant_pairs"):
        assert "power_target" in table["planning"][point]["planning"], point


@pytest.mark.parametrize(
    ("headers", "trusted"),
    [
        ({"Content-Type": "application/json"}, True),
        ({"Content-Type": "application/json", "Origin": "http://127.0.0.1:4180"}, True),
        ({"Content-Type": "application/json; charset=utf-8", "Origin": "http://localhost"}, True),
        ({"Content-Type": "text/plain"}, False),
        ({"Content-Type": "application/json", "Origin": "https://example.org"}, False),
        ({"Content-Type": "application/json", "Origin": "http://127.0.0.1.example.org"}, False),
        ({"Content-Type": "application/json", "Origin": "null"}, False),
    ],
)
def test_only_the_studio_page_may_call_the_api(headers, trusted):
    """Other websites open in the browser cannot start compilations or runs."""

    class Request:
        pass

    request = Request()
    request.headers = headers
    assert server.Editor.trusted(request) is trusted


def test_a_codespace_page_may_call_the_api(monkeypatch):
    class Server:
        server_address = ("127.0.0.1", 4180)

    class Request:
        server = Server()

    request = Request()
    forwarded = "https://studio-4180.app.github.dev"
    request.headers = {"Content-Type": "application/json", "Origin": forwarded}
    assert not server.Editor.trusted(request)
    monkeypatch.setenv("CODESPACE_NAME", "studio")
    monkeypatch.setenv("GITHUB_CODESPACES_PORT_FORWARDING_DOMAIN", "app.github.dev")
    assert server.Editor.trusted(request)
    request.headers = {**request.headers, "Origin": "https://other-4180.app.github.dev"}
    assert not server.Editor.trusted(request)


@pytest.mark.parametrize("backend", [editor.BROWSER, editor.Backend.local(Path("/nonexistent"))])
def test_without_lean_a_proof_says_it_needs_lean_and_the_rest_runs(backend, tmp_path):
    text = (ROOT / "examples/one_sample.stat").read_text()
    result = editor.run_document(Source(text, "one_sample.stat"), backend)
    statuses = {r["name"]: r["status"] for r in result["requests"]}
    assert statuses == {
        "calculation": "calculated",
        "recommendation": "calculated",
        "verification": "needs_lean",
    }
    (proof,) = [r for r in result["requests"] if r["status"] == "needs_lean"]
    assert "Lean" in proof["message"]
    assert ("Codespaces" in proof["message"]) == (backend.where == "browser")
    assert result["values"]["recommended_n"] == 35
    assert result["run_directory"] is None
    # The study as a whole is not established, as statclaim check reports it without Lean.
    assert result["status"] == "unresolved_obligation"


def test_the_capabilities_say_what_needs_lean_and_where_to_go():
    found = editor.capabilities(editor.BROWSER)
    assert found["where"] == "browser" and found["lean"] is False
    assert found["lean_operations"] == ["verify"]
    assert "Codespaces" in found["needs_lean"]
    links = found["links"]
    assert links["codespaces"].startswith("https://codespaces.new/")
    assert links["install"].startswith(links["repository"])
    assert links["studio"] == "https://ssm123ssm.github.io/statClaim/"


def test_the_article_programs_and_case_studies_are_served():
    """The studio lists them, so ?open=paper/<file> and ?open=copd/<file> can open them."""
    paper = editor.handle("GET", "paper", None, editor.BROWSER)[1]
    assert [doc["name"] for doc in paper] == sorted(
        path.name for path in (ROOT / "examples/paper").glob("*.stat")
    )
    assert "simon_design.stat" in [doc["name"] for doc in paper]
    studies = editor.handle("GET", "replication", None, editor.BROWSER)[1]
    assert {"copd/design_cited.stat", "copd/design_declared.stat", "copd/power.stat"} <= {
        doc["name"] for doc in studies
    }
    for doc in studies:
        assert doc["source"] == (ROOT / "replication" / doc["name"]).read_text()
        assert doc["parse_errors"] == []


@pytest.mark.parametrize(
    ("method", "path", "payload", "status"),
    [
        ("GET", "nothing", None, 404),
        ("POST", "nothing", {"source": ""}, 404),
        ("POST", "compile", ["not", "an", "object"], 400),
        ("POST", "compile", {"name": "x.stat"}, 400),
        ("POST", "run", {"source": "", "only": "verify"}, 400),
        ("POST", "compile", {"source": "#" * (editor.MAX_SOURCE + 1)}, 413),
    ],
)
def test_every_transport_gets_the_same_refusals(method, path, payload, status):
    assert editor.handle(method, path, payload, editor.BROWSER)[0] == status


def test_json_requests_are_answered_as_json():
    status, body = editor.handle_json(
        "POST", "compile", json.dumps({"source": "use sampling\n"}), editor.BROWSER
    )
    assert status == 200 and json.loads(body)["status"]
    assert editor.handle_json("POST", "compile", "{", editor.BROWSER)[0] == 400
