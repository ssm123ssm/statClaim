"""Cited observational tests: regression with covariates, correlation and complex surveys.

Their guarantees are cited, so nothing here starts Lean.
"""

import copy
import subprocess
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.observational import METHODS, SCALES, SURVEYS

ROOT = Path(__file__).resolve().parents[1]
USES = (
    "use models.observational\nuse sampling\nuse tests.association\nuse tests.regression\n"
    "use tests.correlation\nuse tests.survey\nuse estimation.observational\n"
)
STUDIES = {
    "case_control": "let study = case_control(cases=300, controls=600)\n",
    "cohort": "let study = cohort(exposed=200, unexposed=400)\n",
    "cross_sectional": "let study = cross_sectional(n=500)\n",
    "continuous": (
        'let study = cross_sectional(n=250, exposure_scale="continuous", '
        'outcome_scale="continuous")\n'
    ),
    "continuous_outcome": 'let study = cohort(n=400, outcome_scale="continuous")\n',
    "matched": "let study = matched_case_control(pairs=150)\n",
    "person_time": "let study = person_time_cohort()\n",
    "cluster_survey": 'let study = cross_sectional(n=12000, survey="cluster", clusters=400)\n',
    "weighted_survey": (
        'let study = cross_sectional(n=8000, survey="weighted", outcome_scale="continuous")\n'
    ),
}


def analysis(method, covariates=""):
    return (
        f"let analysis = {method}(design=fixed(model=study), null=no_association(model=study), "
        f"alpha=1/20{covariates})\n"
    )


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


FITS = {
    "case_control": {"logistic_association"},
    "cohort": {"logistic_association", "modified_poisson"},
    # Design-based methods also fit a simple random sample.
    "cross_sectional": {
        "logistic_association",
        "modified_poisson",
        "survey_logistic",
        "rao_scott_test",
    },
    "continuous": {
        "linear_association",
        "pearson_correlation",
        "spearman_correlation",
        "survey_linear",
    },
    "continuous_outcome": {"linear_association"},
    "matched": {"conditional_logistic"},
    "person_time": {"poisson_rate_regression"},
    "cluster_survey": {"survey_logistic", "rao_scott_test"},
    "weighted_survey": {"survey_linear"},
}


@pytest.mark.parametrize("study", FITS)
def test_each_study_takes_exactly_the_methods_that_fit_it(study):
    for key in METHODS:
        found = codes(STUDIES[study] + analysis(key))
        if key in FITS[study]:
            assert found == [], (study, key, found)
        else:
            assert found and found[0] in ("type", "not_estimable", "complex_sample"), (study, key)


def test_every_fitting_method_has_a_checked_compatibility_derivation():
    for study, keys in FITS.items():
        for key in keys:
            compilation = compiled(STUDIES[study] + analysis(key))
            record = next(d for d in compilation.derivations if d.name == "analysis").to_dict()
            assert record["contract"] == f"{METHODS[key].module}/{key}"
            assert record["scope"] == "compatibility" and record["guarantee"] is None
            assert check_derivation(record) == [], (study, key)


def test_the_checker_rejects_a_method_that_does_not_fit():
    record = next(
        d
        for d in compiled(STUDIES["case_control"] + analysis("logistic_association")).derivations
        if d.name == "analysis"
    ).to_dict()
    changed = copy.deepcopy(record)
    changed["subject"]["design"]["model"]["study"] = "matched_case_control"
    assert check_derivation(changed) != []
    changed = copy.deepcopy(record)
    changed["assumptions"] = changed["assumptions"][1:]
    assert check_derivation(changed) != []


def test_covariates_are_named_once_and_only_where_a_method_takes_them():
    good = STUDIES["case_control"] + analysis(
        "logistic_association", ', adjusted_for=["age", "sex"]'
    )
    compilation = compiled(good)
    assert compilation.status == "elaborated"
    value = next(b.value for b in compilation.program.bindings if b.name == "analysis")
    assert value.covariates == ("age", "sex")
    assert codes(
        STUDIES["case_control"] + analysis("logistic_association", ', adjusted_for=["age", "age"]')
    ) == ["domain"]
    assert codes(
        STUDIES["case_control"] + analysis("logistic_association", ', adjusted_for=["outcome"]')
    ) == ["domain"]
    assert codes(
        STUDIES["continuous"] + analysis("pearson_correlation", ', adjusted_for=["age"]')
    ) == ["arguments"]


@pytest.mark.parametrize(
    "declaration,fragment",
    [
        ('cross_sectional(n=100, survey="cluster")', "how many clusters"),
        ("cross_sectional(n=100, clusters=10)", 'survey="cluster"'),
        ('cross_sectional(n=100, survey="cluster", clusters=200)', "at most the number"),
        ('cross_sectional(n=100, outcome_scale="ordinal")', "outcome_scale must be"),
        ('cross_sectional(n=100, survey="quota")', "survey must be"),
    ],
)
def test_survey_and_scale_declarations_are_validated(declaration, fragment):
    diagnostics = compiled(f"let study = {declaration}\n").diagnostics
    assert [d.code for d in diagnostics] == ["domain"] and fragment in diagnostics[0].message


@pytest.mark.parametrize(
    "study,declaration,code",
    [
        ("continuous", analysis("fisher_exact"), "type"),
        ("cluster_survey", analysis("fisher_exact"), "complex_sample"),
        (
            "cluster_survey",
            "let seen = observed_table(model=study, exposed_cases=1, exposed_noncases=1, "
            "unexposed_cases=1, unexposed_noncases=11997)\n",
            "complex_sample",
        ),
        (
            "cluster_survey",
            "let p = prevalence(model=study, cases=100, level=19/20)\n",
            "complex_sample",
        ),
        (
            "continuous_outcome",
            "let p = cumulative_incidence(model=study, cases=10, level=19/20)\n",
            "type",
        ),
    ],
)
def test_proved_methods_refuse_continuous_variables_and_complex_samples(study, declaration, code):
    assert codes(STUDIES[study] + declaration)[0] == code


def test_too_few_clusters_and_participants_are_refused():
    few = 'let study = cross_sectional(n=1000, survey="cluster", clusters=10)\n'
    assert codes(few + analysis("survey_logistic")) == ["domain"]
    tiny = (
        'let study = cross_sectional(n=3, exposure_scale="continuous", '
        'outcome_scale="continuous")\n'
    )
    assert codes(tiny + analysis("pearson_correlation")) == ["domain"]


def test_a_refusal_names_the_methods_that_fit():
    message = compiled(STUDIES["matched"] + analysis("logistic_association")).diagnostics[0].message
    assert "Methods that fit this study: conditional_logistic." in message


def test_a_cited_claim_reports_its_grade_scope_and_assumptions(tmp_path):
    text = (
        STUDIES["case_control"]
        + analysis("logistic_association", ', adjusted_for=["age"]')
        + "let claim = verify(typeI(analysis))\nlet grade = claim.evidence.grade\n"
    )
    report = check_source(
        Source(USES + text, "study.stat"), project=tmp_path, output=tmp_path / "r"
    )
    assert report["status"] == "cited" and report["values"]["grade"] == "cited"
    details = report["requests"][0]["report"]
    assert details["target_property"].startswith("About exposure and outcome, adjusted for age")
    assert "No bound is claimed at the declared sample sizes" in details["target_property"]
    assert {item["id"] for item in details["assumptions"]} >= {"logit_model", "prespecified_model"}
    assert details["limitations"][0].startswith("The bound concerns association")


def test_registry_values_are_documented_choices():
    from statclaim.reference import PARAMETER_CHOICES

    assert set(PARAMETER_CHOICES["outcome_scale"]) == set(SCALES)
    assert set(PARAMETER_CHOICES["survey"]) == set(SURVEYS)
    for method in METHODS.values():
        assert method.grade == "cited" and method.references
        assert all(assumption.id for assumption in method.assumptions)


def test_the_lesson_and_examples_compile():
    for name in (
        "examples/tutorial/27_covariates_and_surveys.stat",
        "examples/regression.stat",
        "examples/complex_survey.stat",
    ):
        path = ROOT / name
        compilation = compile_source(Source(path.read_text(), str(path)))
        assert compilation.status == "elaborated", (name, compilation.diagnostics)
        assert all(check_derivation(d.to_dict()) == [] for d in compilation.derivations)
