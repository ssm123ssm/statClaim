"""Power of the survey tests through the design effect."""

import copy
import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.association_power import (
    logistic_groups_power,
    survey_groups_power,
    survey_slope_power,
    survey_trend_power,
)

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/survey_power_r.json").read_text())
LESSON = ROOT / "examples/tutorial/35_survey_power.stat"
SURVEY = (
    "use models.observational\nuse sampling\nuse tests.survey\nuse tests.regression\n"
    "use planning\n"
    'let national = cross_sectional(n=12000, exposure="e", outcome="o", survey="cluster", '
    "clusters=400)\n"
    "let table = rao_scott_test(design=fixed(model=national), "
    "null=no_association(model=national), alpha=1/20)\n"
    'let simple = cross_sectional(n=500, exposure="e", outcome="o")\n'
    "let logistic = logistic_association(design=fixed(model=simple), "
    "null=no_association(model=simple), alpha=1/20)\n"
)
POINT = "outcome_prevalence(unexposed=1/10, prevalence_ratio=6/5, exposed_share=1/5{})"


def _f(text):
    return float(Fraction(text))


def target(extra=", design_effect=2"):
    return f"power_target(at={POINT.format(extra)}, minimum=4/5, maximum_typeI=1/20)"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("case", FIXTURE["groups"], ids=lambda c: c["deff"])
def test_two_groups_reach_the_target_at_deff_times_the_simple_size(case):
    """R values from replication/comparison/survey_power_r.R; R is not needed here."""
    point = {
        "p_reference": _f(case["p_reference"]),
        "p_other": _f(case["p_other"]),
        "share_other": _f(case["share_other"]),
        "design_effect": _f(case["deff"]),
    }
    power = survey_groups_power(point, case["survey_n"], 0, 0.05).power
    assert power == pytest.approx(_f(case["power"]), abs=1e-9)
    # It is the simple-random formula at n / deff.
    simple = {key: value for key, value in point.items() if key != "design_effect"}
    assert power == pytest.approx(
        logistic_groups_power(simple, case["simple_random_n"], 0, 0.05).power, abs=1e-12
    )


@pytest.mark.parametrize("case", FIXTURE["trends"], ids=lambda c: c["deff"])
def test_a_measured_exposure_reaches_the_target_at_deff_times_the_simple_size(case):
    point = {
        "value": _f(case["odds_ratio"]),
        "baseline": _f(case["baseline"]),
        "design_effect": _f(case["deff"]),
    }
    power = survey_trend_power(point, case["survey_n"], 0, 0.05).power
    assert power == pytest.approx(_f(case["power"]), abs=1e-9)


@pytest.mark.parametrize("case", FIXTURE["slopes"], ids=lambda c: c["deff"])
def test_the_slope_agrees_with_r(case):
    point = {
        "value": _f(case["slope"]),
        "exposure_sd": _f(case["exposure_sd"]),
        "residual_sd": _f(case["residual_sd"]),
        "design_effect": _f(case["deff"]),
    }
    power = survey_slope_power(point, case["n"], 0, _f(case["alpha"])).power
    assert power == pytest.approx(case["power"], abs=1e-12)


def test_the_lesson_finds_deff_times_the_simple_size(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    declared, needed = (request["report"]["calculation"] for request in report["requests"])
    assert declared["design_effect"]["fraction"] == "2"
    assert declared["effective_sample_size"]["decimal_approximation"] == "6000.000000"
    assert needed["total_sample_size"] == 23530  # R: 23529.51
    assert report["values"]["effective"] == "11765"
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (f"let p = meets(analysis=table, target={target('')})", "planning_point", "design_effect"),
        (f"let p = meets(analysis=logistic, target={target()})", "planning_point", "leave"),
        (
            "let x = outcome_prevalence(unexposed=1/10, prevalence_ratio=2, exposed_share=1/5, "
            "design_effect=0)",
            "domain",
            "positive",
        ),
    ],
)
def test_refusals_explain_the_design_effect(line, code, words):
    found = diagnostics(SURVEY + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_ties_the_design_effect_to_survey_tests():
    text = SURVEY + f"let claim = meets(analysis=table, target={target()})\n"
    derivation = next(
        d for d in compile_source(Source(text)).derivations if d.name == "claim"
    ).to_dict()
    assert check_derivation(derivation) == []
    for change in ("drop", "0"):
        altered = copy.deepcopy(derivation)
        for step in altered["steps"]:
            if step["rule"] in ("power-formula", "alternative"):
                if change == "drop":
                    step["facts"]["point"].pop("design_effect", None)
                else:
                    step["facts"]["point"]["design_effect"] = change
        assert check_derivation(altered), change
