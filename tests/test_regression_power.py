"""Power of the cited observational tests of a correlation and a regression slope."""

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
    correlation_power,
    exposure_means_power,
    slope_power,
    spearman_power,
    survey_means_power,
)
from statclaim.methods.observational import METHODS

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/regression_power_r.json").read_text())

STUDY = (
    "use models.observational\nuse sampling\nuse tests.regression\nuse tests.correlation\n"
    "use planning\n"
    'let clinic = cross_sectional(n=250, exposure="BMI", outcome="pressure", '
    'exposure_scale="continuous", outcome_scale="continuous")\n'
    "let rho = pearson_correlation(design=fixed(model=clinic), "
    "null=no_association(model=clinic), alpha=1/20)\n"
    "let fitted = linear_association(design=fixed(model=clinic), "
    'null=no_association(model=clinic), alpha=1/20, adjusted_for=["age", "sex"])\n'
)
RHO = "power_target(at=correlation(value=1/5), minimum=4/5, maximum_typeI=1/20)"
SLOPE = (
    "power_target(at=slope(value=1/2, exposure_sd=4, residual_sd=15, exposure_r2=1/10), "
    "minimum=9/10, maximum_typeI=1/20)"
)


def run(text, tmp_path):
    return check_source(Source(text, "regression.stat"), project=ROOT, output=tmp_path / "run")


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def _f(text):
    return float(Fraction(text))


@pytest.mark.parametrize("case", FIXTURE["correlations"], ids=lambda c: f"{c['rho']}-{c['n']}")
def test_correlation_power_agrees_with_r(case):
    """R values from replication/comparison/regression_power_r.R; R is not needed here."""
    power = correlation_power({"value": _f(case["rho"])}, case["n"], 0, _f(case["alpha"])).power
    assert power == pytest.approx(case["integrate"], abs=1e-10)
    # Fisher's z, which pwr uses, is close but not the same.
    assert abs(power - case["pwr"]) < 0.003
    if "simulation" in case:  # 40,000 simulated studies: within four standard errors
        assert abs(power - case["simulation"]) < 4 * (power * (1 - power) / 40000) ** 0.5


@pytest.mark.parametrize("case", FIXTURE["slopes"], ids=lambda c: f"{c['k']}-{c['n']}")
def test_slope_power_agrees_with_r(case):
    point = {
        "value": _f(case["slope"]),
        "exposure_sd": _f(case["exposure_sd"]),
        "residual_sd": _f(case["residual_sd"]),
        "exposure_r2": _f(case["exposure_r2"]),
    }
    power = slope_power(point, case["n"], case["k"], _f(case["alpha"])).power
    assert power == pytest.approx(case["integrate"], abs=1e-10)
    assert abs(power - case["simulation"]) < 4 * (power * (1 - power) / 40000) ** 0.5
    # With the exposure held fixed, as pwr.f2.test has it, power is a little higher.
    assert 0 < case["pwr_f2"] - power < 0.01


def test_both_searches_find_the_size_r_finds(tmp_path):
    text = STUDY + (
        "let rho_n = calculate(smallest_sample_size(candidates=total_sizes(analysis=rho, "
        f"min_n=4, max_n=5000), target={RHO}))\n"
        "let slope_n = calculate(smallest_sample_size(candidates=total_sizes(analysis=fitted, "
        f"min_n=10, max_n=5000), target={SLOPE}))\n"
    )
    report = run(text, tmp_path)
    found = [request["report"]["calculation"] for request in report["requests"]]
    for calculation, case in zip(found, FIXTURE["searches"], strict=True):
        assert calculation["total_sample_size"] == case["n"]
        assert float(calculation["power"]["decimal_approximation"]) == pytest.approx(
            case["power_at"], abs=1e-6
        )
    # Bisection: a handful of evaluations, not one per candidate.
    assert all(calculation["candidates_evaluated"] <= 15 for calculation in found)


def test_meets_reports_degrees_of_freedom_and_reads_as_fields(tmp_path):
    text = STUDY + (
        f"let power = calculate(meets(analysis=fitted, target={SLOPE}))\n"
        "let df = power.calculation.degrees_of_freedom\n"
    )
    report = run(text, tmp_path)
    details = report["requests"][0]["report"]
    assert details["calculation"]["covariates"] == 2
    assert report["values"]["df"] == 246
    assert details["decision"] == "target_not_met"
    ids = [item["id"] for item in details["assumptions"]]
    assert {"linear_model", "normal_exposure_power", "covariates_explain_exposure"} <= set(ids)


def test_the_formulas_each_test_has():
    assert {key: [f.point for f in m.formulas] for key, m in METHODS.items() if m.formulas} == {
        "pearson_correlation": ["correlation"],
        "linear_association": ["slope", "outcome_means"],
        "modified_poisson": ["association_groups"],
        "spearman_correlation": ["correlation"],
        "logistic_association": ["association_groups", "odds_per_sd"],
        "conditional_logistic": ["discordant_pairs"],
        "poisson_rate_regression": ["incidence_rates"],
        "survey_logistic": ["association_groups", "odds_per_sd"],
        "survey_linear": ["slope", "outcome_means"],
        "rao_scott_test": ["association_groups"],
    }


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (f"let v = verify(meets(analysis=rho, target={RHO}))", "unsupported_claim", "calculate"),
        (
            "let p = meets(analysis=rho, target=power_target(at=correlation(value=0), "
            "minimum=4/5, maximum_typeI=1/20))",
            "alternative_in_null",
            "outside the null",
        ),
        (f"let p = meets(analysis=fitted, target={RHO})", "planning_point", "slope(value="),
        ("let r = correlation(value=1)", "domain", "strictly between -1 and 1"),
        (
            f"let s = smallest_sample_size(candidates=total_sizes(analysis=fitted, min_n=4, "
            f"max_n=50), target={SLOPE})",
            "domain",
            "at least 5",
        ),
        (
            f"let s = simulate(meets(analysis=rho, target={RHO}), seed=1)",
            "no_simulation_model",
            "calculate",
        ),
    ],
)
def test_refusals_explain_observational_planning(line, code, words):
    found = diagnostics(STUDY + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_points_and_exposure_scales_must_fit_a_formula():
    # A yes-or-no exposure is planned at the two groups' means, not at a slope.
    text = (
        "use models.observational\nuse sampling\nuse tests.regression\nuse planning\n"
        'let cohort_ = cross_sectional(n=300, exposure="smoking", outcome="pressure", '
        'outcome_scale="continuous")\n'
        "let fitted = linear_association(design=fixed(model=cohort_), "
        "null=no_association(model=cohort_), alpha=1/20)\n"
        f"let p = meets(analysis=fitted, target={SLOPE})\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "outcome_means(" in found[0][1]
    # Conditional logistic regression has a formula for a yes-or-no exposure only.
    text = (
        "use models.observational\nuse sampling\nuse tests.regression\nuse planning\n"
        'let paired = matched_case_control(pairs=200, exposure="dose", outcome="o", '
        'exposure_scale="continuous")\n'
        "let fitted = conditional_logistic(design=fixed(model=paired), "
        "null=no_association(model=paired), alpha=1/20)\n"
        f"let p = meets(analysis=fitted, target={RHO})\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "binary exposure" in found[0][1]


def _derivation(text, name):
    return next(d for d in compile_source(Source(text)).derivations if d.name == name).to_dict()


def test_observational_plans_have_checked_derivations():
    text = STUDY + (
        f"let claim = meets(analysis=fitted, target={SLOPE})\n"
        "let search = smallest_sample_size(candidates=total_sizes(analysis=rho, min_n=4, "
        f"max_n=5000), target={RHO})\n"
    )
    for name in ("claim", "search"):
        derivation = _derivation(text, name)
        assert check_derivation(derivation) == [], name
    claim = _derivation(text, "claim")
    for change in ({"residual_sd": "0"}, {"exposure_r2": "1"}, {"slope": "0"}):
        altered = copy.deepcopy(claim)
        for step in altered["steps"]:
            if step["rule"] in ("power-formula", "alternative"):
                step["facts"]["point"].update(change)
        assert check_derivation(altered), change
    search = _derivation(text, "search")
    widened = copy.deepcopy(search)
    step = next(s for s in widened["steps"] if s["rule"] == "search-range")
    step["facts"]["search"]["max_n"] = 10**7
    assert check_derivation(widened)


def test_the_example_and_lesson_plan_measured_variables():
    for path in ("examples/regression.stat", "examples/tutorial/33_correlation_power.stat"):
        program = compile_source(Source((ROOT / path).read_text()))
        assert not program.diagnostics, path
        assert all(check_derivation(d.to_dict()) == [] for d in program.derivations), path


@pytest.mark.parametrize("case", FIXTURE["spearman"], ids=lambda c: f"{c['rho']}-{c['n']}")
def test_spearman_agrees_with_r_and_is_close_to_the_exact_test(case):
    power = spearman_power({"value": _f(case["rho"])}, case["n"], 0, 0.05).power
    assert power == pytest.approx(case["formula"], abs=1e-12)
    # Fisher's z is a little conservative for the exact permutation test.
    assert -0.03 < case["simulation"] - power < 0.03


@pytest.mark.parametrize("case", FIXTURE["means"], ids=lambda c: f"{c['difference']}-{c['k']}")
def test_two_means_agree_with_r(case):
    point = {"value": _f(case["difference"]), "sd": _f(case["sd"])}
    if "exposed" in case:
        point["n_exposed"] = case["exposed"]
        n = case["exposed"] + case["unexposed"]
    else:
        point["exposed_share"] = _f(case["share"])
        n = case["n"]
    power = exposure_means_power(point, n, case["k"], _f(case["alpha"])).power
    assert power == pytest.approx(case["power"], abs=1e-10)
    if isinstance(case.get("pwr"), float):  # pwr.t2n.test adds the other tail
        assert 0 <= case["pwr"] - power < 1e-5


def test_survey_means_agree_with_r():
    (case,) = FIXTURE["survey_means"]
    point = {
        "value": _f(case["difference"]),
        "sd": _f(case["sd"]),
        "exposed_share": _f(case["share"]),
        "design_effect": _f(case["deff"]),
    }
    assert survey_means_power(point, case["n"], 0, 0.05).power == pytest.approx(
        case["power"], abs=1e-12
    )


def test_a_yes_or_no_exposure_is_planned_at_two_means(tmp_path):
    text = (
        "use models.observational\nuse sampling\nuse tests.regression\nuse planning\n"
        'let clinic = cross_sectional(n=250, exposure="smoking", outcome="pressure", '
        'outcome_scale="continuous")\n'
        "let fitted = linear_association(design=fixed(model=clinic), "
        'null=no_association(model=clinic), alpha=1/20, adjusted_for=["age", "sex"])\n'
        "let means = outcome_means(unexposed=120, exposed=125, sd=15, exposed_share=1/3)\n"
        "let goal = power_target(at=means, minimum=4/5, maximum_typeI=1/20)\n"
        "let power = calculate(meets(analysis=fitted, target=goal))\n"
        "let search = smallest_sample_size(candidates=total_sizes(analysis=fitted, min_n=10, "
        "max_n=5000), target=goal)\n"
        "let sizing = calculate(search)\n"
    )
    report = run(text, tmp_path)
    power, sizing = (request["report"]["calculation"] for request in report["requests"])
    assert power["degrees_of_freedom"] == 246  # two covariates
    assert sizing["total_sample_size"] > 250
    derivation = next(d for d in compile_source(Source(text)).derivations if d.name == "search")
    assert check_derivation(derivation.to_dict()) == []
    found = diagnostics(text.replace(", exposed_share=1/3", ""))
    assert found[0][0] == "planning_point" and "exposed_share" in found[0][1]
