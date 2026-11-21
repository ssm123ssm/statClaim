"""Power of the cited regressions of observational studies: logistic, Poisson rates and
conditional logistic."""

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
    logistic_trend_power,
    matched_pairs_power,
    poisson_rates_power,
)

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/logistic_power_r.json").read_text())
LESSON = ROOT / "examples/tutorial/34_regression_power.stat"


def _f(text):
    return float(Fraction(text))


def run(text, tmp_path):
    return check_source(Source(text, "regressions.stat"), project=ROOT, output=tmp_path / "run")


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("case", FIXTURE["logistic_binary"], ids=lambda c: c["p_other"])
def test_hsieh_binary_reaches_the_target_at_pwrss_size(case):
    """R values from replication/comparison/logistic_power_r.R; R is not needed here."""
    point = {
        "p_reference": _f(case["p_reference"]),
        "p_other": _f(case["p_other"]),
        "share_other": _f(case["share_other"]),
    }
    # pwrss divides by 1 - R^2; StatClaim takes the covariates to be unrelated to exposure.
    n = case["n"] * (1 - _f(case["r2"]))
    assert logistic_groups_power(point, n, 0, 0.05).power == pytest.approx(
        _f(case["power"]), abs=1e-9
    )


@pytest.mark.parametrize("case", FIXTURE["logistic_normal"], ids=lambda c: c["odds_ratio"])
def test_hsieh_normal_reaches_the_target_at_pwrss_size(case):
    point = {
        "value": _f(case["odds_ratio"]),
        "baseline": _f(case["baseline"]),
        "exposure_r2": _f(case["r2"]),
    }
    assert logistic_trend_power(point, case["n"], 0, 0.05).power == pytest.approx(
        _f(case["power"]), abs=1e-9
    )


@pytest.mark.parametrize("case", FIXTURE["poisson_rates"], ids=lambda c: c["rate_ratio"])
def test_signorini_agrees_with_r(case):
    point = {"rate_ratio": _f(case["rate_ratio"]), "exposed_share": _f(case["share"])}
    power = poisson_rates_power(point, case["events"], 0, _f(case["alpha"])).power
    assert power == pytest.approx(case["formula"], abs=1e-9)
    # pwrss adds the rejections in the other direction, which are negligible here.
    assert 0 <= case["pwrss"] - power < 1e-6


@pytest.mark.parametrize("case", FIXTURE["matched_pairs"], ids=lambda c: str(c["pairs"]))
def test_connor_agrees_with_mess(case):
    point = {"share": _f(case["share"]), "odds_ratio": _f(case["odds_ratio"])}
    power = matched_pairs_power(point, case["pairs"], 0, _f(case["alpha"])).power
    assert power == pytest.approx(case["mess"], abs=1e-10)


@pytest.mark.parametrize("case", FIXTURE["simulations"], ids=lambda c: str(c["n"]))
def test_hsieh_is_close_to_the_simulated_wald_test(case):
    point = {
        "p_reference": _f(case["p_reference"]),
        "p_other": _f(case["p_other"]),
        "share_other": _f(case["share_other"]),
    }
    power = logistic_groups_power(point, case["n"], 0, 0.05).power
    assert abs(power - case["simulation"]) < 0.02  # 4,000 runs: standard error about 0.006


EXPECTED = {
    "cohort_power": ("exposed", 300, "0.590859"),
    "cohort_needed": ("exposed", 502, None),
    "case_control_needed": ("cases", 126, None),
    "trend_needed": ("total_sample_size", 531, None),
    "pairs_needed": ("pairs", 281, None),
    "events_needed": ("events", 96, None),
}


def test_the_lesson_plans_each_regression(tmp_path):
    text = LESSON.read_text()
    report = run(text, tmp_path)
    # Requests run in the order of their bindings.
    names = [line.split()[1] for line in text.splitlines() if "calculate(" in line]
    found = {
        name: request["report"] for name, request in zip(names, report["requests"], strict=True)
    }
    for name, (key, size, power) in EXPECTED.items():
        calculation = found[name]["calculation"]
        assert calculation[key] == size, name
        if power is not None:
            assert calculation["power"]["decimal_approximation"] == power
    # A case-control search keeps the ratio of controls to cases.
    assert found["case_control_needed"]["calculation"]["controls"] == 252
    program = compile_source(Source(LESSON.read_text()))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


STUDIES = (
    "use models.observational\nuse sampling\nuse tests.regression\nuse planning\n"
    'let paired = matched_case_control(pairs=220, exposure="e", outcome="o")\n'
    "let conditional = conditional_logistic(design=fixed(model=paired), "
    "null=no_association(model=paired), alpha=1/20)\n"
    'let workers = person_time_cohort(exposure="e", outcome="o")\n'
    "let rates = poisson_rate_regression(design=fixed(model=workers), "
    "null=no_association(model=workers), alpha=1/20)\n"
    'let survey = cross_sectional(n=400, exposure="e", outcome="o")\n'
    "let logistic = logistic_association(design=fixed(model=survey), "
    "null=no_association(model=survey), alpha=1/20)\n"
)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            "let p = meets(analysis=conditional, target=power_target(at=risks(unexposed=1/10, "
            "risk_ratio=2), minimum=4/5, maximum_typeI=1/20))",
            "planning_point",
            "discordant_pairs",
        ),
        (
            "let p = meets(analysis=rates, target=power_target(at=incidence_rates(rate_ratio=2, "
            "exposed_time=1, unexposed_time=3), minimum=4/5, maximum_typeI=1/20))",
            "planning_point",
            "events=",
        ),
        (
            "let p = meets(analysis=logistic, target=power_target(at=risks(unexposed=1/10, "
            "risk_ratio=2), minimum=4/5, maximum_typeI=1/20))",
            "planning_point",
            "outcome_prevalence",
        ),
        (
            "let p = meets(analysis=logistic, target=power_target(at=odds_per_sd(odds_ratio=2, "
            "baseline=1/10), minimum=4/5, maximum_typeI=1/20))",
            "planning_point",
            "outcome_prevalence",
        ),
        (
            "let s = matched_sizes(analysis=logistic, min_pairs=10, max_pairs=40)",
            "type",
            "matched study",
        ),
        ("let o = odds_per_sd(odds_ratio=2, baseline=1)", "domain", "strictly between"),
    ],
)
def test_refusals_explain_regression_planning(line, code, words):
    found = diagnostics(STUDIES + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_rejects_altered_regression_plans():
    text = STUDIES + (
        "let target = power_target(at=discordant_pairs(share=1/4, odds_ratio=2), minimum=4/5, "
        "maximum_typeI=1/20)\n"
        "let search = smallest_sample_size(candidates=matched_sizes(analysis=conditional, "
        "min_pairs=10, max_pairs=5000), target=target)\n"
    )
    derivation = next(
        d for d in compile_source(Source(text)).derivations if d.name == "search"
    ).to_dict()
    assert check_derivation(derivation) == []
    for change in ({"discordant": "0"}, {"odds_ratio": "-1"}):
        altered = copy.deepcopy(derivation)
        for step in altered["steps"]:
            if step["rule"] in ("power-formula", "alternative"):
                step["facts"]["point"].update(change)
        assert check_derivation(altered), change
    widened = copy.deepcopy(derivation)
    step = next(s for s in widened["steps"] if s["rule"] == "search-range")
    step["facts"]["search"]["max_pairs"] = 10**7
    assert check_derivation(widened)
