"""The tests of a correlation and a regression slope simulated with skewed data."""

import copy
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim import simulation as engine
from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.association_power import correlation_power
from statclaim.methods.simulation import _slope

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/correlation_simulation_r.json").read_text())
LESSON = ROOT / "examples/tutorial/40_skewed_correlation.stat"
HEAD = (
    "use models.observational\nuse sampling\nuse tests.correlation\nuse tests.regression\n"
    "use planning\n"
    'let survey = cross_sectional(n=30, exposure="x", outcome="y", exposure_scale="continuous", '
    'outcome_scale="continuous")\n'
    "let pearson = pearson_correlation(design=fixed(model=survey), "
    "null=no_association(model=survey), alpha=1/20)\n"
)
SKEWED = "correlation(value=1/2, skewness=3, exposure_skewness=3)"


def target(point=SKEWED, maximum="3/40"):
    return f"power_target(at={point}, minimum=4/5, maximum_typeI={maximum})"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


def _f(text):
    return float(Fraction(text))


def _close(ours: float, runs: int, theirs: float, their_runs: int) -> bool:
    """Within four standard errors of two independent Monte Carlo estimates."""
    p = (ours * runs + theirs * their_runs) / (runs + their_runs)
    return abs(ours - theirs) <= 4 * math.sqrt(p * (1 - p) * (1 / runs + 1 / their_runs))


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize(
    "case", FIXTURE["cases"], ids=lambda c: f"{c['kind']}-{c['n']}-{c['value']}"
)
def test_rejection_rates_agree_with_a_raw_data_simulation_in_r(case):
    """R values from replication/comparison/correlation_simulation_r.R; R is not needed here."""
    skews = {"skewness": _f(case["skewness"]), "exposure_skewness": _f(case["exposure_skewness"])}
    if case["kind"] == "correlation":
        trial = engine.correlation_trial(_f(case["value"]), case["n"], 0.05, **skews)
    else:
        point = {
            "value": _f(case["value"]),
            "exposure_sd": _f(case["exposure_sd"]),
            "residual_sd": _f(case["residual_sd"]),
            **skews,
        }
        trial = _slope(point, case["n"], 0, 0.05)
    runs = 20000
    found = engine.estimate(trial, runs, engine.Stream(7, "r"))
    assert _close(found.rate, runs, case["rate"], case["runs"]), (found.rate, case["rate"])


def test_with_normal_data_the_simulation_agrees_with_the_exact_power():
    found = engine.estimate(engine.correlation_trial(0.3, 60, 0.05), 20000, engine.Stream(5, "n"))
    exact = correlation_power({"value": 0.3}, 60, 0, 0.05).power
    assert found.lower <= exact <= found.upper


def test_the_lesson_simulates_a_skewed_correlation(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    exact, simulated, needed = (r["report"]["calculation"] for r in report["requests"])
    assert _f(exact["power"]["fraction"]) > 0.8
    assert _f(simulated["power_upper"]["fraction"]) < 0.8
    assert simulated["typeI_judged"] and simulated["typeI_target_met"]
    assert needed["total_sample_size"] == 36
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = calculate(meets(analysis=pearson, target={target()}))",
            "unsupported_claim",
            "simulate",
        ),
        (
            "let p = simulate(meets(analysis=pearson, target="
            f"{target('correlation(value=1/2)', '1/20')}), seed=1)",
            "unsupported_claim",
            "exact",
        ),
        ("let x = correlation(value=1/2, skewness=5)", "domain", "between -4 and 4"),
        (
            "let s = spearman_correlation(design=fixed(model=survey), "
            "null=no_association(model=survey), alpha=1/20)\n"
            f"let p = meets(analysis=s, target={target()})",
            "planning_point",
            "not simulated",
        ),
        (
            "let a = linear_association(design=fixed(model=survey), "
            'null=no_association(model=survey), alpha=1/20, adjusted_for=["age"])\n'
            "let p = meets(analysis=a, target=power_target(at=slope(value=1, exposure_sd=1, "
            "residual_sd=1, skewness=1), minimum=4/5, maximum_typeI=3/40))",
            "planning_point",
            "without covariates",
        ),
    ],
)
def test_refusals_explain_skewed_simulation(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_bounds_the_skewness():
    text = HEAD + f"let claim = meets(analysis=pearson, target={target()})\n"
    program = compile_source(Source(text))
    derivation = next(d for d in program.derivations if d.name == "claim").to_dict()
    assert check_derivation(derivation) == []
    altered = copy.deepcopy(derivation)
    for step in altered["steps"]:
        point = step.get("facts", {}).get("point")
        if isinstance(point, dict) and "skewness" in point:
            point["skewness"] = "9"
    assert check_derivation(altered)
