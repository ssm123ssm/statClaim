"""The log-rank test simulated from exponential survival times, with a delayed effect."""

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
from statclaim.methods.power import log_rank_times

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/survival_simulation_r.json").read_text())
LESSON = ROOT / "examples/tutorial/39_survival_simulation.stat"
HEAD = (
    "use models.two_arm_survival\nuse sampling\nuse tests.survival\nuse planning\n"
    "let study = two_arm_survival(n_control=150, n_treatment=150)\n"
    "let analysis = log_rank(design=fixed(model=study), null=equal_survival(model=study), "
    "alpha=1/20)\n"
)
LATE = (
    "exponential_survival(hazard_ratio=7/10, control_median=12, accrual=12, follow_up=12, "
    "effect_delay=3)"
)


def target(point=LATE):
    return f"power_target(at={point}, minimum=4/5, maximum_typeI=1/20)"


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
    "case",
    FIXTURE["cases"],
    ids=lambda c: f"{c['n_control']}-{c['hazard_ratio']}-{c['effect_delay']}",
)
def test_rejection_rates_agree_with_survdiff_in_r(case):
    """R values from replication/comparison/survival_simulation_r.R; R is not needed here."""
    trial = engine.log_rank_trial(
        _f(case["hazard_ratio"]),
        _f(case["control_median"]),
        _f(case["accrual"]),
        _f(case["follow_up"]),
        case["n_control"],
        case["n_treatment"],
        0.05,
        dropout=_f(case["dropout"]),
        dropout_time=_f(case["dropout_time"]),
        delay=_f(case["effect_delay"]),
    )
    runs = 10000
    found = engine.estimate(trial, runs, engine.Stream(7, "r"))
    assert _close(found.rate, runs, case["rate"], case["runs"]), (found.rate, case["rate"])
    if case["effect_delay"] == "0" and case["hazard_ratio"] != "1":
        # Without a delay, Schoenfeld's formula is close to the simulated power.
        point = {
            key: _f(case[key])
            for key in ("control_median", "accrual", "follow_up", "dropout", "dropout_time")
        }
        point["value"] = _f(case["hazard_ratio"])
        formula = log_rank_times(point, case["n_control"], case["n_treatment"], 0, 0.05, "both")
        assert abs(formula.power - found.rate) < 0.03


def test_the_lesson_shows_what_a_delay_costs(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    formula, simulated, too_small, enough = (r["report"]["calculation"] for r in report["requests"])
    schoenfeld = float(formula["power"]["decimal_approximation"])
    assert abs(schoenfeld - 0.8) < 0.01
    assert _f(simulated["power_lower"]["fraction"]) - 0.01 <= schoenfeld
    assert schoenfeld <= _f(simulated["power_upper"]["fraction"]) + 0.01
    assert _f(too_small["power_upper"]["fraction"]) < 0.6
    assert enough["power_target_met"] and not enough["typeI_judged"]
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


def test_type_one_is_simulated_with_equal_survival(tmp_path):
    text = (
        HEAD + f"let p = simulate(meets(analysis=analysis, target={target()}), seed=3, runs=2000)\n"
    )
    report = check_source(Source(text, "null.stat"), project=ROOT, output=tmp_path / "run")
    calculation = report["requests"][0]["report"]["calculation"]
    assert abs(_f(calculation["typeI"]["fraction"]) - 0.05) < 0.015
    assert "from 3 after entry" in calculation["scenario"]


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = calculate(meets(analysis=analysis, target={target()}))",
            "unsupported_claim",
            "simulate",
        ),
        (
            "let x = exponential_survival(hazard_ratio=7/10, control_median=12, accrual=12, "
            "follow_up=12, effect_delay=-1)",
            "domain",
            "at least 0",
        ),
        (
            "let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=100, max_per_arm=900)\n"
            f"let s = simulate(smallest_sample_size(candidates=sizes, target={target()}), seed=1)",
            "domain",
            "one participant at a time",
        ),
        (
            "let p = simulate(meets(analysis=analysis, target="
            f"{target('hazard_ratio(value=7/10, events=200)')}), seed=1)",
            "planning_point",
            "exponential_survival",
        ),
    ],
)
def test_refusals_explain_survival_simulation(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_bounds_the_delay():
    text = HEAD + f"let claim = meets(analysis=analysis, target={target()})\n"
    program = compile_source(Source(text))
    derivation = next(d for d in program.derivations if d.name == "claim").to_dict()
    assert check_derivation(derivation) == []
    altered = copy.deepcopy(derivation)
    step = next(s for s in altered["steps"] if s["rule"] == "power-formula")
    step["facts"]["point"]["effect_delay"] = "-2"
    assert check_derivation(altered)
