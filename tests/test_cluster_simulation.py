"""Power of the t-test on cluster summaries by simulation, with cluster sizes that vary."""

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
from statclaim.methods.power import cluster_means
from statclaim.methods.simulation import _cluster_means, _cluster_proportions

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/cluster_simulation_r.json").read_text())
LESSON = ROOT / "examples/tutorial/37_cluster_simulation.stat"
TRIAL = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.cluster\nuse tests.t\nuse planning\n"
    "let clinics = cluster_assignment(clusters_control=6, clusters_treatment=6, n_control=120, "
    "n_treatment=120)\n"
    "let practice = two_arm(assignment=clinics, outcome=continuous_outcome())\n"
    "let summaries = cluster_t_test(design=fixed(model=practice), "
    "null=equal_means(model=practice), alpha=1/20)\n"
)
VARIED = "mean_difference(value=5, sd=10, icc=1/20, cluster_size_cv=3/5)"


def _f(text):
    return float(Fraction(text))


def target(point=VARIED):
    return f"power_target(at={point}, minimum=4/5, maximum_typeI=1/20)"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


def _close(ours: float, runs: int, theirs: float, their_runs: int) -> bool:
    """Within four standard errors of two independent Monte Carlo estimates."""
    p = (ours * runs + theirs * their_runs) / (runs + their_runs)
    return abs(ours - theirs) <= 4 * math.sqrt(p * (1 - p) * (1 / runs + 1 / their_runs))


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("case", FIXTURE["means"], ids=lambda c: f"{c['k']}-{c['cv']}")
def test_cluster_means_agree_with_a_raw_data_simulation_in_r(case):
    """R values from replication/comparison/cluster_simulation_r.R; R is not needed here."""
    point = {
        "value": _f(case["difference"]),
        "sd": _f(case["sd"]),
        "icc": _f(case["icc"]),
        "size_control": case["m"],
        "size_treatment": case["m"],
        "cluster_size_cv": _f(case["cv"]),
    }
    runs = 20000
    found = engine.estimate(
        _cluster_means(point, case["k"], case["k"], 0, 0.05, "both"), runs, engine.Stream(7, "r")
    )
    assert _close(found.rate, runs, case["power"], case["runs"]), (found.rate, case["power"])
    if case["cv"] == "0":  # equal clusters: the noncentral t is exact
        exact = cluster_means(point, case["k"], case["k"], 0, 0.05, "both").power
        assert found.lower <= exact <= found.upper


@pytest.mark.parametrize("case", FIXTURE["proportions"], ids=lambda c: f"{c['k']}-{c['cv']}")
def test_cluster_proportions_agree_with_a_raw_data_simulation_in_r(case):
    point = {
        "p_control": _f(case["p_control"]),
        "p_treatment": _f(case["p_treatment"]),
        "icc": _f(case["icc"]),
        "size_control": case["m"],
        "size_treatment": case["m"],
        "cluster_size_cv": _f(case["cv"]),
    }
    runs = 20000
    trial = _cluster_proportions(point, case["k"], case["k"], 0, 0.05, "both")
    found = engine.estimate(trial, runs, engine.Stream(7, "r"))
    assert _close(found.rate, runs, case["power"], case["runs"]), (found.rate, case["power"])


def test_the_binomial_draw_has_the_right_mean_and_variance():
    stream = engine.Stream(1, "binomial")
    draws = [stream.binomial(40, 0.3) for _ in range(20000)]
    mean = sum(draws) / len(draws)
    variance = sum((x - mean) ** 2 for x in draws) / (len(draws) - 1)
    assert mean == pytest.approx(12, abs=0.1) and variance == pytest.approx(8.4, rel=0.05)
    assert stream.binomial(10, 0.0) == 0 and stream.binomial(10, 1.0) == 10


def test_the_lesson_simulates_clusters_of_unequal_sizes(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    formula, equal, varied, search = (r["report"]["calculation"] for r in report["requests"])
    assert formula["power"]["decimal_approximation"] == "0.705780"
    # Equal clusters: the simulation's interval holds the noncentral t.
    assert (
        float(equal["power_lower"]["decimal_approximation"])
        <= 0.70578
        <= float(equal["power_upper"]["decimal_approximation"])
    )
    assert Fraction(varied["power"]["fraction"]) < Fraction(66, 100)
    assert varied["cluster_size_cv"]["fraction"] == "3/5"
    assert search["clusters_control"] == 9
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = calculate(meets(analysis=summaries, target={target()}))",
            "unsupported_claim",
            "simulate",
        ),
        (
            "let p = simulate(meets(analysis=summaries, target="
            f"{target('mean_difference(value=5, sd=10)')}), seed=1)",
            "planning_point",
            "icc=...",
        ),
        (
            "let x = mean_difference(value=5, sd=10, icc=1/20, cluster_size_cv=4)",
            "domain",
            "between 0 and 3",
        ),
    ],
)
def test_refusals_explain_cluster_simulation(line, code, words):
    found = diagnostics(TRIAL + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_participant_tests_refuse_cluster_sizes():
    text = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse planning\n"
        "let study = two_arm_continuous(n_control=50, n_treatment=50)\n"
        "let test = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
        "let p = simulate(meets(analysis=test, target=power_target(at=mean_difference(value=5, "
        "sd=10, cluster_size_cv=1/2), minimum=4/5, maximum_typeI=1/20)), seed=1)\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "cluster" in found[0][1]


def test_the_checker_accepts_and_bounds_cluster_size_variation():
    text = TRIAL + f"let claim = meets(analysis=summaries, target={target()})\n"
    derivation = next(
        d for d in compile_source(Source(text)).derivations if d.name == "claim"
    ).to_dict()
    assert check_derivation(derivation) == []
    altered = copy.deepcopy(derivation)
    step = next(s for s in altered["steps"] if s["rule"] == "power-formula")
    step["facts"]["point"]["cluster_size_cv"] = "5"
    assert check_derivation(altered)
