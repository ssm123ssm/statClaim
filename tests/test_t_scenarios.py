"""The t-tests simulated with unequal SDs or a skewed outcome, where Type I is judged."""

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

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/t_scenarios_r.json").read_text())
LESSON = ROOT / "examples/tutorial/38_t_scenarios.stat"
HEAD = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse planning\n"
    "let study = two_arm_continuous(n_control=20, n_treatment=40)\n"
    "let student = t_test(design=fixed(model=study), null=equal_means(model=study), "
    "alpha=1/20)\n"
)
SPREAD = "mean_difference(value=8, sd=20, sd_treatment=10)"


def target(point=SPREAD, maximum="3/40"):
    return f"power_target(at={point}, minimum=4/5, maximum_typeI={maximum})"


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


@pytest.mark.parametrize(
    "case",
    FIXTURE["cases"],
    ids=lambda c: f"{c['test']}-{c['side']}-{c['difference']}-{c['skewness']}",
)
def test_rejection_rates_agree_with_a_raw_data_simulation_in_r(case):
    """R values from replication/comparison/t_scenarios_r.R; R is not needed here."""
    trial = engine.two_means_trial(
        float(Fraction(case["difference"])),
        float(Fraction(case["sd"])),
        case["n_control"],
        case["n_treatment"],
        0.0,
        0.05,
        case["side"],
        case["test"] == "welch",
        sd_treatment=float(Fraction(case["sd_treatment"])),
        skewness=float(Fraction(case["skewness"])),
    )
    runs = 20000
    found = engine.estimate(trial, runs, engine.Stream(7, "r"))
    assert _close(found.rate, runs, case["rate"], case["runs"]), (found.rate, case["rate"])


def test_equal_sds_give_the_same_draws_as_before():
    """A scenario equal to the old one takes the old path, so seeds keep their numbers."""
    for welch in (False, True):
        plain = engine.two_means_trial(5, 10, 30, 30, 0, 0.05, "both", welch)
        same = engine.two_means_trial(5, 10, 30, 30, 0, 0.05, "both", welch, sd_treatment=10)
        first = engine.estimate(plain, 2000, engine.Stream(3, "same"))
        second = engine.estimate(same, 2000, engine.Stream(3, "same"))
        assert first == second


def test_the_lesson_judges_type_one_in_each_scenario(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    pooled, separate, enough = (r["report"]["calculation"] for r in report["requests"])
    assert pooled["typeI_judged"] and separate["typeI_judged"]
    # Student's test rejects a true null far too often when the smaller arm varies more.
    assert Fraction(pooled["typeI_lower"]["fraction"]) > Fraction(3, 40)
    assert pooled["typeI_target_met"] is False
    assert separate["typeI_target_met"] is True
    assert [r["report"]["decision"] for r in report["requests"]][:2] == [
        "target_not_met",
        "target_not_met",
    ]
    assert enough["n_control"] == 65 and enough["typeI_target_met"]
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


def test_a_search_passes_over_sizes_whose_type_one_fails(tmp_path):
    text = HEAD + (
        "let sizes = allocated_arm_sizes(analysis=student, min_control=20, max_control=40, "
        "treatment_per_control=2)\n"
        "let found = simulate(smallest_sample_size(candidates=sizes, target="
        f"{target('mean_difference(value=14, sd=20, sd_treatment=10)')}), seed=1, runs=2000)\n"
    )
    report = check_source(Source(text, "search.stat"), project=ROOT, output=tmp_path / "run")
    request = report["requests"][0]["report"]
    # Power passes early, but Student's Type I stays near 0.11 at every size.
    assert request["decision"] == "no_feasible_candidate"
    assert request["calculation"]["confirmations"] > 1


def test_within_the_theory_type_one_is_reported_not_judged(tmp_path):
    text = HEAD + (
        "let plain = simulate(meets(analysis=student, target="
        f"{target('mean_difference(value=8, sd=20)', '1/20')}), seed=1, runs=2000)\n"
    )
    report = check_source(Source(text, "plain.stat"), project=ROOT, output=tmp_path / "run")
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["typeI_judged"] is False and calculation["typeI_target_met"] is True


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = calculate(meets(analysis=student, target={target()}))",
            "unsupported_claim",
            "simulate",
        ),
        (
            "let x = mean_difference(value=1, sd=1, skewness=5)",
            "domain",
            "between -4 and 4",
        ),
        ("let x = mean_difference(value=1, sd=1, sd_treatment=0)", "domain", "positive"),
        (
            "let sizes = equal_arm_sizes(analysis=student, min_per_arm=10, max_per_arm=1000)\n"
            "let s = simulate(smallest_sample_size(candidates=sizes, target="
            f"{target('mean_difference(value=1, sd=1, skewness=1)')}), seed=1)",
            "domain",
            "one participant at a time",
        ),
    ],
)
def test_refusals_explain_t_test_scenarios(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_other_tests_refuse_a_t_test_scenario():
    text = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.cluster\nuse planning\n"
        "let clinics = cluster_assignment(clusters_control=6, clusters_treatment=6, "
        "n_control=120, n_treatment=120)\n"
        "let practice = two_arm(assignment=clinics, outcome=continuous_outcome())\n"
        "let summaries = cluster_t_test(design=fixed(model=practice), "
        "null=equal_means(model=practice), alpha=1/20)\n"
        "let p = meets(analysis=summaries, target=power_target(at=mean_difference(value=5, "
        "sd=10, icc=1/20, skewness=1), minimum=4/5, maximum_typeI=1/20))\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "two-sample t-test" in found[0][1]


def test_the_checker_bounds_the_scenario():
    text = HEAD + f"let claim = meets(analysis=student, target={target()})\n"
    program = compile_source(Source(text))
    derivation = next(d for d in program.derivations if d.name == "claim").to_dict()
    assert check_derivation(derivation) == []
    for change in ({"sd_treatment": "0"}, {"skewness": "9"}):
        altered = copy.deepcopy(derivation)
        step = next(s for s in altered["steps"] if s["rule"] == "power-formula")
        step["facts"]["point"].update(change)
        assert check_derivation(altered), change
