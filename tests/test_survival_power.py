"""Log-rank power planned from survival times: expected events, then Schoenfeld's formula."""

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
from statclaim.methods import METHODS
from statclaim.methods.power import log_rank_events, log_rank_times

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/survival_power_r.json").read_text())

TRIAL = (
    "use models.two_arm_survival\nuse sampling\nuse tests.survival\nuse planning\n"
    "let followed = two_arm_survival(n_control=200, n_treatment=200)\n"
    "let analysis = log_rank(design=fixed(model=followed), "
    "null=equal_survival(model=followed), alpha=1/20)\n"
)
TIMES = (
    "exponential_survival(hazard_ratio=7/10, control_median=12, accrual=24, follow_up=12, "
    "dropout=1/10, dropout_time=12)"
)


def target(point=TIMES, minimum="4/5"):
    return f"power_target(at={point}, minimum={minimum}, maximum_typeI=1/20)"


def run(text, tmp_path):
    return check_source(Source(text, "survival.stat"), project=ROOT, output=tmp_path / "run")


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def _point(case):
    point = {
        "value": float(Fraction(case["hazard_ratio"])),
        "control_median": float(Fraction(case["control_median"])),
        "accrual": float(Fraction(case["accrual"])),
        "follow_up": float(Fraction(case["follow_up"])),
    }
    if "dropout" in case:
        point.update(
            dropout=float(Fraction(case["dropout"])),
            dropout_time=float(Fraction(case["dropout_time"])),
        )
    return point


@pytest.mark.parametrize("case", FIXTURE["powers"], ids=lambda c: f"{c['n_c']}-{c['accrual']}")
def test_expected_events_and_power_agree_with_r(case):
    """R values from replication/comparison/survival_power_r.R; R is not needed here."""
    alpha = float(Fraction(case["alpha"]))
    result = log_rank_times(_point(case), case["n_c"], case["n_t"], 0, alpha, "both")
    assert result.expected_events == pytest.approx(case["expected_events"], abs=1e-9)
    assert result.event_probabilities[0] == pytest.approx(case["probability_control"], abs=1e-12)
    assert result.event_probabilities[1] == pytest.approx(case["probability_treatment"], abs=1e-12)
    assert result.power == pytest.approx(case["power"], abs=1e-12)
    # Given those events, it is the events formula.
    events = {"value": _point(case)["value"], "events": result.expected_events}
    same = log_rank_events(events, case["n_c"], case["n_t"], 0, alpha, "both")
    assert same.power == pytest.approx(result.power, abs=1e-12)


@pytest.mark.parametrize("case", FIXTURE["searches"], ids=lambda c: c["hazard_ratio"])
def test_searches_find_the_size_r_finds(case, tmp_path):
    lost = (
        f", dropout={case['dropout']}, dropout_time={case['dropout_time']}"
        if "dropout" in case
        else ""
    )
    point = (
        f"exponential_survival(hazard_ratio={case['hazard_ratio']}, "
        f"control_median={case['control_median']}, accrual={case['accrual']}, "
        f"follow_up={case['follow_up']}{lost})"
    )
    goal = f"power_target(at={point}, minimum={case['power']}, maximum_typeI={case['alpha']})"
    space = (
        "equal_arm_sizes(analysis=analysis, min_per_arm=10, max_per_arm=2000)"
        if case["ratio"] == 1
        else "allocated_arm_sizes(analysis=analysis, min_control=10, max_control=1000, "
        f"treatment_per_control={case['ratio']})"
    )
    text = (
        TRIAL + f"let sizing = calculate(smallest_sample_size(candidates={space}, target={goal}))\n"
    )
    calculation = run(text, tmp_path)["requests"][0]["report"]["calculation"]
    assert calculation["n_control"] == case["controls"]
    assert float(calculation["power"]["decimal_approximation"]) == pytest.approx(
        case["power_at"], abs=1e-6
    )
    # rpact and gsDesign give the unrounded total; the search rounds each arm up.
    total = case["controls"] * (1 + case["ratio"])
    assert case["rpact"] == pytest.approx(case["nsurv"])
    assert total - (1 + case["ratio"]) < case["rpact"] <= total


def test_log_rank_has_a_second_formula_at_survival_times():
    method = METHODS["log_rank"]
    assert [f.point for f in method.formulas] == ["hazard_ratio", "exponential_survival"]
    ids = {a.id for a in method.formula_at("exponential_survival").assumptions}
    assert {"exponential_times", "uniform_accrual", "exponential_dropout"} <= ids


def test_the_report_gives_expected_events_and_reads_as_fields(tmp_path):
    text = (
        TRIAL
        + f"let power = calculate(meets(analysis=analysis, target={target()}))\n"
        + "let events = power.calculation.expected_events\n"
    )
    report = run(text, tmp_path)
    details = report["requests"][0]["report"]
    calculation = details["calculation"]
    assert calculation["expected_events"]["decimal_approximation"] == "245.498248"
    assert calculation["formula"] == "schoenfeld_exponential_times"
    assert report["values"]["events"] == "30687281/125000"  # 245.498248
    ids = [item["id"] for item in details["assumptions"]]
    assert "uniform_accrual" in ids and "planning_point_is_input" in ids
    assert any("Lachin" in reference for reference in details["references"])


def test_no_accrual_means_everyone_enters_at_once():
    point = {"value": 0.7, "control_median": 12.0, "accrual": 0.0, "follow_up": 24.0}
    result = log_rank_times(point, 100, 100, 0, 0.05, "both")
    assert result.event_probabilities[0] == pytest.approx(0.75)  # two medians
    near = log_rank_times({**point, "accrual": 1e-9}, 100, 100, 0, 0.05, "both")
    assert near.expected_events == pytest.approx(result.expected_events, rel=1e-6)


@pytest.mark.parametrize(
    ("point", "code", "words"),
    [
        (
            "exponential_survival(hazard_ratio=7/10, control_median=0, accrual=24, follow_up=12)",
            "domain",
            "control_median",
        ),
        (
            "exponential_survival(hazard_ratio=7/10, control_median=12, accrual=0, follow_up=0)",
            "domain",
            "cannot both be 0",
        ),
        (
            "exponential_survival(hazard_ratio=7/10, control_median=12, accrual=24, "
            "follow_up=12, dropout=1/10)",
            "domain",
            "together",
        ),
        (
            "exponential_survival(hazard_ratio=1, control_median=12, accrual=24, follow_up=12)",
            "alternative_in_null",
            "outside the null",
        ),
    ],
)
def test_refusals_explain_the_survival_point(point, code, words):
    found = diagnostics(TRIAL + f"let p = meets(analysis=analysis, target={target(point)})\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_an_events_point_still_refuses_a_size_search_and_names_the_times_point():
    point = "hazard_ratio(value=7/10, events=250)"
    text = TRIAL + (
        "let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=50, max_per_arm=500)\n"
        f"let s = smallest_sample_size(candidates=sizes, target={target(point)})\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "unsupported_claim" and "exponential_survival" in found[0][1]


def test_other_tests_refuse_the_survival_point():
    text = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse planning\n"
        "let study = two_arm_continuous(n_control=50, n_treatment=50)\n"
        "let test = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
        f"let p = meets(analysis=test, target={target()})\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "mean_difference" in found[0][1]


def _derivation(text, name):
    return next(d for d in compile_source(Source(text)).derivations if d.name == name).to_dict()


def test_survival_plans_have_checked_derivations():
    text = TRIAL + (
        "let sizes = equal_arm_sizes(analysis=analysis, min_per_arm=50, max_per_arm=1000)\n"
        f"let search = smallest_sample_size(candidates=sizes, target={target()})\n"
        f"let claim = meets(analysis=analysis, target={target()})\n"
    )
    for name in ("search", "claim"):
        derivation = _derivation(text, name)
        assert check_derivation(derivation) == [], name
        step = next(s for s in derivation["steps"] if s["rule"] == "power-formula")
        assert step["facts"]["formula"] == "schoenfeld_exponential_times"
    derivation = _derivation(text, "claim")
    for change in ({"control_median": "0"}, {"dropout": "1"}, {"accrual": "-1"}):
        altered = copy.deepcopy(derivation)
        step = next(s for s in altered["steps"] if s["rule"] == "power-formula")
        step["facts"]["point"].update(change)
        assert check_derivation(altered), change
    dropped = copy.deepcopy(derivation)
    step = next(s for s in dropped["steps"] if s["rule"] == "power-formula")
    del step["facts"]["point"]["dropout_time"]
    assert check_derivation(dropped)


def test_the_example_and_lesson_plan_from_times():
    for path in ("examples/log_rank.stat", "examples/tutorial/32_survival_power.stat"):
        program = compile_source(Source((ROOT / path).read_text()))
        assert not program.diagnostics, path
        assert all(check_derivation(d.to_dict()) == [] for d in program.derivations), path
