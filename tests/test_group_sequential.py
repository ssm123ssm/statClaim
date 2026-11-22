"""Power of a design with interim looks, by simulation: stopping at each look, the expected
size, and the simulated Type I error beside the proved bound."""

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
FIXTURE = json.loads((ROOT / "tests/fixtures/group_sequential_r.json").read_text())
LESSON = ROOT / "examples/tutorial/41_interim_power.stat"
HEAD = (
    "use models.two_arm_continuous\nuse models.two_arm_binomial\nuse sampling\nuse tests.t\n"
    "use tests.fisher\nuse designs.group_sequential\nuse planning\n"
    "let halfway = two_arm_continuous(n_control=50, n_treatment=50)\n"
    "let complete = two_arm_continuous(n_control=100, n_treatment=100)\n"
    "let interim = t_test(design=fixed(model=halfway), null=equal_means(model=halfway), "
    "alpha=1/200)\n"
    "let final = t_test(design=fixed(model=complete), null=equal_means(model=complete), "
    "alpha=9/200)\n"
    "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\n"
)
POINT = "mean_difference(value=5, sd=10)"


def _f(text):
    return float(Fraction(text))


def target(point=POINT, maximum="1/20"):
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


@pytest.mark.parametrize("case", FIXTURE["cases"], ids=lambda c: f"{c['test']}-{len(c['looks'])}")
def test_stopping_rates_agree_with_a_raw_data_simulation_in_r(case):
    """R values from replication/comparison/group_sequential_r.R; R is not needed here."""
    looks = [(look["n_control"], look["n_treatment"], _f(look["alpha"])) for look in case["looks"]]
    runs = 20000
    for difference, theirs in (
        (_f(case["difference"]), case["stopped"]),
        (0.0, case["stopped_null"]),
    ):
        trial = engine.sequential_two_means_trial(
            difference,
            _f(case["sd"]),
            looks,
            0.0,
            case["side"],
            case["test"] == "welch",
            skewness=_f(case["skewness"]),
        )
        found = engine.estimate_looks(trial, len(looks), runs, engine.Stream(7, "r", difference))
        for ours, rate in zip(found.stopped, theirs, strict=True):
            assert _close(ours / runs, runs, rate, case["runs"]), (found.stopped, theirs)
        assert _close(found.overall.rate, runs, sum(theirs), case["runs"])


def test_a_single_look_is_the_plain_test():
    plain = engine.two_means_trial(5, 10, 60, 60, 0, 0.05, "both", False)
    once = engine.sequential_two_means_trial(5, 10, [(60, 60, 0.05)], 0, "both", False)
    runs = 20000
    first = engine.estimate(plain, runs, engine.Stream(3, "a")).rate
    second = engine.estimate_looks(once, 1, runs, engine.Stream(3, "b")).overall.rate
    assert _close(first, runs, second, runs)


def test_the_lesson_reports_looks_and_the_expected_size(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    looked, once = (r["report"]["calculation"] for r in report["requests"])
    first, last = looked["looks"]
    assert first["n_control"] == 50 and last["alpha"]["fraction"] == "9/200"
    # The look stops a good share of trials early, so fewer participants are expected.
    assert _f(first["stop"]["fraction"]) > 0.25
    assert _f(looked["expected_sample_size"]["fraction"]) < 175
    assert _f(looked["expected_sample_size_null"]["fraction"]) > 199
    # The split is conservative: simulated Type I is below the proved 1/20, and the look
    # costs little power against one analysis at the full level.
    assert _f(looked["typeI_upper"]["fraction"]) < 0.06 and not looked["typeI_judged"]
    assert abs(_f(looked["power"]["fraction"]) - _f(once["power"]["fraction"])) < 0.02
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = calculate(meets(analysis=trial, target={target()}))",
            "unsupported_claim",
            "simulate",
        ),
        (
            f"let p = verify(meets(analysis=trial, target={target()}))",
            "unsupported_claim",
            "cannot",
        ),
        (
            "let a = fisher(design=fixed(model=two_arm_binomial(n_control=50, n_treatment=50)), "
            "null=equal_proportions(model=two_arm_binomial(n_control=50, n_treatment=50)), "
            "alpha=1/200)\n"
            "let b = fisher(design=fixed(model=two_arm_binomial(n_control=100, n_treatment=100)), "
            "null=equal_proportions(model=two_arm_binomial(n_control=100, n_treatment=100)), "
            "alpha=9/200)\n"
            "let exact = alpha_spending(looks=[a, b], alpha=1/20)\n"
            "let p = simulate(meets(analysis=exact, target=power_target(at=binomial_rates("
            "p_control=3/10, p_treatment=1/2), minimum=4/5, maximum_typeI=1/20)), seed=1)",
            "unsupported_claim",
            "calculate",
        ),
    ],
)
def test_refusals_explain_designs_with_looks(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_rederives_the_looks():
    text = HEAD + f"let claim = meets(analysis=trial, target={target()})\n"
    program = compile_source(Source(text))
    derivation = next(d for d in program.derivations if d.name == "claim").to_dict()
    assert check_derivation(derivation) == []
    rules = [step["rule"] for step in derivation["steps"]]
    assert {"increasing-looks", "simulation-model", "sequential-planning-contract"} <= set(rules)
    for change in ("point", "level"):
        altered = copy.deepcopy(derivation)
        if change == "point":
            step = next(s for s in altered["steps"] if s["rule"] == "simulation-model")
            step["facts"]["point"]["sd"] = "0"
        else:
            altered["subject"]["subject"]["analysis"]["alpha"] = "1/10"
        assert check_derivation(altered), change
