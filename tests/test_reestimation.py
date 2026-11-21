"""Blinded sample-size re-estimation: power, and Type I error judged at declared nulls."""

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
FIXTURE = json.loads((ROOT / "tests/fixtures/reestimation_r.json").read_text())
LESSON = ROOT / "examples/tutorial/42_reestimation.stat"
HEAD = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse tests.cluster\n"
    "use designs.adaptive\nuse planning\n"
    "let study = two_arm_continuous(n_control=64, n_treatment=64)\n"
    "let final = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
    "let trial = blinded_reestimation(analysis=final, interim_per_arm=30, difference=5, "
    "power=4/5, max_per_arm=200)\n"
    "let nulls = null_scenarios(at=[mean_difference(value=0, sd=6), "
    "mean_difference(value=0, sd=14)])\n"
)


def target(point="mean_difference(value=5, sd=14)", nulls=", nulls=nulls"):
    return f"power_target(at={point}, minimum=3/4, maximum_typeI=3/40{nulls})"


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


@pytest.mark.parametrize("row", FIXTURE["scenarios"], ids=lambda r: f"sd{r['sd']}")
def test_rates_and_sizes_agree_with_a_raw_data_simulation_in_r(row):
    """R values from replication/comparison/reestimation_r.R; R is not needed here."""
    design = FIXTURE["design"]
    runs = 20000
    for difference, rate, per_arm in (
        (0.0, row["typeI"], row["null_per_arm"]),
        (5.0, row["power"], row["power_per_arm"]),
    ):
        trial = engine.blinded_reestimation_trial(
            difference,
            row["sd"],
            design["initial"],
            design["interim"],
            design["largest"],
            5.0,
            0.8,
            0.0,
            0.05,
            "both",
        )
        found = engine.estimate_sized(trial, runs, engine.Stream(7, "r", difference, row["sd"]))
        assert _close(found.found.rate, runs, rate, row["runs"]), (found.found.rate, rate)
        assert abs(float(found.mean_per_arm) - per_arm) < 0.03 * per_arm + 0.5


def test_the_rule_recomputes_the_textbook_size():
    # 2 x 100 x (1.96 + 0.8416)^2 / 25 = 62.8, so 63 per arm at an SD of 10.
    assert engine.reestimated_size(100, 5, 0.8, 0.025) == 63


def test_the_lesson_judges_type_one_at_each_null(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    adapted, unadapted = (r["report"]["calculation"] for r in report["requests"])
    assert [null["sd"]["fraction"] for null in adapted["null_scenarios"]] == ["6", "10", "14"]
    assert all(null["typeI_target_met"] for null in adapted["null_scenarios"])
    assert adapted["typeI_judged"] and adapted["typeI_target_met"]
    # Re-estimation rescues the power that a misjudged SD costs the fixed design.
    assert Fraction(adapted["power_lower"]["fraction"]) > Fraction(3, 4)
    assert Fraction(unadapted["power_upper"]["fraction"]) < Fraction(3, 5)
    assert Fraction(adapted["expected_sample_size"]["fraction"]) > 200
    decisions = [r["report"]["decision"] for r in report["requests"]]
    assert decisions == ["target_met", "target_not_met"]
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = meets(analysis=trial, target={target(nulls='')})",
            "planning_point",
            "not proved",
        ),
        (
            "let p = meets(analysis=trial, target=power_target(at=mean_difference(value=5, sd=14), "
            "minimum=3/4, maximum_typeI=3/40, nulls=null_scenarios(at=[mean_difference(value=1, "
            "sd=10)])))",
            "planning_point",
            "on the null",
        ),
        (
            f"let p = meets(analysis=final, target={target()})",
            "planning_point",
            "blinded_reestimation",
        ),
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
            "let w = welch_test(design=fixed(model=study), null=equal_means(model=study), "
            "alpha=1/20)\n"
            "let r = blinded_reestimation(analysis=w, interim_per_arm=30, difference=5, power=4/5, "
            "max_per_arm=200)",
            "unsupported_claim",
            "Student",
        ),
        (
            "let r = blinded_reestimation(analysis=final, interim_per_arm=64, difference=5, "
            "power=4/5, max_per_arm=200)",
            "domain",
            "below the planned 64",
        ),
    ],
)
def test_refusals_explain_reestimation(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_rejects_altered_rules_and_nulls():
    text = HEAD + f"let claim = meets(analysis=trial, target={target()})\n"
    program = compile_source(Source(text))
    derivation = next(d for d in program.derivations if d.name == "claim").to_dict()
    assert check_derivation(derivation) == []
    analysis = derivation["subject"]["subject"]["analysis"]
    for change in ("interim", "null"):
        altered = copy.deepcopy(derivation)
        if change == "interim":
            altered["subject"]["subject"]["analysis"]["interim_per_arm"] = 99
        else:
            altered["subject"]["subject"]["target"]["nulls"][0]["mean_difference"] = "2"
        assert check_derivation(altered), change
    assert analysis["rule"] == "blinded_reestimation"
