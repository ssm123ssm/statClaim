"""Exact power of the logistic regression trial test: its Wald statistic summed over both
arms' binomial counts, against glm fitted to every table in R."""

import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.power import two_proportions, wald_rejection

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/logistic_wald_r.json").read_text())
LESSON = ROOT / "examples/tutorial/44_logistic_power.stat"


def _f(text):
    return float(Fraction(text))


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize(
    "case", FIXTURE["cases"], ids=lambda c: f"{c['n_control']}-{c['p_treatment']}"
)
def test_power_matches_glm_on_every_table(case):
    """R values from replication/comparison/logistic_wald_r.R; R is not needed here."""
    ours = wald_rejection(
        case["n_control"],
        case["n_treatment"],
        _f(case["alpha"]),
        case["side"],
        _f(case["p_control"]),
        _f(case["p_treatment"]),
    )
    assert ours == pytest.approx(case["power"], abs=1e-12)


def test_an_empty_cell_never_rejects():
    # With rates of 0 and 1 every table has an empty cell: glm cannot reject any of them.
    assert wald_rejection(20, 20, 0.05, "both", 0.0, 1.0) == 0.0


def test_large_samples_approach_the_normal_formula():
    point = {"p_control": 0.3, "p_treatment": 0.4}
    exact = wald_rejection(800, 800, 0.05, "both", 0.3, 0.4)
    assert abs(exact - two_proportions(point, 800, 800, 0, 0.05, "both").power) < 0.01


def test_the_lesson_compares_exact_power_with_the_formula(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    small, search = (r["report"]["calculation"] for r in report["requests"])
    assert small["formula"] == "logistic_wald_enumeration"
    assert _f(small["typeI_at_control_rate"]["fraction"]) < 0.05
    assert search["n_control"] > 0 and search["power_target_met"]
    assert not compile_source(Source(text)).diagnostics
