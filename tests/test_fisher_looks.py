"""Exact power of Fisher's test at interim looks, summed over every path of counts."""

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
from statclaim.looks_planning import fisher_looks
from statclaim.planning import fisher_rejection_probability

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/fisher_looks_r.json").read_text())
LESSON = ROOT / "examples/tutorial/45_fisher_looks.stat"
HEAD = LESSON.read_text().split("# Response rates")[0]
RATES = "binomial_rates(p_control=3/10, p_treatment=1/2)"


def target(point=RATES):
    return f"power_target(at={point}, minimum=4/5, maximum_typeI=1/20)"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("case", FIXTURE["cases"], ids=lambda c: c["alternative"])
def test_stopping_matches_brute_force_in_r(case):
    """R values from replication/comparison/fisher_looks_r.R; R is not needed here."""
    looks = [
        (look["n_control"], look["n_treatment"], Fraction(look["alpha"]), case["alternative"])
        for look in case["looks"]
    ]
    control, treatment = float(Fraction(case["p_control"])), float(Fraction(case["p_treatment"]))
    for rates, theirs in (
        ((control, treatment), case["stopped"]),
        ((control, control), case["stopped_null"]),
    ):
        ours = fisher_looks(looks, *rates)
        assert ours == pytest.approx(theirs, abs=1e-12)


def test_one_look_is_the_exact_fixed_power():
    one = fisher_looks([(60, 60, Fraction(1, 20), "two_sided")], 0.3, 0.55)
    exact = fisher_rejection_probability(60, 60, Fraction(1, 20), Fraction(3, 10), Fraction(11, 20))
    assert sum(one) == pytest.approx(float(exact), abs=1e-12)


def test_the_lesson_reports_each_look(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    calculation = report["requests"][0]["report"]["calculation"]
    first, last = calculation["looks"]
    assert first["n_control"] == 50 and last["alpha"]["fraction"] == "9/200"
    assert calculation["power"]["decimal_approximation"] == "0.785800"
    assert float(calculation["typeI_at_control_rate"]["decimal_approximation"]) < 0.05
    assert float(calculation["expected_sample_size"]["decimal_approximation"]) < 190
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = simulate(meets(analysis=trial, target={target()}), seed=1)",
            "unsupported_claim",
            "calculate",
        ),
        (
            f"let p = verify(meets(analysis=trial, target={target()}))",
            "unsupported_claim",
            "not proved",
        ),
        (
            "let big = two_arm_binomial(n_control=600, n_treatment=600)\n"
            "let late = fisher(design=fixed(model=big), null=equal_proportions(model=big), "
            "alpha=9/200)\n"
            "let wide = alpha_spending(looks=[interim, late], alpha=1/20)\n"
            f"let p = meets(analysis=wide, target={target()})",
            "domain",
            "500 per arm",
        ),
    ],
)
def test_refusals_explain_fisher_looks(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_rejects_an_altered_point():
    text = HEAD + f"let claim = meets(analysis=trial, target={target()})\n"
    derivation = next(
        d for d in compile_source(Source(text)).derivations if d.name == "claim"
    ).to_dict()
    assert check_derivation(derivation) == []
    rules = [step["rule"] for step in derivation["steps"]]
    assert "exact-looks" in rules and "simulation-model" not in rules
    altered = copy.deepcopy(derivation)
    step = next(s for s in altered["steps"] if s["rule"] == "exact-looks")
    step["facts"]["point"]["p_control"] = "2"
    assert check_derivation(altered)
