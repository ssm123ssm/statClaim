"""Prevalence, cumulative incidence and incidence rates: estimability, rates and certificates.

Nothing here starts Lean; tests/test_association_integration.py does.
"""

import copy
import subprocess
from fractions import Fraction
from math import comb
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.incidence import (
    ObservedEvents,
    ProportionEstimate,
    RateRatioInterval,
    RateResult,
    RateTest,
    proportion_assumptions,
    rate_assumptions,
    rate_ratio_assumptions,
    rate_result_assumptions,
    render_rate_proof,
    render_rate_ratio_proof,
    render_rate_result_proof,
    show,
    tails_at,
)
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.identify import identify

ROOT = Path(__file__).resolve().parents[1]
USES = (
    "use models.observational\nuse sampling\nuse tests.association\nuse estimation.observational\n"
)
STUDIES = {
    "cross_sectional": 'let study = cross_sectional(n=800, outcome="insomnia")\n',
    "cohort": "let study = cohort(exposed=200, unexposed=400)\n",
    "population_cohort": "let study = cohort(n=900)\n",
    "case_control": "let study = case_control(cases=100, controls=200)\n",
    "matched": "let study = matched_case_control(pairs=100)\n",
    "person_time": "let study = person_time_cohort()\n",
}
EVENTS = (
    "let counted = observed_events(model=study, exposed_events=48, exposed_time=12500, "
    "unexposed_events=61, unexposed_time=31000)\n"
)
RATE_TEST = (
    "let analysis = rate_test(design=fixed(model=study), null=no_association(model=study), "
    "alpha=1/20)\n"
)


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize(
    "design,measure,extra,expected",
    [
        ("cross_sectional", "prevalence", "", []),
        ("cohort", "prevalence", "", ["not_estimable"]),
        ("cohort", "cumulative_incidence", ', group="exposed"', []),
        ("cohort", "cumulative_incidence", "", ["domain"]),
        ("population_cohort", "cumulative_incidence", "", []),
        ("population_cohort", "cumulative_incidence", ', group="exposed"', ["domain"]),
        ("cross_sectional", "cumulative_incidence", "", ["not_estimable"]),
        ("case_control", "prevalence", "", ["not_estimable"]),
        ("case_control", "cumulative_incidence", "", ["not_estimable"]),
        ("matched", "prevalence", "", ["not_estimable"]),
        ("person_time", "cumulative_incidence", "", ["not_estimable"]),
    ],
)
def test_each_design_estimates_only_its_own_proportion(design, measure, extra, expected):
    text = STUDIES[design] + f"let p = {measure}(model=study, cases=20, level=19/20{extra})\n"
    assert codes(text) == expected


def test_cases_must_fit_the_group():
    text = STUDIES["cohort"] + (
        'let p = cumulative_incidence(model=study, cases=201, level=19/20, group="exposed")\n'
    )
    diagnostics = compiled(text).diagnostics
    assert [d.code for d in diagnostics] == ["domain"] and "between 0 and 200" in diagnostics[
        0
    ].message


def test_a_rate_test_compiles_with_a_checked_derivation():
    compilation = compiled(
        STUDIES["person_time"] + RATE_TEST + EVENTS + "let c = verify(typeI(analysis))\n"
    )
    assert compilation.status == "elaborated", compilation.diagnostics
    record = next(d for d in compilation.derivations if d.name == "analysis").to_dict()
    assert record["contract"] == "tests.association/rate_test"
    assert check_derivation(record) == []
    changed = copy.deepcopy(record)
    changed["subject"]["design"]["model"]["study"] = "cohort"
    assert check_derivation(changed) != []
    null = next(b.value for b in compilation.program.bindings if b.name == "analysis").hypothesis
    assert null.statement == "rate_exposed = rate_unexposed"


@pytest.mark.parametrize(
    "text,code",
    [
        (
            STUDIES["person_time"]
            + "let t = fisher_exact(design=fixed(model=study), null=no_association(model=study), "
            "alpha=1/20)\n",
            "type",
        ),
        (
            STUDIES["person_time"]
            + "let t = observed_table(model=study, exposed_cases=1, exposed_noncases=1, "
            "unexposed_cases=1, unexposed_noncases=1)\n",
            "type",
        ),
        (STUDIES["cohort"] + RATE_TEST, "type"),
        (STUDIES["person_time"] + EVENTS.replace("12500", "0"), "domain"),
        (STUDIES["person_time"] + EVENTS.replace("=48", "=480"), "domain"),
        (
            STUDIES["person_time"]
            + EVENTS.replace("=48", "=0").replace("=61", "=0")
            + "let r = rate_ratio(events=counted, level=19/20)\n",
            "domain",
        ),
    ],
)
def test_rates_and_counts_of_participants_do_not_mix(text, code):
    assert codes(text)[0] == code


def test_rates_and_proportions_calculate_exactly(tmp_path):
    text = (
        STUDIES["person_time"]
        + RATE_TEST
        + EVENTS
        + "let found = calculate(rate_result(analysis=analysis, events=counted))\n"
        + "let ratio = calculate(rate_ratio(events=counted, level=19/20))\n"
        + "let survey = cross_sectional(n=800)\n"
        + "let common = calculate(prevalence(model=survey, cases=152, level=19/20))\n"
        + "let p = found.calculation.p_value\n"
    )
    report = check_source(Source(USES + text, "study.stat"), project=ROOT, output=tmp_path / "r")
    assert report["status"] == "calculated"
    found, ratio, common = (request["report"]["calculation"] for request in report["requests"])
    share = Fraction(12500, 43500)
    a, d = share.as_integer_ratio()
    upper = sum(comb(109, k) * a**k * (d - a) ** (109 - k) for k in range(48, 110))
    lower = sum(comb(109, k) * a**k * (d - a) ** (109 - k) for k in range(0, 49))
    expected = min(Fraction(1), Fraction(2 * min(upper, lower), d**109))
    assert Fraction(found["p_value"]["fraction"]) == expected
    assert report["values"]["p"] == str(expected)
    assert Fraction(ratio["estimate"]["fraction"]) == Fraction(48 * 31000, 12500 * 61)
    assert Fraction(common["estimate"]["fraction"]) == Fraction(152, 800)


EVENTS_OBJECT = ObservedEvents(48, Fraction(12500), 61, Fraction(31000), "night shifts", "cancer")
TEST_OBJECT = RateTest(Fraction(1, 20), "night shifts", "cancer")


def test_proofs_tails_and_assumptions():
    assert tails_at(4, 2, Fraction(1, 2)) == (11, 11, 16)
    assert show(Fraction(16843, 2)) == "8421.5" and show(Fraction(1, 3)) == "1/3"
    assert "Incidence.typeI" in render_rate_proof(TEST_OBJECT, "a" * 64)
    result = RateResult(TEST_OBJECT, EVENTS_OBJECT)
    proof = render_rate_result_proof(result, "a" * 64)
    assert "ratPoint 12500 43500" not in proof and "ratPoint 25 87" in proof
    assert "Incidence.twice_min_le_iff" in proof
    no_unexposed = RateRatioInterval(
        ObservedEvents(7, Fraction(1234), 0, Fraction(2345)), Fraction(19, 20)
    )
    assert no_unexposed.bounds[1] is None and no_unexposed.estimate is None
    assert (
        "∧"
        not in render_rate_ratio_proof(no_unexposed, "a" * 64)
        .split("checked_interval")[1]
        .split(":=")[0]
    )
    estimate = ProportionEstimate(
        "cumulative_incidence", "cohort", 200, 30, Fraction(19, 20), group="exposed"
    )
    for texts in (
        rate_assumptions(),
        rate_result_assumptions(result),
        rate_ratio_assumptions(no_unexposed),
        proportion_assumptions(estimate),
    ):
        assert all(identify(text)["id"] for text in texts)


def test_the_lesson_and_example_compile():
    for name in ("examples/tutorial/26_prevalence_and_rates.stat", "examples/incidence_rates.stat"):
        path = ROOT / name
        compilation = compile_source(Source(path.read_text(), str(path)))
        assert compilation.status == "elaborated", (name, compilation.diagnostics)
