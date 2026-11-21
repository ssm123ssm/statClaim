"""Precision targets for planned intervals: margins of error, absolute or relative, and
assurance."""

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
from statclaim.precision import Plan, arm_level

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/precision_r.json").read_text())
LESSON = ROOT / "examples/tutorial/36_precision.stat"
HEAD = (
    "use models.observational\nuse models.two_arm_binomial\nuse tests.binomial\nuse sampling\n"
    "use planning\n"
)
SURVEY = HEAD + (
    'let survey = cross_sectional(n=400, exposure="smoking", outcome="asthma")\n'
    'let estimate = planned_interval(model=survey, measure="prevalence")\n'
)


EFFECT = "proportion(value=1/10, design_effect=2)"


def _f(text):
    return float(Fraction(text))


def run(text, tmp_path):
    return check_source(Source(text, "precision.stat"), project=ROOT, output=tmp_path / "run")


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


def target(point="proportion(value=1/10)", rest="margin_of_error=3/100"):
    return f"precision_target(at={point}, level=19/20, {rest})"


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("case", FIXTURE["singles"], ids=lambda c: f"{c['p']}-{c['n']}")
def test_a_proportion_agrees_with_binom_test(case):
    """R values from replication/comparison/precision_r.R; R is not needed here."""
    p = _f(case["p"])
    plan = Plan("proportion", "exact", Fraction(case["level"]), (p,), p)
    bounds, _ = plan.expected((case["n"],))
    assert plan.margin(bounds, False) == pytest.approx(case["expected_margin"], abs=1e-12)
    assurance = plan.assurance((case["n"],), False, _f(case["margin"]))
    assert assurance == pytest.approx(case["assurance"], abs=1e-11)
    if "presize_exact" in case:  # presize does not round to the grid
        assert abs(plan.margin(bounds, False) - case["presize_exact"]) < 1e-4


@pytest.mark.parametrize("case", FIXTURE["pairs"], ids=lambda c: f"{c['kind']}-{c['relative']}")
def test_two_groups_agree_with_r(case):
    p0, p1 = _f(case["p0"]), _f(case["p1"])
    value = {"difference": p1 - p0, "ratio": p1 / p0, "odds": (p1 / (1 - p1)) / (p0 / (1 - p0))}
    plan = Plan(case["kind"], "exact", Fraction(case["level"]), (p0, p1), value[case["kind"]])
    sizes = (case["n0"], case["n1"])
    bounds, _ = plan.expected(sizes)
    assert plan.margin(bounds, case["relative"]) == pytest.approx(
        case["expected_margin"], abs=1e-12
    )
    assert plan.assurance(sizes, case["relative"], _f(case["margin"])) == pytest.approx(
        case["assurance"], abs=1e-11
    )


def test_matched_pairs_and_rates_agree_with_r():
    case = FIXTURE["matched"]
    psi = _f(case["odds_ratio"])
    plan = Plan(
        "matched",
        "exact",
        Fraction(case["level"]),
        (psi / (1 + psi),),
        psi,
        share=_f(case["share"]),
    )
    assert plan.assurance((case["pairs"],), True, _f(case["margin"])) == pytest.approx(
        case["assurance"], abs=1e-11
    )
    case = FIXTURE["rates"]
    ratio, exposed, unexposed = (
        _f(case[k]) for k in ("rate_ratio", "exposed_time", "unexposed_time")
    )
    share = exposed * ratio / (exposed * ratio + unexposed)
    plan = Plan(
        "rate", "exact", Fraction(case["level"]), (share,), ratio, scale=unexposed / exposed
    )
    assert plan.assurance((case["events"],), True, _f(case["margin"])) == pytest.approx(
        case["assurance"], abs=1e-11
    )


@pytest.mark.parametrize("case", FIXTURE["normals"], ids=lambda c: c["kind"])
def test_normal_intervals_agree_with_presize(case):
    level = Fraction(case["level"])
    if case["kind"] == "proportion":
        p = _f(case["p"])
        plan = Plan("proportion", "normal", level, (p,), p)
        sizes = (case["n"],)
    else:
        p0, p1 = _f(case["p0"]), _f(case["p1"])
        value = {"difference": p1 - p0, "ratio": p1 / p0, "odds": (p1 / (1 - p1)) / (p0 / (1 - p0))}
        plan = Plan(case["kind"], "normal", level, (p0, p1), value[case["kind"]])
        sizes = (case["n0"], case["n1"])
    bounds, _ = plan.expected(sizes)
    assert plan.margin(bounds, False) == pytest.approx(case["presize"], abs=1e-9)


def test_the_arm_level_is_statclaims():
    assert arm_level(Fraction(19, 20)) == Fraction(9747, 10000)


def test_the_lesson_plans_a_prevalence_and_more(tmp_path):
    text = LESSON.read_text()
    report = run(text, tmp_path)
    found = [request["report"]["calculation"] for request in report["requests"]]
    declared, smallest, assured, survey, risk_ratio = found
    assert declared["margin_achieved"]["decimal_approximation"] == "0.030650"
    assert not declared["precision_target_met"]
    assert smallest["total_sample_size"] == 417
    assert assured["total_sample_size"] == 457
    assert assured["assurance"]["decimal_approximation"] >= "0.8"
    # Cochran's size with the design effect and the finite population, as in R.
    assert survey["total_sample_size"] == FIXTURE["cochran"]["n"]
    assert risk_ratio["exposed"] * 2 == risk_ratio["unexposed"]
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


def test_fields_read_from_a_precision_result(tmp_path):
    text = SURVEY + (
        f"let result = calculate(meets(analysis=estimate, target={target()}))\n"
        "let margin = result.calculation.margin_achieved\n"
        "let met = result.calculation.precision_target_met\n"
    )
    report = run(text, tmp_path)
    assert report["values"]["margin"] == "613/20000"
    assert report["values"]["met"] is False


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let v = verify(meets(analysis=estimate, target={target()}))",
            "unsupported_claim",
            "Lean",
        ),
        (
            "let s = smallest_sample_size(candidates=interval_sizes(interval=estimate, "
            "min_size=10, "
            f"max_size=999), target={target(rest='margin_of_error=3/100, assurance=4/5')})",
            "unsupported_claim",
            "sample_size",
        ),
        (
            "let t = precision_target(at=proportion(value=1/10), level=19/20, "
            "margin_of_error=1/50, "
            "relative_margin_of_error=1/5)",
            "domain",
            "one of",
        ),
        (
            "let p = meets(analysis=estimate, target=power_target(at=proportion(value=1/10), "
            "minimum=4/5, maximum_typeI=1/20))",
            "planning_point",
            "precision_target",
        ),
        (
            f"let p = meets(analysis=estimate, target={target(EFFECT)})",
            "planning_point",
            'method="normal"',
        ),
        (
            'let x = planned_interval(model=survey, measure="risk_ratio")',
            "not_estimable",
            "prevalence",
        ),
        (
            "let s = interval_sizes(interval=estimate, min_size=10, max_size=100, ratio=2)",
            "domain",
            "two groups",
        ),
    ],
)
def test_refusals_explain_precision_planning(line, code, words):
    found = diagnostics(SURVEY + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_a_complex_survey_needs_the_normal_interval_and_its_design_effect():
    text = HEAD + (
        'let national = cross_sectional(n=2000, exposure="e", outcome="o", survey="cluster", '
        "clusters=100)\n"
    )
    found = diagnostics(text + 'let x = planned_interval(model=national, measure="prevalence")\n')
    assert found[0][0] == "complex_sample" and 'method="normal"' in found[0][1]
    text += 'let x = planned_interval(model=national, measure="prevalence", method="normal")\n'
    found = diagnostics(text + f"let p = meets(analysis=x, target={target()})\n")
    assert found[0][0] == "planning_point" and "design_effect" in found[0][1]


def test_a_ratio_takes_a_relative_margin_below_one():
    text = HEAD + (
        'let followed = cohort(exposed=300, unexposed=600, exposure="e", outcome="o")\n'
        'let rr = planned_interval(model=followed, measure="risk_ratio")\n'
        "let p = meets(analysis=rr, target=precision_target(at=risks(unexposed=1/10, "
        "risk_ratio=2), level=19/20, relative_margin_of_error=1))\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "domain" and "(1 - r)" in found[0][1]


def _derivation(text, name):
    return next(d for d in compile_source(Source(text)).derivations if d.name == name).to_dict()


def test_the_checker_rejects_altered_precision_plans():
    text = SURVEY + (
        f"let claim = meets(analysis=estimate, target={target()})\n"
        "let search = smallest_sample_size(candidates=interval_sizes(interval=estimate, "
        f"min_size=10, max_size=5000), target={target()})\n"
    )
    for name in ("claim", "search"):
        assert check_derivation(_derivation(text, name)) == [], name
    claim = _derivation(text, "claim")
    for rule, change in (
        ("precision-point", {"proportion": "1"}),
        ("precision-target", {"level": "1"}),
        ("precision-target", {"margin_of_error": "0"}),
    ):
        altered = copy.deepcopy(claim)
        step = next(s for s in altered["steps"] if s["rule"] == rule)
        facts = step["facts"]["point" if rule == "precision-point" else "target"]
        facts.update(change)
        assert check_derivation(altered), (rule, change)
    search = _derivation(text, "search")
    widened = copy.deepcopy(search)
    step = next(s for s in widened["steps"] if s["rule"] == "search-range")
    step["facts"]["search"]["max_size"] = 10**7
    assert check_derivation(widened)
