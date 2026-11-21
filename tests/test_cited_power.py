"""Approximate power for cited tests: a calculation, never evidence and never a bound."""

import copy
import json
import math
import subprocess
from pathlib import Path
from statistics import NormalDist

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import best_status, inspect_program, weakest_link
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.methods import METHODS, POWER_FORMULAS
from statclaim.methods.power import log_rank_events, two_means, two_proportions

ROOT = Path(__file__).resolve().parents[1]
CONTINUOUS = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse tests.mixed_model\n"
    "use planning\n"
    "let study = two_arm_continuous(n_control=440, n_treatment=440)\n"
    "let plan = fixed(model=study)\n"
    "let ni = mmrm_test_one_sided(design=plan, "
    "null=mean_difference_at_most(model=study, value=-50), alpha=1/40)\n"
)
POINT = "mean_difference(value=-10, sd=167)"


def target(point=POINT, minimum="9/10", maximum="1/40"):
    return f"power_target(at={point}, minimum={minimum}, maximum_typeI={maximum})"


def run(text, tmp_path):
    return check_source(Source(text, "power.stat"), project=ROOT, output=tmp_path / "run")


def codes(text):
    return [d.code for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


# Values from the normal formulas, computed by hand from the formulas in the docs.
# (formula, point, n_control, n_treatment, null value, alpha, side,
#  power, critical estimate, direction)
PINNED = [
    (
        two_means,
        {"value": -10, "sd": 167},
        440,
        440,
        -50,
        0.025,
        "higher",
        0.944387,
        -27.9325,
        "above",
    ),
    (
        two_means,
        {"value": -10, "sd": 167},
        440,
        440,
        -50,
        0.0125,
        "higher",
        0.905116,
        -24.7637,
        "above",
    ),
    (
        two_means,
        {"value": 50, "sd": 188},
        500,
        500,
        0,
        0.0125,
        "higher",
        0.975221,
        26.6506,
        "above",
    ),
    (
        two_means,
        {"value": 0, "sd": 3},
        440,
        440,
        -0.75,
        0.025,
        "higher",
        0.959780,
        -0.35358,
        "above",
    ),
    (two_means, {"value": -3, "sd": 12}, 400, 400, 0, 0.05, "both", 0.942438, -1.66309, "below"),
    (two_means, {"value": 5, "sd": 10}, 40, 80, 0, 0.05, "both", 0.733037, 3.79545, "above"),
    (
        two_proportions,
        {"p_control": 0.3, "p_treatment": 0.5},
        100,
        100,
        0,
        0.05,
        "both",
        0.828109,
        0.135790,
        "above",
    ),
    (
        two_proportions,
        {"p_control": 0.4, "p_treatment": 0.2},
        60,
        120,
        0,
        0.05,
        "both",
        0.805681,
        -0.137042,
        "below",
    ),
    (
        log_rank_events,
        {"value": 0.7, "events": 250},
        200,
        200,
        0,
        0.05,
        "both",
        0.80505,
        0.780424,
        "below",
    ),
    (
        log_rank_events,
        {"value": 1.5, "events": 120},
        100,
        200,
        0,
        0.05,
        "both",
        0.553239,
        1.46162,
        "above",
    ),
]


@pytest.mark.parametrize("case", PINNED, ids=lambda case: f"{case[0].__name__}-{case[7]}")
def test_formulas_give_the_pinned_normal_values(case):
    formula, point, nc, nt, null_value, alpha, side, power, critical, direction = case
    result = formula(point, nc, nt, null_value, alpha, side)
    assert result.power == pytest.approx(power, abs=1e-6)
    assert result.critical == pytest.approx(critical, rel=1e-5)
    assert result.direction == direction


def test_two_means_matches_the_textbook_expression():
    """Power = Phi((delta - margin) / SE - z_(1 - alpha)), SE = sd * sqrt(1/n1 + 1/n2)."""
    normal = NormalDist()
    se = 167 * math.sqrt(2 / 440)
    expected = normal.cdf(40 / se - normal.inv_cdf(1 - 0.025))
    assert two_means({"value": -10, "sd": 167}, 440, 440, -50, 0.025, "higher").power == expected


def test_r_values_agree_within_the_stated_tolerance():
    """Base R values from tests/fixtures/power_r.R (R is not needed to run this test).

    power.prop.test uses the same normal formula, so it agrees to 1e-9. power.t.test uses
    the noncentral t distribution; with 400 or more per arm the normal value is higher by
    less than 0.001.
    """
    fixture = json.loads((ROOT / "tests/fixtures/power_r.json").read_text())
    assert fixture["cases"]
    for case in fixture["cases"]:
        side = "higher" if case["alternative"] == "one.sided" else "both"
        if case["function"] == "power.t.test":
            point = {"value": case["delta"], "sd": case["sd"]}
            result = two_means(point, case["n"], case["n"], 0, case["alpha"], side)
            assert 0 <= result.power - case["power"] < 0.001, case
        else:
            point = {"p_control": case["p1"], "p_treatment": case["p2"]}
            result = two_proportions(point, case["n"], case["n"], 0, case["alpha"], side)
            assert result.power == pytest.approx(case["power"], abs=1e-9), case


def test_every_method_with_a_formula_names_assumptions_and_references():
    assert {m.power.key for m in METHODS.values() if m.power} == set(POWER_FORMULAS)
    for formula in POWER_FORMULAS.values():
        assert formula.assumptions and formula.references
        # Each says how power is approximated: a normal formula, or the noncentral t.
        ids = {a.id for a in formula.assumptions}
        assert ids & {"normal_approximation_power", "noncentral_t_power"}
    assert "proportional_hazards" in [a.id for a in METHODS["log_rank"].power.assumptions]
    assert "proportional_hazards" not in [a.id for a in METHODS["log_rank"].assumptions]


def test_calculate_reports_approximate_power_with_status_calculated(tmp_path):
    text = (
        CONTINUOUS
        + f"let power = calculate(meets(analysis=ni, target={target()}))\n"
        + "let value = power.calculation.power\n"
        + "let critical = power.calculation.critical_estimate\n"
    )
    report = run(text, tmp_path)
    assert report["status"] == "calculated"
    assert not report["backend_invoked"] and not report["certificate_issued"]
    request = report["requests"][0]
    assert request["status"] == "calculated"
    assert request["value"]["status"] == "calculated"
    details = request["report"]
    calculation = details["calculation"]
    assert calculation["power"]["decimal_approximation"] == "0.944387"
    assert calculation["critical_estimate"]["decimal_approximation"] == "-27.932496"
    assert calculation["reject_when"] == "above"
    assert calculation["power_target_met"] and calculation["typeI_target_met"]
    assert details["decision"] == "target_met"
    assert report["values"]["value"] == "944387/1000000"
    ids = [item["id"] for item in details["assumptions"]]
    assert "missing_at_random" in ids and "normal_approximation_power" in ids
    assert "planning_standard_deviation" in ids
    assert any("Julious" in reference for reference in details["references"])
    rendered = render_report(report, Source(text, "power.stat"))
    assert "normal approximation, not a bound" in rendered
    assert "rejects when the estimate is above -27.93" in rendered
    assert "Program status: calculated" in rendered


def test_verify_is_refused_and_points_to_calculate():
    text = CONTINUOUS + f"verify(meets(analysis=ni, target={target()}))\n"
    diagnostics = compile_source(Source(text)).diagnostics
    assert [d.code for d in diagnostics] == ["unsupported_claim"]
    assert "calculate" in diagnostics[0].message


def test_level_above_the_requested_bound_misses_the_target(tmp_path):
    text = CONTINUOUS + f"let claim = meets(analysis=ni, target={target(maximum='1/80')})\n"
    text += "calculate(claim)\n"
    report = run(text, tmp_path)
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["power_target_met"] and not calculation["typeI_target_met"]
    assert report["requests"][0]["report"]["decision"] == "target_not_met"
    derivation = next(d for d in compile_source(Source(text)).derivations if d.name == "claim")
    assert [o.rule for o in derivation.obligations] == ["cited-error-budget"]
    assert check_derivation(derivation.to_dict()) == []


@pytest.mark.parametrize(
    ("point", "code"),
    [
        ("mean_difference(value=-60, sd=167)", "alternative_in_null"),
        ("mean_difference(value=-50, sd=167)", "alternative_in_null"),
        ("binomial_rates(p_control=1/5, p_treatment=2/5)", "planning_point"),
        ("mean_difference(value=-10, sd=0)", "domain"),
    ],
)
def test_planning_point_must_fit_and_lie_outside_the_null(point, code):
    assert codes(CONTINUOUS + f"calculate(meets(analysis=ni, target={target(point)}))\n") == [code]


def test_exact_analysis_rejects_a_cited_planning_point():
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.fisher\nuse planning\n"
        "let study = two_arm_binomial(n_control=20, n_treatment=20)\n"
        "let test = fisher(design=fixed(model=study), null=equal_proportions(model=study), "
        "alpha=1/20)\n"
    )
    for point in ("mean_difference(value=1, sd=2)", "hazard_ratio(value=1/2, events=10)"):
        meets = text + f"calculate(meets(analysis=test, target={target(point)}))\n"
        assert codes(meets) == ["planning_point"]
        search = (
            text
            + "let sizes = equal_arm_sizes(analysis=test, min_per_arm=5, max_per_arm=50)\n"
            + f"calculate(sample_size(candidates=sizes, target={target(point)}))\n"
        )
        assert codes(search) == ["planning_point"]


def test_two_sided_point_at_zero_is_in_the_null():
    text = (
        CONTINUOUS
        + "let two = t_test(design=plan, null=equal_means(model=study), alpha=1/20)\n"
        + f"calculate(meets(analysis=two, target={target('mean_difference(value=0, sd=5)')}))\n"
    )
    assert codes(text) == ["alternative_in_null"]


def test_a_test_without_a_formula_gets_a_clear_diagnostic():
    text = (
        CONTINUOUS
        + "use tests.declared\n"
        + "let own = declared_test(design=plan, null=equal_means(model=study), alpha=1/20, "
        + 'method="Van Elteren test")\n'
        + f"calculate(meets(analysis=own, target={target('mean_difference(value=3, sd=5)')}))\n"
    )
    diagnostics = compile_source(Source(text)).diagnostics
    assert [d.code for d in diagnostics] == ["no_power_formula"]
    assert "t_test" in diagnostics[0].message


SURVIVAL = (
    "use models.two_arm_survival\nuse sampling\nuse tests.survival\nuse planning\n"
    "let study = two_arm_survival(n_control=200, n_treatment=200)\n"
    "let test = log_rank(design=fixed(model=study), null=equal_survival(model=study), "
    "alpha=1/20)\n"
)


def test_log_rank_power_uses_events_and_cannot_search_arm_sizes(tmp_path):
    point = "hazard_ratio(value=7/10, events=250)"
    report = run(
        SURVIVAL + f"calculate(meets(analysis=test, target={target(point, '4/5', '1/20')}))\n",
        tmp_path,
    )
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["power"]["decimal_approximation"] == "0.805050"
    assert calculation["reject_when"] == "below"
    ids = [item["id"] for item in report["requests"][0]["report"]["assumptions"]]
    assert "proportional_hazards" in ids and "planning_events" in ids
    too_many = "hazard_ratio(value=7/10, events=401)"
    assert codes(SURVIVAL + f"calculate(meets(analysis=test, target={target(too_many)}))\n") == [
        "planning_point"
    ]
    search = (
        SURVIVAL
        + "let sizes = equal_arm_sizes(analysis=test, min_per_arm=10, max_per_arm=100)\n"
        + f"calculate(sample_size(candidates=sizes, target={target(point)}))\n"
    )
    assert codes(search) == ["unsupported_claim"]


def test_search_returns_the_first_equal_arm_size_reaching_the_target(tmp_path):
    text = (
        CONTINUOUS
        + "let sizes = equal_arm_sizes(analysis=ni, min_per_arm=10, max_per_arm=2000)\n"
        + f"let search = smallest_sample_size(candidates=sizes, target={target()})\n"
        + "let found = calculate(search)\n"
        + "let n = found.calculation.n_control\n"
    )
    report = run(text, tmp_path)
    normal = NormalDist()
    z = normal.inv_cdf(1 - 1 / 40) + normal.inv_cdf(9 / 10)
    closed_form = math.ceil(2 * (z * 167 / 40) ** 2)
    assert report["values"]["n"] == closed_form == 367
    assert report["requests"][0]["report"]["calculation"]["candidates_evaluated"] == 358
    derivation = next(d for d in compile_source(Source(text)).derivations if d.name == "search")
    assert check_derivation(derivation.to_dict()) == []
    exhausted = text.replace("max_per_arm=2000", "max_per_arm=50")
    report = run(exhausted, tmp_path / "second")
    assert report["requests"][0]["report"]["decision"] == "no_feasible_candidate"
    assert report["requests"][0]["status"] == "calculated"


RATES = "binomial_rates(p_control=3/10, p_treatment=1/2)"


def test_logistic_power_matches_the_two_proportion_formula(tmp_path):
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.logistic\nuse planning\n"
        "let study = two_arm_binomial(n_control=100, n_treatment=100)\n"
        "let test = logistic_regression_one_sided(design=fixed(model=study), "
        "null=proportion_difference_at_most(model=study, value=0), alpha=1/40)\n"
        f"calculate(meets(analysis=test, target={target(RATES, '4/5')}))\n"
    )
    report = run(text, tmp_path)
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["power"]["decimal_approximation"] == "0.828109"
    ids = [item["id"] for item in report["requests"][0]["report"]["assumptions"]]
    assert "unadjusted_proportions" in ids


def test_adaptive_design_leaves_the_calculation_unresolved(tmp_path):
    text = CONTINUOUS.replace("let plan = fixed(model=study)", "let plan = adaptive(model=study)")
    text += f"calculate(meets(analysis=ni, target={target()}))\n"
    assert codes(text) == ["sampling_scope"]


def test_planning_claim_is_graded_by_its_cited_analysis():
    text = CONTINUOUS + f"let claim = meets(analysis=ni, target={target()})\n"
    compilation = compile_source(Source(text))
    claim = next(b.value for b in compilation.program.bindings if b.name == "claim")
    assert best_status(claim) == "calculated"
    assert weakest_link(claim.subject)["grade"] == "cited"
    entry = next(item for item in inspect_program(compilation) if "claim" in item["names"])
    assert "normal approximation, not a bound" in entry["description"]


def test_checker_rejects_an_altered_power_derivation():
    text = CONTINUOUS + f"let claim = meets(analysis=ni, target={target()})\n"
    derivation = next(
        d for d in compile_source(Source(text)).derivations if d.name == "claim"
    ).to_dict()
    assert check_derivation(derivation) == []
    altered = copy.deepcopy(derivation)
    step = next(s for s in altered["steps"] if s["rule"] == "power-formula")
    step["facts"]["version"] = 99
    assert check_derivation(altered)
    inside = copy.deepcopy(derivation)
    inside["subject"]["subject"]["target"]["at"]["mean_difference"] = "-60"
    assert check_derivation(inside)
    dropped = copy.deepcopy(derivation)
    dropped["assumptions"] = [a for a in dropped["assumptions"] if "planning input" not in a]
    assert check_derivation(dropped)


def test_example_file_calculates_every_power(tmp_path):
    path = ROOT / "examples/cited_power.stat"
    report = check_source(Source(path.read_text(), str(path)), project=ROOT, output=tmp_path / "x")
    assert report["status"] == "calculated"
    assert [r["status"] for r in report["requests"]] == ["calculated"] * 4
    decisions = [r["report"]["decision"] for r in report["requests"]]
    assert decisions == ["target_met", "target_met", "target_not_met", "target_met"]
    assert report["values"]["must_exceed"] == "-260009/250000"  # -1.040036
