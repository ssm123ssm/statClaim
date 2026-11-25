"""Exact power of Fisher's test of association for cohort and case-control studies.

Nothing here starts Lean; tests/test_lean_translation.py proves these claims in Lean.
"""

import copy
import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.association import AssociationTest
from statclaim.derivation_checker import check_derivation
from statclaim.incidence import RateTest
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.matched import MatchedTest
from statclaim.observational_planning import (
    AssociationPowerPlan,
    MatchedPowerPlan,
    RatePowerPlan,
    TotalPowerPlan,
    binomial_region,
    search_groups,
)
from statclaim.planning import fisher_rejection_probability

ROOT = Path(__file__).resolve().parents[1]
USES = "use models.observational\nuse sampling\nuse tests.association\nuse planning\n"
CASE_CONTROL = (
    'let study = case_control(cases=120, controls=240, exposure="phone use", outcome="glioma")\n'
    "let analysis = fisher_exact(design=fixed(model=study), null=no_association(model=study), "
    "alpha=1/20)\n"
)
COHORT = (
    'let study = cohort(exposed=150, unexposed=300, exposure="statin use", outcome="dementia")\n'
    "let analysis = fisher_exact(design=fixed(model=study), null=no_association(model=study), "
    "alpha=1/20)\n"
)


def target(point, minimum="4/5", maximum="1/20"):
    return f"let target = power_target(at={point}, minimum={minimum}, maximum_typeI={maximum})\n"


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def run(text, tmp_path):
    return check_source(Source(USES + text, "study.stat"), project=ROOT, output=tmp_path / "r")


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_power_agrees_with_r():
    """R values from replication/comparison/observational_power_r.R (R is not needed here):
    every table through base R's fisher.test, and exact2x2::power2x2 within its error bound."""
    fixture = json.loads((ROOT / "tests/fixtures/observational_power_r.json").read_text())
    assert len(fixture["cases"]) == 7
    for case in fixture["cases"]:
        power = fisher_rejection_probability(
            case["first"],
            case["second"],
            Fraction(case["alpha"]),
            Fraction(case["p_first"]),
            Fraction(case["p_second"]),
        )
        assert abs(float(power) - case["enumeration"]) < 1e-12, case
        assert abs(float(power) - case["exact2x2"]) < 1e-6, case


def test_cohort_and_case_control_power_calculate_exactly(tmp_path):
    text = (
        CASE_CONTROL
        + target("exposure_prevalence(controls=1/5, odds_ratio=2)")
        + "let power = calculate(meets(analysis=analysis, target=target))\n"
        + "let value = power.calculation.power\n"
    )
    report = run(text, tmp_path)
    assert report["status"] == "calculated"
    calculation = report["requests"][0]["report"]["calculation"]
    assert (calculation["cases"], calculation["controls"]) == (120, 240)
    assert calculation["exposure_cases"]["fraction"] == "1/3"
    assert calculation["odds_ratio"]["fraction"] == "2"
    assert "risk_ratio" not in calculation
    expected = fisher_rejection_probability(
        240, 120, Fraction(1, 20), Fraction(1, 5), Fraction(1, 3)
    )
    assert Fraction(calculation["power"]["fraction"]) == expected
    assert report["values"]["value"] == str(expected)
    assert calculation["power_target_met"] is False
    assert report["requests"][0]["report"]["limitations"][0].startswith("The bound concerns")

    text = (
        COHORT
        + target("risks(unexposed=1/10, risk_ratio=2)")
        + "let power = calculate(meets(analysis=analysis, target=target))\n"
    )
    calculation = run(text, tmp_path / "cohort")["requests"][0]["report"]["calculation"]
    assert (calculation["exposed"], calculation["unexposed"]) == (150, 300)
    assert calculation["risk_exposed"]["fraction"] == "1/5"
    assert calculation["risk_ratio"]["fraction"] == "2"
    assert calculation["risk_difference"]["fraction"] == "1/10"
    assert calculation["odds_ratio"]["fraction"] == "9/4"


def test_the_smallest_design_matches_r(tmp_path):
    text = (
        CASE_CONTROL
        + target("exposure_prevalence(controls=1/5, cases=1/3)")
        + "let sizes = case_control_sizes(analysis=analysis, min_cases=20, max_cases=200, "
        "controls_per_case=2)\n"
        + "let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))\n"
        + "let needed = sizing.calculation.cases\n"
    )
    report = run(text, tmp_path)
    calculation = report["requests"][0]["report"]["calculation"]
    # R gives 0.7976 at 132 cases and 0.8003 at 133, each with twice as many controls.
    assert (calculation["cases"], calculation["controls"]) == (133, 266)
    assert calculation["candidates_evaluated"] == 114
    assert calculation["minimum_sample_size_claim"] == "requested"
    assert report["values"]["needed"] == 133
    text = (
        COHORT
        + target("risks(unexposed=1/10, exposed=1/5)", minimum="99/100")
        + "let sizes = cohort_sizes(analysis=analysis, min_exposed=10, max_exposed=20)\n"
        + "let sizing = calculate(sample_size(candidates=sizes, target=target))\n"
    )
    request = run(text, tmp_path / "none")["requests"][0]
    assert request["report"]["decision"] == "no_feasible_candidate"
    assert request["report"]["calculation"]["min_exposed"] == 10


@pytest.mark.parametrize(
    "study,point,code,fragment",
    [
        (
            CASE_CONTROL,
            "risks(unexposed=1/10, exposed=1/5)",
            "planning_point",
            "exposure_prevalence",
        ),
        (COHORT, "exposure_prevalence(controls=1/5, cases=1/3)", "planning_point", "risks("),
        (COHORT, "binomial_rates(p_control=1/10, p_treatment=1/5)", "planning_point", "risks("),
        (COHORT, "risks(unexposed=1/10, exposed=1/10)", "alternative_in_null", "risk_exposed"),
        (COHORT, "risks(unexposed=1/10, exposed=1/5, risk_ratio=2)", "planning_point", "one of"),
        (COHORT, "risks(unexposed=1/10)", "planning_point", "one of"),
        (COHORT, "risks(unexposed=1/2, risk_ratio=3)", "domain", "above 1"),
        (COHORT, "risks(unexposed=1/10, risk_ratio=0)", "domain", "positive"),
        (
            'let study = cross_sectional(n=200, exposure="x", outcome="y")\n'
            "let analysis = fisher_exact(design=fixed(model=study), "
            "null=no_association(model=study), alpha=1/20)\n",
            "risks(unexposed=1/10, exposed=1/5)",
            "planning_point",
            "outcome_prevalence",
        ),
        (
            "let study = case_control(cases=600, controls=600)\n"
            "let analysis = fisher_exact(design=fixed(model=study), "
            "null=no_association(model=study), alpha=1/20)\n",
            "exposure_prevalence(controls=1/5, cases=1/3)",
            "domain",
            "limited to 500",
        ),
    ],
)
def test_points_must_fit_the_design(study, point, code, fragment):
    diagnostics = compiled(
        study + target(point) + "let p = calculate(meets(analysis=analysis, target=target))\n"
    ).diagnostics
    assert diagnostics, (study, point)
    assert diagnostics[0].code == code
    assert fragment in diagnostics[0].message


def test_a_cohort_of_one_population_has_no_search():
    text = (
        'let study = cohort(n=300, exposure="x", outcome="y")\n'
        "let analysis = fisher_exact(design=fixed(model=study), null=no_association(model=study), "
        "alpha=1/20)\n"
        "let sizes = cohort_sizes(analysis=analysis, min_exposed=10, max_exposed=20)\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == "unsupported_claim"
    assert "fixes only its total" in diagnostics[0].message


@pytest.mark.parametrize(
    "candidates,code,fragment",
    [
        ("cohort_sizes(analysis=analysis, min_exposed=10, max_exposed=20)", "type", "cohort"),
        (
            "case_control_sizes(analysis=analysis, min_cases=10, max_cases=200, "
            "controls_per_case=3)",
            "domain",
            "limited to 500",
        ),
        (
            "case_control_sizes(analysis=analysis, min_cases=10, max_cases=20, "
            "controls_per_case=11)",
            "domain",
            "controls_per_case",
        ),
        ("case_control_sizes(analysis=analysis, min_cases=20, max_cases=10)", "domain", "at least"),
    ],
)
def test_search_spaces_are_checked(candidates, code, fragment):
    text = (
        CASE_CONTROL
        + target("exposure_prevalence(controls=1/5, cases=1/3)")
        + f"let sizes = {candidates}\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == code
    assert fragment in diagnostics[0].message


def test_derivations_are_checked_independently():
    text = (
        CASE_CONTROL
        + target("exposure_prevalence(controls=1/5, cases=1/3)")
        + "let claim = meets(analysis=analysis, target=target)\n"
        + "let sizes = case_control_sizes(analysis=analysis, min_cases=20, max_cases=60, "
        "controls_per_case=2)\n"
        + "let search = smallest_sample_size(candidates=sizes, target=target)\n"
    )
    compilation = compiled(text)
    assert compilation.status == "elaborated", compilation.diagnostics
    for name in ("claim", "search"):
        record = next(d for d in compilation.derivations if d.name == name).to_dict()
        assert record["contract"] in ("planning/meets", "planning/sample_size")
        assert check_derivation(record) == [], name
        changed = copy.deepcopy(record)
        changed["subject"]["subject"]["target"]["at"]["exposure_cases"] = "1/5"
        assert check_derivation(changed) != []
    record = next(d for d in compilation.derivations if d.name == "search").to_dict()
    changed = copy.deepcopy(record)
    changed["subject"]["subject"]["candidates"]["controls_per_case"] = 20
    assert check_derivation(changed) != []


def test_verify_and_simulate_are_refused_where_they_do_not_apply():
    text = (
        CASE_CONTROL
        + target("exposure_prevalence(controls=1/5, cases=1/3)", maximum="1/40")
        + "let checked = verify(meets(analysis=analysis, target=target))\n"
    )
    assert [d.code for d in compiled(text).diagnostics] == ["typeI_target_not_established"]
    text = (
        CASE_CONTROL
        + target("exposure_prevalence(controls=1/5, cases=1/3)")
        + "let s = simulate(meets(analysis=analysis, target=target), seed=1)\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == "unsupported_claim"
    assert "exact power" in diagnostics[0].message


def plan(minimal=False):
    test = AssociationTest("case_control", Fraction(1, 20), (60, 30), None, "smoking", "cancer")
    found, evaluated = search_groups(
        test, Fraction(1, 5), Fraction(1, 2), Fraction(1, 2), Fraction(1, 20), 10, 60, minimal, 2
    )
    return found, evaluated


def test_a_minimal_search_finds_the_smallest_groups():
    found, evaluated = plan(minimal=True)
    assert found.test.groups == (34, 17) and evaluated == 8


@pytest.mark.parametrize(
    "arguments,fragment",
    [
        ((Fraction(1, 5), Fraction(1, 5)), "outside the null"),
        ((Fraction(1, 5), Fraction(6, 5)), "between zero and one"),
    ],
)
def test_plans_refuse_invalid_points(arguments, fragment):
    test = AssociationTest("cohort", Fraction(1, 20), (40, 40))
    with pytest.raises(ValueError, match=fragment):
        AssociationPowerPlan(test, *arguments, Fraction(4, 5), Fraction(1, 20))


def test_plans_refuse_designs_they_cannot_certify():
    with pytest.raises(ValueError, match="fixed groups"):
        AssociationPowerPlan(
            AssociationTest("cross_sectional", Fraction(1, 20), None, 100),
            Fraction(1, 5),
            Fraction(1, 3),
            Fraction(4, 5),
            Fraction(1, 20),
        )
    test = AssociationTest("cohort", Fraction(1, 20), (40, 40))
    with pytest.raises(ValueError, match="describes a search"):
        AssociationPowerPlan(
            test, Fraction(1, 5), Fraction(1, 3), Fraction(4, 5), Fraction(1, 20), ratio=2
        )
    with pytest.raises(ValueError, match="candidate of the search"):
        AssociationPowerPlan(
            test,
            Fraction(1, 5),
            Fraction(1, 3),
            Fraction(4, 5),
            Fraction(1, 20),
            "sample_size",
            (50, 60),
        )


def test_the_lesson_and_example_compile():
    for name in (
        "examples/tutorial/29_observational_power.stat",
        "examples/observational_power.stat",
    ):
        path = ROOT / name
        compilation = compile_source(Source(path.read_text(), str(path)))
        assert compilation.status == "elaborated", (name, compilation.diagnostics)


# McNemar's test and the rate test ----------------------------------------------------------
MATCHED = (
    'let paired = matched_case_control(pairs=150, exposure="benzodiazepine use", '
    'outcome="hip fracture")\n'
    "let analysis = mcnemar(design=fixed(model=paired), null=no_association(model=paired), "
    "alpha=1/20)\n"
)
RATES = (
    'let workers = person_time_cohort(exposure="solvents", outcome="kidney cancer")\n'
    "let analysis = rate_test(design=fixed(model=workers), null=no_association(model=workers), "
    "alpha=1/40)\n"
)
RATE_POINT = "incidence_rates(rate_ratio=2, exposed_time=8000, unexposed_time=24000"


def test_matched_and_rate_power_agree_with_r():
    fixture = json.loads((ROOT / "tests/fixtures/observational_power_r.json").read_text())
    for case in fixture["matched"]:
        plan = MatchedPowerPlan(
            MatchedTest(case["pairs"], Fraction(case["alpha"])),
            Fraction(case["discordant"]),
            Fraction(case["odds_ratio"]),
            Fraction(1, 2),
            Fraction(1, 2),
        )
        assert abs(float(plan.power) - case["enumeration"]) < 1e-12, case
        assert abs(float(plan.power) - case["exact2x2"]) < 1e-6, case
    for case in fixture["rates"]:
        plan = RatePowerPlan(
            RateTest(Fraction(case["alpha"])),
            Fraction(case["exposed_time"]),
            Fraction(case["unexposed_time"]),
            Fraction(case["rate_ratio"]),
            case["events"],
            Fraction(1, 2),
            Fraction(1, 2),
        )
        assert abs(float(plan.power) - case["enumeration"]) < 1e-12, case
    assert len(fixture["matched"]) == len(fixture["rates"]) == 5


def test_matched_and_rate_power_calculate(tmp_path):
    text = (
        MATCHED
        + target("discordant_pairs(share=1/4, odds_ratio=2)")
        + "let power = calculate(meets(analysis=analysis, target=target))\n"
        + "let sizes = matched_sizes(analysis=analysis, min_pairs=250, max_pairs=400)\n"
        + "let sizing = calculate(smallest_sample_size(candidates=sizes, target=target))\n"
        + "let needed = sizing.calculation.pairs\n"
    )
    report = run(text, tmp_path)
    power, sizing = (request["report"]["calculation"] for request in report["requests"])
    assert power["case_exposed_share"]["fraction"] == "2/3"
    assert power["expected_discordant_pairs"]["fraction"] == "75/2"
    assert round(float(Fraction(power["power"]["fraction"])), 6) == 0.474075
    # R gives 0.79875 at 297 pairs and 0.80013 at 298.
    assert report["values"]["needed"] == 298
    assert sizing["candidates_evaluated"] == 49
    text = (
        RATES
        + target(RATE_POINT + ", events=60)", maximum="1/40")
        + "let power = calculate(meets(analysis=analysis, target=target))\n"
        + target(RATE_POINT + ")", maximum="1/40").replace("let target", "let open")
        + "let counts = event_counts(analysis=analysis, min_events=20, max_events=200)\n"
        + "let sizing = calculate(smallest_sample_size(candidates=counts, target=open))\n"
        + "let needed = sizing.calculation.events\n"
    )
    report = run(text, tmp_path / "rates")
    power = report["requests"][0]["report"]["calculation"]
    assert power["exposed_time_share"]["fraction"] == "1/4"
    assert power["exposed_event_share"]["fraction"] == "2/5"
    assert round(float(Fraction(power["power"]["fraction"])), 6) == 0.548895
    # R gives 0.7823 at 93 events and 0.8054 at 94.
    assert report["values"]["needed"] == 94


@pytest.mark.parametrize(
    "study,declaration,code,fragment",
    [
        (
            MATCHED,
            "let t = " + "risks(unexposed=1/10, exposed=1/5)\n",
            "planning_point",
            "discordant",
        ),
        (
            MATCHED,
            "let t = discordant_pairs(share=1/4, odds_ratio=1)\n",
            "alternative_in_null",
            "=",
        ),
        (MATCHED, "let t = discordant_pairs(share=0, odds_ratio=2)\n", "domain", "share"),
        (RATES, f"let t = {RATE_POINT})\n", "planning_point", "events="),
        (RATES, f"let t = {RATE_POINT}, events=600)\n", "domain", "events"),
        (
            RATES,
            "let t = incidence_rates(rate_ratio=1, exposed_time=1, unexposed_time=1, events=20)\n",
            "alternative_in_null",
            "rate_exposed",
        ),
        (
            RATES,
            "let t = incidence_rates(rate_ratio=2, exposed_time=0, unexposed_time=1, events=20)\n",
            "domain",
            "exposed_time",
        ),
    ],
)
def test_matched_and_rate_points_are_checked(study, declaration, code, fragment):
    text = (
        study
        + declaration
        + "let target = power_target(at=t, minimum=4/5, maximum_typeI=1/20)\n"
        + "let p = calculate(meets(analysis=analysis, target=target))\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == code
    assert fragment in diagnostics[0].message


def test_searches_over_pairs_and_events_are_checked():
    text = (
        RATES
        + target(RATE_POINT + ", events=60)", maximum="1/40")
        + "let counts = event_counts(analysis=analysis, min_events=20, max_events=200)\n"
        + "let s = calculate(sample_size(candidates=counts, target=target))\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == "planning_point" and "leave events out" in diagnostics[0].message
    text = MATCHED + "let sizes = matched_sizes(analysis=analysis, min_pairs=10, max_pairs=500)\n"
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == "domain" and "400 pairs" in diagnostics[0].message
    text = (
        "let paired = matched_case_control(pairs=401)\n"
        "let analysis = mcnemar(design=fixed(model=paired), null=no_association(model=paired), "
        "alpha=1/20)\n"
        + target("discordant_pairs(share=1/4, odds_ratio=2)")
        + "let p = calculate(meets(analysis=analysis, target=target))\n"
    )
    assert compiled(text).diagnostics[0].code == "domain"
    text = (
        MATCHED
        + target("discordant_pairs(share=1/4, odds_ratio=2)", maximum="1/40")
        + "let checked = verify(meets(analysis=analysis, target=target))\n"
    )
    (diagnostic,) = compiled(text).diagnostics
    assert diagnostic.code == "typeI_target_not_established"
    assert "The test's theorem" in diagnostic.message


def test_matched_and_rate_derivations_are_checked():
    text = (
        MATCHED
        + target("discordant_pairs(share=1/4, odds_ratio=2)")
        + "let claim = meets(analysis=analysis, target=target)\n"
        + "let search = sample_size(candidates=matched_sizes(analysis=analysis, min_pairs=10, "
        "max_pairs=300), target=target)\n"
    )
    compilation = compiled(text)
    assert compilation.status == "elaborated", compilation.diagnostics
    for name in ("claim", "search"):
        record = next(d for d in compilation.derivations if d.name == name).to_dict()
        assert check_derivation(record) == [], name
        changed = copy.deepcopy(record)
        changed["subject"]["subject"]["target"]["at"]["odds_ratio"] = "1"
        assert check_derivation(changed) != []
    text = (
        RATES
        + target(RATE_POINT + ", events=60)", maximum="1/40")
        + "let claim = meets(analysis=analysis, target=target)\n"
    )
    record = next(d for d in compiled(text).derivations if d.name == "claim").to_dict()
    assert check_derivation(record) == []
    changed = copy.deepcopy(record)
    changed["subject"]["subject"]["target"]["at"]["events"] = 600
    assert check_derivation(changed) != []


# Designs that fix only the total -----------------------------------------------------------
SURVEY = (
    'let survey = cross_sectional(n=120, exposure="night shifts", outcome="insomnia")\n'
    "let analysis = fisher_exact(design=fixed(model=survey), null=no_association(model=survey), "
    "alpha=1/20)\n"
)
SURVEY_POINT = "outcome_prevalence(unexposed=1/10, prevalence_ratio=3, exposed_share=3/10)"


def test_total_power_agrees_with_r():
    fixture = json.loads((ROOT / "tests/fixtures/observational_power_r.json").read_text())
    assert len(fixture["totals"]) == 3
    for case in fixture["totals"]:
        plan = TotalPowerPlan(
            AssociationTest(case["design"], Fraction(case["alpha"]), None, case["n"]),
            Fraction(case["p_first"]),
            Fraction(case["p_second"]),
            Fraction(case["exposed_share"]),
            Fraction(1, 2),
            Fraction(1, 2),
        )
        assert abs(float(plan.power) - case["enumeration"]) < 1e-12, case


def test_total_power_calculates_and_searches(tmp_path):
    text = (
        SURVEY
        + target(SURVEY_POINT)
        + "let power = calculate(meets(analysis=analysis, target=target))\n"
        + "let sizes = total_sizes(analysis=analysis, min_n=60, max_n=150)\n"
        + "let found = calculate(sample_size(candidates=sizes, target=target))\n"
        + "let needed = found.calculation.total_sample_size\n"
    )
    report = run(text, tmp_path)
    power, found = (request["report"]["calculation"] for request in report["requests"])
    assert power["expected_exposed"]["fraction"] == "36"
    assert power["prevalence_ratio"]["fraction"] == "3"
    assert round(float(Fraction(power["power"]["fraction"])), 6) == 0.711988
    assert report["values"]["needed"] == 148
    assert found["minimum_sample_size_claim"] == "not_requested"


@pytest.mark.parametrize(
    "study,point,code,fragment",
    [
        (SURVEY, "outcome_prevalence(unexposed=1/10, exposed=1/5)", "arguments", "exposed_share"),
        (SURVEY, "risks(unexposed=1/10, exposed=1/5)", "planning_point", "outcome_prevalence"),
        (
            SURVEY,
            "outcome_prevalence(unexposed=1/2, prevalence_ratio=3, exposed_share=1/2)",
            "domain",
            "above 1",
        ),
        (
            SURVEY,
            "outcome_prevalence(unexposed=1/10, exposed=1/5, exposed_share=1)",
            "domain",
            "strictly between",
        ),
        (
            'let people = cohort(n=100, exposure="x", outcome="y")\n'
            "let analysis = fisher_exact(design=fixed(model=people), "
            "null=no_association(model=people), alpha=1/20)\n",
            "risks(unexposed=1/10, exposed=1/5)",
            "planning_point",
            "exposed_share",
        ),
        (
            COHORT,
            "risks(unexposed=1/10, exposed=1/5, exposed_share=1/2)",
            "planning_point",
            "Leave exposed_share out",
        ),
        (
            "let survey = cross_sectional(n=151)\n"
            "let analysis = fisher_exact(design=fixed(model=survey), "
            "null=no_association(model=survey), alpha=1/20)\n",
            SURVEY_POINT,
            "domain",
            "150 participants",
        ),
    ],
)
def test_total_points_must_fit_the_design(study, point, code, fragment):
    diagnostics = compiled(
        study + target(point) + "let p = calculate(meets(analysis=analysis, target=target))\n"
    ).diagnostics
    assert diagnostics[0].code == code
    assert fragment in diagnostics[0].message


def test_a_large_declared_study_can_still_be_searched(tmp_path):
    """The declared size limits exact power at that size; a search checks its own bounds."""
    text = (
        'let survey = cross_sectional(n=400, exposure="night shifts", outcome="insomnia")\n'
        "let analysis = fisher_exact(design=fixed(model=survey), "
        "null=no_association(model=survey), alpha=1/20)\n"
        + target(SURVEY_POINT)
        + "let found = calculate(sample_size(candidates=total_sizes(analysis=analysis, min_n=60, "
        "max_n=150), target=target))\n"
        + "let paired = matched_case_control(pairs=1000)\n"
        + "let pairs_test = mcnemar(design=fixed(model=paired), null=no_association(model=paired), "
        "alpha=1/20)\n"
        + "let pairs_target = power_target(at=discordant_pairs(share=1/2, odds_ratio=3), "
        "minimum=4/5, maximum_typeI=1/20)\n"
        + "let pairs = calculate(sample_size(candidates=matched_sizes(analysis=pairs_test, "
        "min_pairs=55, max_pairs=80), target=pairs_target))\n"
    )
    report = run(text, tmp_path)
    assert report["status"] == "calculated", report["diagnostics"]
    assert report["requests"][0]["report"]["calculation"]["total_sample_size"] == 148
    assert report["requests"][1]["report"]["calculation"]["pairs"] == 67


def test_total_searches_are_sufficient_only():
    text = (
        SURVEY
        + target(SURVEY_POINT)
        + "let sizes = total_sizes(analysis=analysis, min_n=60, max_n=150)\n"
        + "let found = calculate(smallest_sample_size(candidates=sizes, target=target))\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == "unsupported_claim" and "sample_size(" in diagnostics[0].message
    text = CASE_CONTROL + "let sizes = total_sizes(analysis=analysis, min_n=60, max_n=150)\n"
    assert compiled(text).diagnostics[0].code == "type"
    text = SURVEY + "let sizes = total_sizes(analysis=analysis, min_n=60, max_n=151)\n"
    assert compiled(text).diagnostics[0].code == "domain"


def test_total_derivations():
    text = (
        SURVEY
        + target(SURVEY_POINT)
        + "let claim = meets(analysis=analysis, target=target)\n"
        + "let search = sample_size(candidates=total_sizes(analysis=analysis, min_n=60, "
        "max_n=150), target=target)\n"
    )
    compilation = compiled(text)
    assert compilation.status == "elaborated", compilation.diagnostics


def test_exact_rate_region_at_one_quarter():
    assert binomial_region(60, Fraction(1, 4), Fraction(1, 40)) == (8, 24)
