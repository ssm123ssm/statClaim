"""Observational studies: designs, the null of no association, refusals and derivations.

Nothing here starts Lean; tests/test_association_integration.py does.
"""

import copy
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.association import (
    MEASURES,
    AssociationResult,
    AssociationTable,
    AssociationTest,
    EffectInterval,
    association_assumptions,
    association_claims,
    association_payload,
    interval_assumptions,
    interval_claims,
    interval_payload,
    parse_association_payload,
    parse_interval_payload,
    parse_result_payload,
    render_association_proof,
    render_interval_proof,
    render_result_proof,
    result_assumptions,
    result_payload,
)
from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.identify import identify

ROOT = Path(__file__).resolve().parents[1]
USES = "use models.observational\nuse sampling\nuse tests.association\n"
TEST = (
    "let analysis = fisher_exact(design=fixed(model=study), null=no_association(model=study), "
    "alpha=1/20)\n"
)
STUDIES = {
    "cross_sectional": 'let study = cross_sectional(n=400, exposure="smoking", outcome="wheeze")\n',
    "cohort": "let study = cohort(exposed=100, unexposed=300)\n",
    "population_cohort": "let study = cohort(n=900)\n",
    "case_control": 'let study = case_control(cases=80, controls=160, outcome="glioma")\n',
}


def compiled(text, uses=USES):
    return compile_source(Source(uses + text, "study.stat"))


def codes(text, uses=USES):
    return [d.code for d in compiled(text, uses).diagnostics]


def derivation(compilation, name="analysis"):
    return next(d for d in compilation.derivations if d.name == name).to_dict()


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("design", STUDIES)
def test_every_design_compiles_with_a_checked_derivation(design):
    compilation = compiled(STUDIES[design] + TEST + "let claim = verify(typeI(analysis))\n")
    assert compilation.status == "elaborated", compilation.diagnostics
    record = derivation(compilation)
    assert record["contract"] == "tests.association/fisher_exact"
    assert check_derivation(record) == []
    analysis = next(b.value for b in compilation.program.bindings if b.name == "analysis")
    test = analysis.lower()
    assert test.fixed_groups == (design in ("cohort", "case_control"))
    assert analysis.guarantee.scope == "finite_sample"


def test_the_null_is_stated_in_each_designs_terms():
    statements = {}
    for design, text in STUDIES.items():
        program = compiled(text + "let null = no_association(model=study)\n").program
        statements[design] = next(b.value for b in program.bindings if b.name == "null").statement
    assert statements == {
        "cross_sectional": "prevalence_exposed = prevalence_unexposed",
        "cohort": "risk_exposed = risk_unexposed",
        "population_cohort": "risk_exposed = risk_unexposed",
        "case_control": "exposure_cases = exposure_controls",
    }


def test_groups_and_names_reach_the_test():
    program = compiled(
        'let study = case_control(cases=80, controls=160, exposure="smoking", outcome="glioma")\n'
        + TEST
    ).program
    test = next(b.value for b in program.bindings if b.name == "analysis").lower()
    assert test == AssociationTest(
        "case_control", Fraction(1, 20), (160, 80), None, "smoking", "glioma"
    )
    cohort = compiled(STUDIES["cohort"] + TEST).program
    assert next(b.value for b in cohort.bindings if b.name == "analysis").lower().groups == (
        300,
        100,
    )


@pytest.mark.parametrize(
    "declaration,fragment",
    [
        ("cohort(exposed=10, unexposed=20, n=30)", "not both"),
        ("cohort(exposed=10)", "needs exposed and unexposed"),
        ("cohort()", "needs exposed and unexposed"),
        ("cross_sectional(n=0)", "positive"),
        ("case_control(cases=10, controls=-1)", "positive"),
        ("cross_sectional(n=2000000)", "at most"),
        ('cross_sectional(n=10, exposure="")', "plain words"),
        ('cross_sectional(n=10, outcome="a\\nb")', "plain words"),
    ],
)
def test_invalid_designs_are_refused_with_reasons(declaration, fragment):
    diagnostics = compiled(f"let study = {declaration}\n").diagnostics
    assert [d.code for d in diagnostics] == ["domain"]
    assert fragment in diagnostics[0].message


TRIAL_USES = (
    "use models.observational\nuse models.two_arm_binomial\nuse models.two_arm_continuous\n"
    "use sampling\nuse tests.association\nuse tests.fisher\nuse tests.t\nuse tests.declared\n"
    "use tests.randomisation\nuse tests.difference\n"
)


@pytest.mark.parametrize(
    "analysis,code",
    [
        ("fisher(design=fixed(model=study), null=no_association(model=study), alpha=1/20)", "type"),
        ("t_test(design=fixed(model=study), null=no_association(model=study), alpha=1/20)", None),
        (
            "declared_test(design=fixed(model=study), null=no_association(model=study), "
            'alpha=1/20, method="chi-squared test")',
            "observational_design",
        ),
        (
            "randomisation_test(design=fixed(model=study), null=no_effect(model=study), "
            "alpha=1/20)",
            None,
        ),
        ("no_effect(model=study)", "observational_design"),
        ("equal_proportions(model=study)", "type"),
    ],
)
def test_tests_and_nulls_of_randomised_arms_refuse_an_observational_study(analysis, code):
    diagnostics = compiled(
        STUDIES["cohort"] + f"let analysis = {analysis}\n", TRIAL_USES
    ).diagnostics
    assert diagnostics, analysis
    first = diagnostics[0]
    assert first.code in ({code} if code else {"observational_design", "hypothesis_mismatch"})
    assert "fisher_exact" in first.message or "observational" in first.message


def test_a_trials_null_explains_where_an_association_null_belongs():
    diagnostics = compiled(
        STUDIES["cohort"]
        + "let analysis = fisher(design=fixed(model=study), null=no_association(model=study), "
        "alpha=1/20)\n",
        TRIAL_USES,
    ).diagnostics
    assert "fisher_exact from tests.association" in diagnostics[0].message


def test_the_test_refuses_a_trial_and_a_null_of_another_study():
    trial = (
        "let trial = two_arm_binomial(n_control=50, n_treatment=50)\n"
        "let study = cohort(exposed=100, unexposed=300)\n"
        "let analysis = fisher_exact(design=fixed(model=trial), null=no_association(model=study), "
        "alpha=1/20)\n"
    )
    assert codes(trial, TRIAL_USES)[0] == "type"
    other = (
        STUDIES["cohort"]
        + "let other = cohort(exposed=100, unexposed=301)\n"
        + "let analysis = fisher_exact(design=fixed(model=study), "
        "null=no_association(model=other), alpha=1/20)\n"
    )
    assert codes(other) == ["model_mismatch"]


def test_data_dependent_stopping_leaves_an_obligation(tmp_path):
    text = (
        STUDIES["cohort"] + "let analysis = fisher_exact(design=adaptive(model=study), "
        "null=no_association(model=study), alpha=1/20)\nlet claim = verify(typeI(analysis))\n"
    )
    compilation = compiled(text)
    assert [d.code for d in compilation.diagnostics] == ["sampling_scope"]
    record = derivation(compilation)
    assert [item["rule"] for item in record["obligations"]] == ["fixed-sampling"]
    assert check_derivation(record) == []
    report = check_source(Source(USES + text, "study.stat"), project=ROOT, output=tmp_path / "run")
    request = report["requests"][0]
    assert request["status"] == "unresolved_obligation"


def test_an_association_test_is_not_a_calculation():
    text = STUDIES["cohort"] + TEST + "let claim = calculate(typeI(analysis))\n"
    assert codes(text) == ["type"]


def test_fields_of_studies_and_tests_are_published():
    text = (
        STUDIES["cohort"]
        + TEST
        + "let size = study.exposed\nlet named = study.outcome\nlet level = analysis.alpha\n"
        + "let statement = analysis.null.statement\n"
    )
    compilation = compiled(text)
    assert compilation.status == "elaborated", compilation.diagnostics
    values = {b.name: b.value for b in compilation.program.bindings}
    assert values["size"] == 100 and values["named"] == "outcome"
    assert values["level"] == Fraction(1, 20)
    assert values["statement"] == "risk_exposed = risk_unexposed"


def _other_design(record):
    record["subject"]["design"]["model"]["study"] = "cross_sectional"


def _more_cases(record):
    record["subject"]["design"]["model"]["cases"] = 81


def _two_arm_null(record):
    record["subject"]["null"]["predicate"] = "equal_proportions"


def _fewer_assumptions(record):
    record["assumptions"] = record["assumptions"][:-1]


def _no_sampling_step(record):
    record["steps"] = record["steps"][:-1]


def _a_guarantee(record):
    record["guarantee"] = {"grade": "cited", "sentence": "anything"}


def _randomisation_contract(record):
    record["contract"] = "tests.randomisation/randomisation_test"


@pytest.mark.parametrize(
    "change",
    [
        _other_design,
        _more_cases,
        _two_arm_null,
        _fewer_assumptions,
        _no_sampling_step,
        _a_guarantee,
        _randomisation_contract,
    ],
)
def test_the_checker_rejects_tampered_association_derivations(change):
    record = derivation(compiled(STUDIES["case_control"] + TEST))
    assert check_derivation(record) == []
    changed = copy.deepcopy(record)
    change(changed)
    assert check_derivation(changed) != []


TESTS = [
    AssociationTest("cohort", Fraction(1, 20), (300, 100), None, "smoking", "asthma"),
    AssociationTest("cohort", Fraction(1, 40), None, 900),
    AssociationTest("case_control", Fraction(1, 20), (160, 80)),
    AssociationTest("cross_sectional", Fraction(1, 20), None, 1200, "night shifts", "insomnia"),
]


@pytest.mark.parametrize("test", TESTS)
def test_payloads_round_trip_and_reject_tampering(test):
    payload = association_payload(test)
    assert parse_association_payload(copy.deepcopy(payload)) == test
    changed = copy.deepcopy(payload)
    changed["analysis"]["test_version"] = "9"
    with pytest.raises(ValueError):
        parse_association_payload(changed)
    changed = copy.deepcopy(payload)
    changed["design"]["extra"] = 1
    with pytest.raises(ValueError):
        parse_association_payload(changed)


@pytest.mark.parametrize(
    "arguments",
    [
        ("trial", Fraction(1, 20), (10, 10)),
        ("cohort", Fraction(1, 20), (10, 10), 20),
        ("cohort", Fraction(1, 20)),
        ("case_control", Fraction(1, 20), None, 40),
        ("cross_sectional", Fraction(1, 20), (10, 10)),
        ("cohort", Fraction(1, 20), (0, 10)),
        ("cohort", Fraction(3, 2), (10, 10)),
        ("cohort", Fraction(1, 20), (10, 10), None, "smoking\nimport Mathlib"),
    ],
)
def test_invalid_tests_have_no_payload(arguments):
    with pytest.raises(ValueError):
        AssociationTest(*arguments)


@pytest.mark.parametrize("test", TESTS)
def test_the_proof_names_the_numbers_and_never_the_names(test):
    proof = render_association_proof(test, "a" * 64)
    assert "sorry" not in proof and "STATCLAIM" not in proof.split("run_cmd")[0]
    if test.fixed_groups:
        assert f"def firstGroup : ℕ := {test.groups[0]}" in proof
        assert "Association.groups_typeI_le_alpha" in proof
    else:
        assert f"def sampleSize : ℕ := {test.n}" in proof
        assert "Association.mixture_typeI_le_alpha" in proof
    assert test.exposure not in proof.replace("exposed", "")
    with pytest.raises(ValueError):
        render_association_proof(test, "not a hash")


@pytest.mark.parametrize("test", TESTS)
def test_claims_say_association_and_every_assumption_is_recognised(test):
    claims = " ".join(association_claims(test))
    assert "no association" in claims and str(test.alpha) in claims
    assert all(identify(text)["id"] for text in association_assumptions(test))
    if test.design == "case_control":
        assert "odds ratio 1" in claims


def test_the_examples_and_lesson_compile_with_checked_derivations():
    for name in (
        "examples/case_control.stat",
        "examples/cross_sectional.stat",
        "examples/tutorial/23_observational_studies.stat",
    ):
        path = ROOT / name
        compilation = compile_source(Source(path.read_text(), str(path)))
        assert compilation.status == "elaborated", (name, compilation.diagnostics)
        assert compilation.derivations
        assert all(check_derivation(d.to_dict()) == [] for d in compilation.derivations)


# Observed tables, results and effect intervals --------------------------------------------
ESTIMATION = USES + "use estimation.observational\n"
COHORT_TABLE = (
    "let seen = observed_table(model=study, exposed_cases=30, exposed_noncases=70, "
    "unexposed_cases=25, unexposed_noncases=275)\n"
)
CASE_TABLE = (
    "let seen = observed_table(model=study, exposed_cases=50, exposed_noncases=60, "
    "unexposed_cases=30, unexposed_noncases=100)\n"
)
SURVEY_TABLE = (
    "let seen = observed_table(model=study, exposed_cases=40, exposed_noncases=60, "
    "unexposed_cases=30, unexposed_noncases=270)\n"
)


@pytest.mark.parametrize(
    "design,table,fragment",
    [
        ("cohort", COHORT_TABLE.replace("70", "71"), "101 exposed"),
        ("case_control", CASE_TABLE.replace("50", "51"), "81 cases"),
        ("cross_sectional", SURVEY_TABLE.replace("270", "271"), "401 participants"),
        (
            "cross_sectional",
            "let seen = observed_table(model=study, exposed_cases=0, exposed_noncases=0, "
            "unexposed_cases=30, unexposed_noncases=370)\n",
            "at least one exposed",
        ),
        ("cohort", COHORT_TABLE.replace("=30", "=-1"), "zero or more"),
    ],
)
def test_a_table_must_fit_what_the_design_fixed(design, table, fragment):
    diagnostics = compiled(STUDIES[design] + table, ESTIMATION).diagnostics
    assert [d.code for d in diagnostics] == ["domain"]
    assert fragment in diagnostics[0].message


@pytest.mark.parametrize(
    "design,table,allowed",
    [
        ("cohort", COHORT_TABLE, {"odds_ratio", "risk_ratio", "risk_difference"}),
        (
            "population_cohort",
            SURVEY_TABLE.replace("270", "770"),
            {"odds_ratio", "risk_ratio", "risk_difference"},
        ),
        ("case_control", CASE_TABLE, {"odds_ratio"}),
        (
            "cross_sectional",
            SURVEY_TABLE,
            {"odds_ratio", "prevalence_ratio", "prevalence_difference"},
        ),
    ],
)
def test_each_design_estimates_only_what_its_sampling_allows(design, table, allowed):
    for measure in MEASURES:
        text = STUDIES[design] + table + f"let effect = {measure}(table=seen, level=19/20)\n"
        found = codes(text, ESTIMATION)
        if measure in allowed:
            assert found == [], (design, measure, found)
        else:
            assert found == ["not_estimable"], (design, measure, found)


def test_a_case_control_study_explains_why_it_has_no_risk_ratio():
    text = (
        STUDIES["case_control"] + CASE_TABLE + "let effect = risk_ratio(table=seen, level=19/20)\n"
    )
    message = compiled(text, ESTIMATION).diagnostics[0].message
    assert "fixed how many have the outcome" in message and "odds_ratio" in message


def test_results_and_intervals_calculate_exactly_without_lean(tmp_path):
    text = (
        STUDIES["cohort"]
        + TEST
        + COHORT_TABLE
        + "let found = calculate(association_result(analysis=analysis, table=seen))\n"
        + "let ratio = calculate(risk_ratio(table=seen, level=19/20))\n"
        + "let p = found.calculation.p_value\nlet low = ratio.calculation.lower\n"
    )
    report = check_source(
        Source(ESTIMATION + text, "study.stat"), project=ROOT, output=tmp_path / "r"
    )
    assert report["status"] == "calculated"
    found, ratio = (request["report"]["calculation"] for request in report["requests"])
    from statclaim.fisher import fisher_exact

    expected = fisher_exact(
        n_control=300, n_treatment=100, control_successes=25, treatment_successes=30
    )
    assert Fraction(found["p_value"]["fraction"]) == expected.p_value
    assert report["values"]["p"] == str(expected.p_value)
    assert Fraction(ratio["estimate"]["fraction"]) == Fraction(30 * 300, 100 * 25)
    assert (
        Fraction(ratio["lower"]["fraction"])
        < Fraction(36, 10)
        < Fraction(ratio["upper"]["fraction"])
    )


def test_a_result_needs_the_analysis_and_the_table_of_one_study():
    text = (
        STUDIES["cohort"]
        + TEST
        + 'let other = cohort(exposed=100, unexposed=300, outcome="wheeze")\n'
        + COHORT_TABLE.replace("model=study", "model=other")
        + "let found = calculate(association_result(analysis=analysis, table=seen))\n"
    )
    assert codes(text, ESTIMATION) == ["model_mismatch"]


TABLES = [
    AssociationTable("cohort", (30, 70, 25, 275), (300, 100), None, "smoking", "asthma"),
    AssociationTable("case_control", (50, 60, 30, 100), (160, 80)),
    AssociationTable("cross_sectional", (40, 60, 30, 270), None, 400),
    AssociationTable("cohort", (5, 95, 0, 300), (300, 100)),
]


@pytest.mark.parametrize("table", TABLES)
def test_effect_intervals_contain_the_estimate_and_round_trip(table):
    for measure, (_, _, designs) in MEASURES.items():
        if table.design not in designs:
            with pytest.raises(ValueError):
                EffectInterval(measure, table, Fraction(19, 20))
            continue
        interval = EffectInterval(measure, table, Fraction(19, 20))
        lower, upper = interval.bounds
        estimate = interval.estimate
        if estimate is not None:
            assert lower <= estimate and (upper is None or estimate <= upper)
        payload = interval_payload(interval)
        assert parse_interval_payload(copy.deepcopy(payload)) == interval
        changed = copy.deepcopy(payload)
        changed["interval"]["lower"] = "0"
        with pytest.raises(ValueError):
            parse_interval_payload(changed)
        claims = " ".join(interval_claims(interval))
        assert "both groups' exact confidence sets" in claims
        assert all(identify(text)["id"] for text in interval_assumptions(interval))
        proof = render_interval_proof(interval, "a" * 64)
        assert "theorem checked_interval" in proof and "sorry" not in proof


def test_a_zero_reference_count_gives_no_finite_upper_bound():
    interval = EffectInterval("risk_ratio", TABLES[3], Fraction(19, 20))
    assert interval.bounds[1] is None and interval.estimate is None
    assert "no finite upper bound" in interval_claims(interval)[1]


@pytest.mark.parametrize("table", TABLES[:3])
def test_result_payloads_round_trip_and_reject_tampering(table):
    test = AssociationTest(
        table.design, Fraction(1, 20), table.groups, table.n, table.exposure, table.outcome
    )
    result = AssociationResult(test, table)
    payload = result_payload(result)
    assert parse_result_payload(copy.deepcopy(payload)) == result
    changed = copy.deepcopy(payload)
    changed["result"]["reject_null"] = not changed["result"]["reject_null"]
    with pytest.raises(ValueError):
        parse_result_payload(changed)
    assert all(identify(text)["id"] for text in result_assumptions(result))
    proof = render_result_proof(result, "a" * 64)
    assert "theorem checked_decision" in proof and proof.count("STATCLAIM_CHECKED") == 1
