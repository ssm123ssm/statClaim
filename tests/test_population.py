"""Who is analysed: population= on an assignment, and what each test makes of it.

A randomisation test needs everyone randomised, so population="randomised" turns its
assumption into a declaration and "per_protocol" is refused. Other tests take either
population, and their claims say which one the bound covers.
"""

import copy
import subprocess
from fractions import Fraction

import pytest

from statclaim.contract_reports import study_report
from statclaim.derivation_checker import check_derivation
from statclaim.language import normalize
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import inspect_program
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods.assumptions import (
    PER_PROTOCOL_POPULATION,
    PRESPECIFIED_EXCLUSIONS,
    RANDOMISED_POPULATION,
)
from statclaim.methods.identify import identify
from statclaim.randomisation import (
    POPULATION,
    RandomisationTest,
    randomisation_assumptions,
    render_randomisation_proof,
)

USES = (
    "use models.two_arm_binomial\nuse models.two_arm_continuous\nuse sampling\n"
    "use tests.randomisation\nuse tests.fisher\nuse tests.t\nuse tests.cluster\n"
    "use tests.declared\nuse multiplicity.bonferroni\n"
)
ARMS = 'let arms = assignment(n_control=20, n_treatment=20, randomisation="complete"{extra})\n'
PAIN = "let study = two_arm(assignment=arms, outcome=continuous_outcome())\n"
RESPONSE = "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
RANDOMISATION = (
    "let analysis = randomisation_test(design=fixed(model=study), null=no_effect(model=study), "
    "alpha=1/20{draws})\nverify typeI(analysis)\n"
)
FISHER = (
    "let analysis = fisher(design=fixed(model=study), null=equal_proportions(model=study), "
    "alpha=1/20)\n"
)
T_TEST = (
    "let analysis = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
)


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def arms(population=None):
    return ARMS.format(extra=f', population="{population}"' if population else "")


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


def derivation(compilation, name="analysis"):
    return next(d for d in compilation.derivations if d.name == name).to_dict()


def statuses(compilation):
    (claim,) = inspect_program(compilation)
    return {item["id"]: item["status"] for item in claim["identified_assumptions"]}


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_the_population_is_recorded_only_when_declared():
    plain = compiled(arms() + PAIN).program.bindings[0].value
    assert "population" not in normalize(plain)
    for population in ("randomised", "per_protocol"):
        value = compiled(arms(population) + PAIN).program.bindings[0].value
        assert value.population == population
        assert normalize(value)["population"] == population
    clinics = compiled(
        "let arms = cluster_assignment(clusters_control=6, clusters_treatment=6, n_control=60, "
        'n_treatment=60, population="randomised")\n'
    )
    assert not clinics.diagnostics
    assert clinics.program.bindings[0].value.population == "randomised"


def test_an_unknown_population_is_refused():
    diagnostic = compiled(arms("itt") + PAIN).diagnostics[0]
    assert diagnostic.code == "domain"
    assert '"randomised"' in diagnostic.message and '"per_protocol"' in diagnostic.message


def test_a_declared_randomised_population_is_stated_not_assumed():
    compilation = compiled(arms("randomised") + PAIN + RANDOMISATION.format(draws=""))
    assert not compilation.diagnostics
    assert statuses(compilation) == {
        "complete_randomisation": "declared",
        "prespecified_analysis": "declared",
        "analysed_as_randomised": "declared",
        "counts_every_split": "assumed",
        "bound_under_null": "condition",
    }
    record = derivation(compilation)
    assert check_derivation(record) == []
    rules = [step["rule"] for step in record["steps"]]
    assert rules[-3:] == ["randomised-population", "randomisation-contract", "fixed-sampling"]
    step = record["steps"][rules.index("randomised-population")]
    assert step["conclusion"] == (
        "analysis: every randomised participant is analysed, in the arm it was assigned to, "
        "as the assignment declares."
    )
    # The contract does not rest on it: without it, the assumption is listed instead.
    assert record["steps"][rules.index("randomisation-contract")]["uses"] == [0, 1, 2, 3, 4]
    assert POPULATION in record["assumptions"]


def test_with_draws_the_population_is_declared_and_the_draws_assumed():
    compilation = compiled(arms("randomised") + PAIN + RANDOMISATION.format(draws=", draws=999"))
    found = statuses(compilation)
    assert found["analysed_as_randomised"] == "declared"
    assert found["analysed_with_draws"] == "assumed"
    assert "counts_every_split" not in found
    assert check_derivation(derivation(compilation)) == []


def test_without_a_population_nothing_changes():
    compilation = compiled(arms() + PAIN + RANDOMISATION.format(draws=""))
    assert statuses(compilation)["analysed_as_randomised"] == "assumed"
    assert "randomised-population" not in [s["rule"] for s in derivation(compilation)["steps"]]


@pytest.mark.parametrize("piece,named", [(RESPONSE, "such as fisher"), (PAIN, "such as t_test")])
def test_a_per_protocol_randomisation_test_is_refused(piece, named):
    diagnostic = compiled(
        arms("per_protocol") + piece + RANDOMISATION.format(draws="")
    ).diagnostics[0]
    assert diagnostic.code == "population_mismatch"
    assert 'population="per_protocol"' in diagnostic.message
    assert 'declare population="randomised"' in diagnostic.message
    assert named in diagnostic.message


def test_a_forged_per_protocol_derivation_fails_the_check():
    record = derivation(compiled(arms("randomised") + PAIN + RANDOMISATION.format(draws="")))
    forged = copy.deepcopy(record)
    for model in (forged["subject"]["design"]["model"], forged["subject"]["null"]["model"]):
        model["population"] = "per_protocol"
    step = next(s for s in forged["steps"] if s["rule"] == "randomised-population")
    step["facts"]["population"] = "per_protocol"
    problems = check_derivation(forged)
    assert any("premise does not hold" in problem for problem in problems)
    # Dropping the declaration from the record while keeping its step is caught too.
    dropped = copy.deepcopy(record)
    del dropped["subject"]["design"]["model"]["population"]
    assert check_derivation(dropped)


def test_a_randomisation_test_covers_every_randomised_unit():
    test = RandomisationTest(
        12, 6, Fraction(1, 20), "cluster", "two_arm_continuous", 120, 120, population="randomised"
    )
    assert POPULATION in randomisation_assumptions(test)
    assert "theorem checked_typeI" in render_randomisation_proof(test, "0" * 64)
    with pytest.raises(ValueError, match="every randomised unit"):
        RandomisationTest(
            12,
            6,
            Fraction(1, 20),
            "cluster",
            "two_arm_continuous",
            120,
            120,
            population="per_protocol",
        )


@pytest.mark.parametrize(
    "population,condition",
    [("per_protocol", PER_PROTOCOL_POPULATION), ("randomised", RANDOMISED_POPULATION)],
)
def test_an_exact_test_claim_says_which_population_it_covers(population, condition):
    compilation = compiled(arms(population) + RESPONSE + FISHER + "verify typeI(analysis)\n")
    assert not compilation.diagnostics
    (claim,) = inspect_program(compilation)
    assert condition.text in claim["assumptions"]
    assert statuses(compilation)[condition.id] == "condition"
    register = study_report(compilation, "study.stat")["assumption_register"]
    assert next(item for item in register if item["id"] == condition.id)["status"] == "condition"
    # The derivation and the certificate are the same for either population.
    assert condition.text not in derivation(compilation)["assumptions"]


def test_a_cited_claim_says_which_population_it_covers(tmp_path):
    text = USES + arms("per_protocol") + PAIN + T_TEST + "verify typeI(analysis)\n"
    report = check_source(Source(text, "study.stat"), project=tmp_path, output=tmp_path / "run")
    (request,) = report["requests"]
    assert request["status"] == "cited"
    found = request["value"]["evidence"]["assumptions"]
    assert {"id": "per_protocol_population", "status": "condition"}.items() <= next(
        item for item in found if item["id"] == "per_protocol_population"
    ).items()
    # Listed once, though the run adds conditions after the compile-time description.
    assert [item["id"] for item in found].count("per_protocol_population") == 1


def test_a_family_lists_each_population_once():
    text = (
        arms("per_protocol")
        + PAIN
        + "let first = t_test(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/40)\n"
        + "let second = welch_test(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/40)\n"
        + "let family = bonferroni(analyses=[first, second], alpha=1/20)\n"
        + "verify familywise(family)\n"
    )
    compilation = compiled(text)
    assert not compilation.diagnostics, compilation.diagnostics
    (claim,) = inspect_program(compilation)
    assert claim["assumptions"].count(PER_PROTOCOL_POPULATION.text) == 1


def test_a_declared_test_may_take_a_per_protocol_population():
    text = (
        arms("per_protocol")
        + PAIN
        + "let analysis = declared_test(design=fixed(model=study), null=no_effect(model=study), "
        'alpha=1/20, method="Permutation test on completers")\n'
    )
    assert codes(text) == []


def test_tests_without_an_assignment_population_have_no_condition():
    compilation = compiled(arms() + RESPONSE + FISHER + "verify typeI(analysis)\n")
    (claim,) = inspect_program(compilation)
    assert not {item["id"] for item in claim["identified_assumptions"]} & {
        "randomised_population",
        "per_protocol_population",
    }


def test_a_per_protocol_claim_assumes_the_exclusions_were_not_chosen_from_the_results():
    # Per-protocol arm sizes count those left after exclusions, so the file cannot show
    # that they were fixed before outcomes: the claim lists that as assumed.
    claim = RESPONSE + FISHER + "verify typeI(analysis)\n"
    assert statuses(compiled(arms("per_protocol") + claim))[PRESPECIFIED_EXCLUSIONS.id] == "assumed"
    assert PRESPECIFIED_EXCLUSIONS.id not in statuses(compiled(arms("randomised") + claim))
    # The sentence says "fixed before", but it is not the design's declaration.
    assert identify(PRESPECIFIED_EXCLUSIONS.text)["status"] == "assumed"


def test_the_one_call_spelling_declares_a_population():
    text = (
        'let study = two_arm_binomial(n_control=26, n_treatment=24, population="per_protocol")\n'
        + FISHER
        + "verify typeI(analysis)\n"
    )
    found = statuses(compiled(text))
    assert found[PER_PROTOCOL_POPULATION.id] == "condition"
    assert found[PRESPECIFIED_EXCLUSIONS.id] == "assumed"
