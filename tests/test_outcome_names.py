"""Named outcomes: one name is one outcome, and a family asks each question of it once.

Without names, two analyses with the same content could be two outcomes measured on the
same participants. With a name, the same test of the same null of one outcome on the same
participants, listed twice in a family, is caught.
"""

import copy
import subprocess

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language import normalize
from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source

USES = (
    "use models.two_arm_binomial\nuse models.two_arm_continuous\nuse sampling\n"
    "use tests.fisher\nuse tests.difference\nuse tests.t\nuse tests.randomisation\n"
    "use designs.group_sequential\nuse multiplicity.bonferroni\n"
    "use multiplicity.fixed_sequence\n"
)
ARMS = "let arms = assignment(n_control=100, n_treatment=100)\n"
RESPONSE = 'let study = two_arm(assignment=arms, outcome=binary_outcome(name="response"))\n'
PAIN = 'let study = two_arm(assignment=arms, outcome=continuous_outcome(name="pain"))\n'


def fisher(name, alpha="1/40", model="study"):
    return (
        f"let {name} = fisher(design=fixed(model={model}), null=equal_proportions(model={model}), "
        f"alpha={alpha})\n"
    )


def t_test(name, test="t_test", alpha="1/40", model="study"):
    return (
        f"let {name} = {test}(design=fixed(model={model}), null=equal_means(model={model}), "
        f"alpha={alpha})\n"
    )


FAMILY = "let family = bonferroni(analyses=[{members}], alpha=1/20)\nverify familywise(family)\n"


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def errors(text):
    return [(d.code, d.message) for d in compiled(text).diagnostics]


def derivation(compilation, name="family"):
    return next(d for d in compilation.derivations if d.name == name).to_dict()


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_a_name_is_recorded_on_the_outcome_and_the_model():
    compilation = compiled(ARMS + RESPONSE)
    assert not compilation.diagnostics
    model = compilation.program.bindings[-1].value
    assert model.measured.name == "response"
    assert normalize(model.measured)["name"] == "response"
    assert normalize(model)["outcome_name"] == "response"
    plain = compiled(ARMS + "let study = two_arm(assignment=arms, outcome=binary_outcome())\n")
    assert "outcome_name" not in normalize(plain.program.bindings[-1].value)


@pytest.mark.parametrize("name", ['""', '"   "', '"pain\\nscore"', '"' + "x" * 101 + '"'])
def test_a_name_must_be_one_short_line(name):
    text = ARMS + f"let study = two_arm(assignment=arms, outcome=binary_outcome(name={name}))\n"
    assert errors(text)[0][0] == "domain"


def test_the_same_question_of_a_named_outcome_twice_is_refused():
    text = (
        ARMS + RESPONSE + fisher("first") + fisher("again") + FAMILY.format(members="first, again")
    )
    ((code, message), *_) = errors(text)
    assert code == "duplicate_analysis"
    assert 'first and again ask the same question of the outcome "response"' in message


def test_a_different_level_does_not_make_a_different_question():
    text = (
        ARMS
        + RESPONSE
        + fisher("first", "1/40")
        + fisher("again", "1/80")
        + FAMILY.format(members="first, again")
    )
    assert errors(text)[0][0] == "duplicate_analysis"


def test_one_outcome_declared_in_two_models_is_one_outcome():
    text = (
        ARMS
        + RESPONSE
        + 'let copy = two_arm(assignment=arms, outcome=binary_outcome(name="response"))\n'
        + fisher("first")
        + fisher("again", model="copy")
        + FAMILY.format(members="first, again")
    )
    assert errors(text)[0][0] == "duplicate_analysis"


def test_different_questions_of_one_outcome_are_allowed():
    # Two tests of one null, and non-inferiority then superiority in a fixed sequence.
    tests = ARMS + PAIN + t_test("pooled") + t_test("welch", "welch_test")
    assert errors(tests + FAMILY.format(members="pooled, welch")) == []
    margins = (
        ARMS
        + RESPONSE
        + "let worse = proportion_difference_at_most(model=study, value=-1/10)\n"
        + "let noninferior = difference_test(design=fixed(model=study), null=worse, alpha=1/20)\n"
        + fisher("superior", "1/20")
        + "let order = fixed_sequence(analyses=[noninferior, superior], alpha=1/20)\n"
    )
    assert errors(margins) == []


def test_looks_at_one_named_outcome_are_allowed():
    text = (
        "let half = two_arm(assignment=assignment(n_control=50, n_treatment=50), "
        'outcome=continuous_outcome(name="pain"))\n'
        "let full = two_arm(assignment=assignment(n_control=100, n_treatment=100), "
        'outcome=continuous_outcome(name="pain"))\n'
        + t_test("interim", alpha="1/200", model="half")
        + t_test("final", alpha="9/200", model="full")
        + "let trial = alpha_spending(looks=[interim, final], alpha=1/20)\n"
    )
    assert errors(text) == []


@pytest.mark.parametrize(
    "second,kind",
    [
        ('continuous_outcome(name="response")', "a continuous outcome"),
        ('binary_outcome(name="response", better="lower")', 'better="lower"'),
    ],
)
def test_one_name_cannot_be_two_outcomes(second, kind):
    text = (
        ARMS + 'let study = two_arm(assignment=arms, outcome=binary_outcome(name="response", '
        'better="higher"))\n'
        + f"let other = two_arm(assignment=arms, outcome={second})\n"
        + fisher("first")
        + (
            t_test("second", model="other")
            if "continuous" in second
            else fisher("second", model="other")
        )
        + FAMILY.format(members="first, second")
    )
    ((code, message), *_) = errors(text)
    assert code == "outcome_conflict"
    assert '"response"' in message and kind in message


def test_a_question_repeated_inside_a_nested_combination_is_refused():
    text = (
        ARMS
        + RESPONSE
        + fisher("first")
        + fisher("second", "1/80")
        + fisher("again", "1/80")
        + "let inner = bonferroni(analyses=[second, again], alpha=1/40)\n"
    )
    assert errors(text)[0][0] == "duplicate_analysis"
    across = (
        ARMS
        + RESPONSE
        + 'let other = two_arm(assignment=arms, outcome=binary_outcome(name="relapse"))\n'
        + fisher("first")
        + fisher("relapse", "1/80", model="other")
        + fisher("again", "1/80")
        + "let inner = bonferroni(analyses=[relapse, again], alpha=1/40)\n"
        + FAMILY.format(members="first, inner")
    )
    ((code, message), *_) = errors(across)
    assert code == "duplicate_analysis" and '"response"' in message


def test_unnamed_outcomes_keep_the_old_behaviour():
    text = (
        ARMS
        + "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
        + fisher("first")
        + fisher("again")
        + FAMILY.format(members="first, again")
    )
    compilation = compiled(text)
    assert not compilation.diagnostics
    rules = [step["rule"] for step in derivation(compilation)["steps"]]
    assert "distinct-questions" not in rules


@pytest.mark.parametrize(
    "piece,tests",
    [
        (RESPONSE, fisher("first") + fisher("second", model="other")),  # a proved Fisher family
        (PAIN, t_test("first") + t_test("second", model="other")),  # a composed family
    ],
)
def test_the_derivation_records_and_checks_distinct_questions(piece, tests):
    other = piece.replace("let study", "let other").replace('"response"', '"relapse"')
    other = other.replace('"pain"', '"function"')
    compilation = compiled(ARMS + piece + other + tests + FAMILY.format(members="first, second"))
    assert not compilation.diagnostics, compilation.diagnostics
    record = derivation(compilation)
    assert check_derivation(record) == []
    step = next(s for s in record["steps"] if s["rule"] == "distinct-questions")
    assert set(step["facts"]["outcomes"].split(", ")) in (
        {"response", "relapse"},
        {"pain", "function"},
    )
    # A forged record whose two members ask the same question fails the check.
    forged = copy.deepcopy(record)
    first, second = forged["subject"]["analyses"]
    second["analysis"] = copy.deepcopy(first["analysis"])
    assert check_derivation(forged)


def test_randomisation_tests_with_named_outcomes_join_families():
    text = (
        'let arms = assignment(n_control=20, n_treatment=20, randomisation="complete")\n'
        + PAIN
        + "let exact = randomisation_test(design=fixed(model=study), null=no_effect(model=study), "
        "alpha=1/40, draws=999)\n" + t_test("cited") + FAMILY.format(members="exact, cited")
    )
    compilation = compiled(text)
    assert not compilation.diagnostics
    assert check_derivation(derivation(compilation)) == []
    twice = text.replace("exact, cited", "exact, again").replace(
        "let family",
        "let again = randomisation_test(design=fixed(model=study), "
        "null=no_effect(model=study), alpha=1/40, draws=999)\nlet family",
    )
    assert errors(twice)[0][0] == "duplicate_analysis"


def test_the_name_and_the_population_can_be_read_back(tmp_path):
    from statclaim.language_runner import check_source

    text = (
        'let arms = assignment(n_control=10, n_treatment=10, population="per_protocol")\n'
        + RESPONSE
        + "let what = study.outcome.name\nlet who = study.assignment.population\n"
        + "let unnamed = binary_outcome().name\n"
    )
    report = check_source(Source(USES + text, "study.stat"), project=tmp_path, elaborate_only=True)
    values = report["values"]
    assert (values["what"], values["who"], values["unnamed"]) == ("response", "per_protocol", None)


def test_a_null_on_another_named_outcome_is_a_different_model():
    text = (
        ARMS
        + RESPONSE
        + 'let other = two_arm(assignment=arms, outcome=binary_outcome(name="relapse"))\n'
        + "let mixed = fisher(design=fixed(model=study), null=equal_proportions(model=other), "
        "alpha=1/20)\n"
    )
    ((code, message),) = errors(text)
    assert code == "model_mismatch" and "differ in their assignment or outcome" in message


def test_the_one_call_spelling_names_an_outcome():
    text = (
        'let study = two_arm_binomial(n_control=100, n_treatment=100, name="response")\n'
        + fisher("first")
        + fisher("again")
        + FAMILY.format(members="first, again")
    )
    ((code, message), *_) = errors(text)
    assert code == "duplicate_analysis" and '"response"' in message
