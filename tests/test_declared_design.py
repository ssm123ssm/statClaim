"""Clusters and repeated measurements, declared on the model's pieces and checked."""

import copy
import subprocess

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language import normalize
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import inspect_program
from statclaim.language_syntax import Source

USES = (
    "use models.two_arm_binomial\nuse models.two_arm_continuous\nuse models.two_arm_survival\n"
    "use sampling\nuse tests.t\nuse tests.mixed_model\nuse tests.survival\nuse tests.logistic\n"
    "use tests.fisher\nuse tests.difference\nuse tests.declared\nuse estimation\nuse planning\n"
    "use multiplicity.bonferroni\n"
)
CLUSTERS = (
    "let arms = cluster_assignment(clusters_control=8, clusters_treatment=8, n_control=160, "
    "n_treatment=160)\n"
)
INDIVIDUAL = "let arms = assignment(n_control=100, n_treatment=100)\n"
REPEATED = (
    INDIVIDUAL + "let study = two_arm(assignment=arms, outcome=continuous_outcome("
    'better="higher", measurements=3))\n'
)


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


def checked(text):
    """Compile, require no diagnostics, and re-check every derivation independently."""
    compilation = compiled(text)
    assert not compilation.diagnostics, compilation.diagnostics
    for derivation in compilation.derivations:
        assert check_derivation(derivation.to_dict()) == [], derivation.name
    return compilation


def derivation(compilation, name):
    return next(d for d in compilation.derivations if d.name == name).to_dict()


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize("test", ["t_test", "welch_test"])
def test_a_test_of_one_value_per_participant_refuses_repeated_measurements(test):
    text = REPEATED + (
        f"let analysis = {test}(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/20)\n"
    )
    diagnostics = compiled(text).diagnostics
    assert [d.code for d in diagnostics] == ["unit_mismatch"]
    assert "measured 3 times" in diagnostics[0].message
    assert "mmrm_test" in diagnostics[0].message


def test_a_mixed_model_takes_repeated_measurements_and_the_checker_agrees():
    text = REPEATED + (
        "let analysis = mmrm_test(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/20)\nverify typeI(analysis)\n"
    )
    compilation = checked(text)
    step = next(
        s for s in derivation(compilation, "analysis")["steps"] if s["rule"] == "declared-design"
    )
    assert step["facts"]["design"] == "3 measurements per participant"
    assert [claim["best_status"] for claim in inspect_program(compilation)] == ["cited"]


@pytest.mark.parametrize(
    "analysis",
    [
        "t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)",
        "mmrm_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)",
    ],
)
def test_continuous_tests_refuse_randomisation_by_cluster(analysis):
    text = CLUSTERS + "let study = two_arm(assignment=arms, outcome=continuous_outcome())\n"
    diagnostics = compiled(text + f"let analysis = {analysis}\n").diagnostics
    assert [d.code for d in diagnostics] == ["unit_mismatch"]
    assert (
        "8 control and 8 treatment clusters" in diagnostics[0].message
        and "declared_test" in diagnostics[0].message
    )


@pytest.mark.parametrize(
    "analysis",
    [
        "fisher(design=fixed(model=study), null=equal_proportions(model=study), alpha=1/20)",
        "fisher_one_sided(design=fixed(model=study), null=proportion_difference_at_most("
        "model=study, value=0), alpha=1/20)",
        "difference_test(design=fixed(model=study), null=proportion_difference_at_most("
        "model=study, value=-1/10), alpha=1/40)",
        "logistic_regression(design=fixed(model=study), null=equal_proportions(model=study), "
        "alpha=1/20)",
        "difference_interval(model=study, control_successes=40, treatment_successes=60, "
        "level=19/20)",
    ],
)
def test_binary_tests_and_intervals_refuse_randomisation_by_cluster(analysis):
    text = CLUSTERS + "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
    assert codes(text + f"let analysis = {analysis}\n") == ["unit_mismatch"]


def test_the_log_rank_test_refuses_randomisation_by_cluster():
    text = CLUSTERS + (
        "let study = two_arm(assignment=arms, outcome=survival_outcome())\n"
        "let analysis = log_rank(design=fixed(model=study), null=equal_survival(model=study), "
        "alpha=1/20)\n"
    )
    assert codes(text) == ["unit_mismatch"]


@pytest.mark.parametrize(
    ("design", "vouched"),
    [
        (
            CLUSTERS + "let study = two_arm(assignment=arms, outcome=continuous_outcome())\n",
            "accounts_for_clusters",
        ),
        (REPEATED, "accounts_for_repeated_measures"),
    ],
)
def test_a_declared_test_takes_the_design_on_the_authors_word(design, vouched):
    text = design + (
        "let analysis = declared_test(design=fixed(model=study), null=equal_means(model=study), "
        'alpha=1/20, method="Mixed model with a random effect")\nverify typeI(analysis)\n'
    )
    compilation = checked(text)
    (claim,) = inspect_program(compilation)
    assert claim["best_status"] == "declared"
    assert vouched in [item["id"] for item in claim["identified_assumptions"]]
    assert vouched in derivation(compilation, "analysis")["guarantee"]["given"]


def test_families_and_power_carry_the_declared_design():
    text = REPEATED + (
        "let symptoms = mmrm_test_one_sided(design=fixed(model=study), "
        "null=mean_difference_at_most(model=study, value=0), alpha=1/40)\n"
        "let binary = two_arm_binomial(n_control=100, n_treatment=100)\n"
        "let response = fisher(design=fixed(model=binary), null=equal_proportions(model=binary), "
        "alpha=1/40)\n"
        "let family = bonferroni(analyses=[symptoms, response], alpha=1/20)\n"
        "verify familywise(family)\n"
        "let target = power_target(at=mean_difference(value=3, sd=10), minimum=4/5, "
        "maximum_typeI=1/40)\n"
        "let power = calculate(meets(analysis=symptoms, target=target))\n"
    )
    compilation = checked(text)
    assert [claim["best_status"] for claim in inspect_program(compilation)] == [
        "conditional",
        "calculated",
    ]


def test_the_checker_rejects_a_derivation_that_hides_or_alters_the_design():
    text = REPEATED + (
        "let analysis = mmrm_test(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/20)\n"
    )
    recorded = derivation(checked(text), "analysis")
    index = next(i for i, s in enumerate(recorded["steps"]) if s["rule"] == "declared-design")
    hidden = copy.deepcopy(recorded)
    del hidden["steps"][index]
    assert check_derivation(hidden)
    altered = copy.deepcopy(recorded)
    altered["subject"]["design"]["model"]["measurements"] = 4
    altered["subject"]["null"]["model"]["measurements"] = 4
    assert check_derivation(altered)
    clustered = copy.deepcopy(recorded)
    for part in ("design", "null"):
        clustered["subject"][part]["model"].update(clusters_control=5, clusters_treatment=5)
    assert check_derivation(clustered)


def test_a_plain_design_records_nothing_new():
    """Files that declare no clusters or repeated measurements keep their records."""
    one = (
        INDIVIDUAL
        + "let study = two_arm(assignment=arms, outcome=continuous_outcome(measurements=1))\n"
    )
    short = "let study = two_arm_continuous(n_control=100, n_treatment=100)\n"
    analysis = (
        "let analysis = t_test(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/20)\n"
    )
    first, second = checked(one + analysis), checked(short + analysis)
    assert derivation(first, "analysis") == derivation(second, "analysis")
    assert "declared-design" not in [s["rule"] for s in derivation(first, "analysis")["steps"]]


def test_the_records_name_clusters_and_measurements():
    values = {
        b.name: normalize(b.value)
        for b in checked(
            CLUSTERS + "let study = two_arm(assignment=arms, outcome=continuous_outcome("
            "measurements=2))\n"
        ).program.bindings
    }
    assert values["arms"] == {
        "n_control": 160,
        "n_treatment": 160,
        "clusters_control": 8,
        "clusters_treatment": 8,
    }
    assert values["study"]["measurements"] == 2 and values["study"]["clusters_treatment"] == 8


@pytest.mark.parametrize(
    ("line", "code"),
    [
        (
            "let bad = cluster_assignment(clusters_control=0, clusters_treatment=4, "
            "n_control=40, n_treatment=40)",
            "domain",
        ),
        (
            "let bad = cluster_assignment(clusters_control=4, clusters_treatment=50, "
            "n_control=40, n_treatment=40)",
            "domain",
        ),
        ("let bad = continuous_outcome(measurements=0)", "domain"),
        ("let bad = binary_outcome(measurements=2)", "arguments"),
        ("let bad = survival_outcome(measurements=2)", "arguments"),
    ],
)
def test_malformed_design_declarations_are_refused(line, code):
    assert codes(line + "\n") == [code]


def test_a_null_on_a_model_with_other_pieces_is_named_as_such():
    text = REPEATED + (
        'let plain = two_arm(assignment=arms, outcome=continuous_outcome(better="higher"))\n'
        "let analysis = mmrm_test(design=fixed(model=study), null=equal_means(model=plain), "
        "alpha=1/20)\n"
    )
    diagnostics = compiled(text).diagnostics
    assert [d.code for d in diagnostics] == ["model_mismatch"]
    assert "same arm sizes but differ in their assignment or outcome" in diagnostics[0].message
