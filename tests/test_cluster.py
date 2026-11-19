"""The cited t-test on cluster-level summaries: units, minimums, messages and derivations."""

import copy
import subprocess
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import inspect_program
from statclaim.language_syntax import Source
from statclaim.methods import METHODS
from statclaim.methods.assumptions import CONTRADICTED_BY

ROOT = Path(__file__).resolve().parents[1]
USES = (
    "use models.two_arm_continuous\nuse models.two_arm_binomial\nuse sampling\nuse tests.t\n"
    "use tests.cluster\nuse tests.fisher\nuse tests.declared\nuse multiplicity.bonferroni\n"
)
CLINICS = (
    "let arms = cluster_assignment(clusters_control={c}, clusters_treatment={c}, "
    "n_control=120, n_treatment=120)\n"
)
STUDY = "let study = two_arm(assignment=arms, outcome=continuous_outcome({outcome}))\n"
TEST = (
    "let analysis = {test}(design=fixed(model=study), null=equal_means(model=study), "
    "alpha={alpha})\n"
)


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def source(c=6, outcome="", test="cluster_t_test", alpha="1/20"):
    return CLINICS.format(c=c) + STUDY.format(outcome=outcome) + TEST.format(test=test, alpha=alpha)


def derivation(compilation, name="analysis"):
    return next(d for d in compilation.derivations if d.name == name).to_dict()


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_the_method_takes_clusters_and_is_cited():
    method = METHODS["cluster_t_test"]
    assert method.unit == "cluster" and method.min_per_arm == 4
    assert {a.id for a in method.assumptions} == {
        "independent_clusters",
        "fixed_sample_sizes",
        "single_analysis",
        "normal_cluster_summaries",
    }
    # Clusters contradict independent participants, not independent clusters.
    assert "independent_clusters" not in CONTRADICTED_BY["clusters"]
    assert all(reference.endswith("[to verify]") for reference in method.references)
    assert any("Donner" in r for r in method.references)
    assert any("Hayes" in r for r in method.references)


def test_a_cluster_randomised_trial_gets_a_cited_claim_and_a_checked_derivation():
    compilation = compiled(source() + "verify typeI(analysis)\n")
    assert not compilation.diagnostics
    record = derivation(compilation)
    assert check_derivation(record) == []
    assert [step["rule"] for step in record["steps"]] == [
        "same-model",
        "supported-null",
        "level-interior",
        "enough-clusters",
        "declared-design",
        "cluster-contract",
        "fixed-sampling",
    ]
    assert record["steps"][3]["conclusion"] == (
        "analysis: (6, 6) clusters per arm meet the method's minimum of 4 per arm and 8 in total."
    )
    assert record["guarantee"]["grade"] == "cited"
    assert record["guarantee"]["scope"] == "finite_sample"
    (claim,) = inspect_program(compilation)
    assert claim["best_status"] == "cited"
    ids = {item["id"] for item in claim["identified_assumptions"]}
    assert {"independent_clusters", "normal_cluster_summaries"} <= ids


def test_repeated_measurements_within_clusters_are_accepted():
    compilation = compiled(source(outcome="measurements=3"))
    assert not compilation.diagnostics
    assert check_derivation(derivation(compilation)) == []


def test_participants_randomised_one_by_one_are_refused():
    text = (
        "let arms = assignment(n_control=120, n_treatment=120)\n"
        + STUDY.format(outcome="")
        + TEST.format(test="cluster_t_test", alpha="1/20")
    )
    (diagnostic,) = compiled(text).diagnostics
    assert diagnostic.code == "unit_mismatch"
    assert "one summary per cluster" in diagnostic.message
    assert "cluster_assignment(...)" in diagnostic.message


def test_too_few_clusters_are_refused_and_the_minimum_is_in_clusters():
    (diagnostic,) = compiled(source(c=3)).diagnostics
    assert diagnostic.code == "domain"
    assert "at least 4 clusters per arm" in diagnostic.message
    assert "randomises 3 and 3" in diagnostic.message
    assert not compiled(source(c=4)).diagnostics


def test_only_a_continuous_outcome_and_the_equal_means_null_are_supported():
    binary = (
        CLINICS.format(c=6)
        + "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
        + "let analysis = cluster_t_test(design=fixed(model=study), "
        "null=equal_proportions(model=study), alpha=1/20)\n"
    )
    assert [d.code for d in compiled(binary).diagnostics] == ["hypothesis_mismatch"]
    one_sided = (
        CLINICS.format(c=6)
        + STUDY.format(outcome="")
        + "let analysis = cluster_t_test(design=fixed(model=study), "
        "null=mean_difference_at_most(model=study, value=0), alpha=1/20)\n"
    )
    assert [d.code for d in compiled(one_sided).diagnostics] == ["hypothesis_mismatch"]


def test_the_unit_mismatch_message_names_the_tests_that_fit():
    (t_test,) = compiled(source(test="t_test")).diagnostics
    assert t_test.code == "unit_mismatch"
    assert "Use cluster_t_test" in t_test.message and "randomisation_test" in t_test.message
    fisher = (
        CLINICS.format(c=6)
        + "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
        + "let analysis = fisher(design=fixed(model=study), null=equal_proportions(model=study), "
        "alpha=1/20)\n"
    )
    (diagnostic,) = compiled(fisher).diagnostics
    # For a binary outcome the fitting cited test is the one on cluster proportions.
    assert "Use cluster_proportion_t_test" in diagnostic.message
    assert "cluster_t_test," not in diagnostic.message
    assert "randomisation_test" in diagnostic.message


BINARY = (
    "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
    "let analysis = cluster_proportion_t_test(design=fixed(model=study), "
    "null=equal_proportions(model=study), alpha=1/20)\n"
)


def test_a_binary_outcome_by_cluster_gets_the_proportion_test():
    method = METHODS["cluster_proportion_t_test"]
    assert method.unit == "cluster" and method.outcome == "binary"
    assert "normal_cluster_proportions" in {a.id for a in method.assumptions}
    compilation = compiled(CLINICS.format(c=6) + BINARY + "verify typeI(analysis)\n")
    assert not compilation.diagnostics
    record = derivation(compilation)
    assert check_derivation(record) == []
    assert record["steps"][3]["rule"] == "enough-clusters"
    assert [claim["best_status"] for claim in inspect_program(compilation)] == ["cited"]
    individual = "let arms = assignment(n_control=120, n_treatment=120)\n" + BINARY
    assert [d.code for d in compiled(individual).diagnostics] == ["unit_mismatch"]
    assert [d.code for d in compiled(CLINICS.format(c=3) + BINARY).diagnostics] == ["domain"]


def test_a_family_with_a_cluster_level_member_is_checked():
    text = (
        source(alpha="1/40")
        + "let other = declared_test(design=fixed(model=study), null=equal_means(model=study), "
        'alpha=1/40, method="Mixed model with a random intercept for clinic")\n'
        + "let family = bonferroni(analyses=[analysis, other], alpha=1/20)\n"
    )
    compilation = compiled(text)
    assert not compilation.diagnostics
    assert [check_derivation(d.to_dict()) for d in compilation.derivations] == [[], [], []]


def _three_clusters(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        model.update(clusters_control=3, clusters_treatment=3)
    record["steps"][3]["facts"].update(clusters_control=3, clusters_treatment=3)
    record["steps"][3]["conclusion"] = record["steps"][3]["conclusion"].replace("(6, 6)", "(3, 3)")


def _no_clusters(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        del model["clusters_control"], model["clusters_treatment"]


def _participants_counted(record):
    step = record["steps"][3]
    step["rule"] = "enough-data"
    step["facts"] = {
        "subject": "analysis",
        "n_control": 120,
        "n_treatment": 120,
        "min_per_arm": 4,
        "min_total": 8,
    }


def _plain_contract(record):
    record["steps"][5]["rule"] = "cited-contract"


def _lower_minimum(record):
    record["steps"][3]["facts"]["min_per_arm"] = 2


def _independence_dropped(record):
    record["assumptions"] = record["assumptions"][1:]


@pytest.mark.parametrize(
    "change",
    [
        _three_clusters,
        _no_clusters,
        _participants_counted,
        _plain_contract,
        _lower_minimum,
        _independence_dropped,
    ],
)
def test_the_checker_rejects_tampered_cluster_derivations(change):
    record = derivation(compiled(source()))
    assert check_derivation(record) == []
    altered = copy.deepcopy(record)
    change(altered)
    assert check_derivation(altered) != []


def test_the_example_compiles_with_a_cited_and_a_proved_claim():
    path = ROOT / "examples/cluster_trial.stat"
    compilation = compile_source(Source(path.read_text(), str(path)))
    assert compilation.status == "elaborated"
    assert [claim["best_status"] for claim in inspect_program(compilation)] == [
        "cited",
        "verified",
    ]
    assert [check_derivation(d.to_dict()) for d in compilation.derivations] == [[], []]
