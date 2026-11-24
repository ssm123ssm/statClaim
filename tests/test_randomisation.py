"""Randomisation tests: the sharp null, the declared scheme, derivations and certificates.

Nothing here starts Lean; tests/test_lean_translation.py proves these claims in Lean.
"""

import copy
import subprocess
from fractions import Fraction
from math import comb
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import inspect_program
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.randomisation import (
    MAX_UNITS,
    RandomisationTest,
    render_randomisation_proof,
    splits_needed,
)

ROOT = Path(__file__).resolve().parents[1]
USES = (
    "use models.two_arm_binomial\nuse models.two_arm_continuous\nuse models.two_arm_survival\n"
    "use sampling\nuse tests.randomisation\nuse tests.t\nuse tests.mixed_model\n"
    "use tests.survival\nuse tests.logistic\nuse tests.fisher\nuse tests.declared\n"
)
ARMS = 'let arms = assignment(n_control=20, n_treatment=20, randomisation="complete")\n'
CLINICS = (
    "let arms = cluster_assignment(clusters_control={c}, clusters_treatment={c}, "
    'n_control=120, n_treatment=120, randomisation="complete")\n'
)
STUDY = 'let study = two_arm(assignment=arms, outcome=continuous_outcome(better="higher"))\n'
TEST = (
    "let analysis = randomisation_test(design=fixed(model=study), null=no_effect(model=study), "
    "alpha=1/20)\n"
)


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def diagnostics(text):
    return [(d.code, d.message) for d in compiled(text).diagnostics]


def derivation(compilation, name="analysis"):
    return next(d for d in compilation.derivations if d.name == name).to_dict()


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_a_declared_randomisation_gives_a_proved_claim_and_a_checked_derivation():
    compilation = compiled(ARMS + STUDY + TEST + "verify typeI(analysis)\n")
    assert not compilation.diagnostics
    record = derivation(compilation)
    assert check_derivation(record) == []
    assert [step["rule"] for step in record["steps"]] == [
        "same-model",
        "supported-null",
        "level-range",
        "declared-randomisation",
        "can-reject",
        "randomisation-contract",
        "fixed-sampling",
    ]
    assert record["steps"][4]["facts"] == {
        "subject": "analysis",
        "splits": "137846528820",
        "alpha": "1/20",
    }
    (claim,) = inspect_program(compilation)
    assert claim["best_status"] == "verified" and claim["scope"] == "finite_sample"
    ids = {item["id"]: item["status"] for item in claim["identified_assumptions"]}
    assert ids == {
        "complete_randomisation": "declared",
        "prespecified_analysis": "declared",
        "analysed_as_randomised": "assumed",
        "bound_under_null": "condition",
    }


def test_clusters_are_the_randomised_units():
    compilation = compiled(CLINICS.format(c=6) + STUDY + TEST)
    assert not compilation.diagnostics
    test = compilation.program.bindings[-1].value.lower()
    assert (test.unit, test.units, test.treated, test.splits) == ("cluster", 12, 6, 924)
    step = derivation(compilation)["steps"][3]
    assert step["conclusion"] == (
        "analysis: the assignment declares complete randomisation of 12 clusters, 6 treated."
    )
    assert check_derivation(derivation(compilation)) == []


@pytest.mark.parametrize(
    "outcome",
    ["binary_outcome()", "continuous_outcome(measurements=3)", "survival_outcome()"],
)
def test_any_outcome_and_repeated_measurements_are_accepted(outcome):
    text = ARMS + f"let study = two_arm(assignment=arms, outcome={outcome})\n" + TEST
    compilation = compiled(text)
    assert not compilation.diagnostics
    assert check_derivation(derivation(compilation)) == []


@pytest.mark.parametrize(
    "test,null",
    [
        ("t_test", "no_effect"),
        ("welch_test", "no_effect"),
        ("mmrm_test", "no_effect"),
        ("t_test_one_sided", "no_effect"),
        ("randomisation_test", "equal_means"),
        ("randomisation_test", "mean_difference_at_most"),
    ],
)
def test_the_sharp_null_and_mean_nulls_never_stand_in_for_each_other(test, null):
    value = ", value=0" if null == "mean_difference_at_most" else ""
    text = (
        ARMS
        + STUDY
        + f"let analysis = {test}(design=fixed(model=study), null={null}(model=study{value}), "
        "alpha=1/20)\n"
    )
    ((code, message),) = diagnostics(text)
    assert code == "hypothesis_mismatch"
    assert "not a proof that your null is false" in message


@pytest.mark.parametrize(
    "outcome,test",
    [("survival_outcome()", "log_rank"), ("binary_outcome()", "logistic_regression")],
)
def test_other_outcomes_cited_tests_refuse_the_sharp_null(outcome, test):
    text = (
        ARMS
        + f"let study = two_arm(assignment=arms, outcome={outcome})\n"
        + f"let analysis = {test}(design=fixed(model=study), null=no_effect(model=study), "
        "alpha=1/20)\n"
    )
    assert [code for code, _ in diagnostics(text)] == ["hypothesis_mismatch"]


def test_exact_binomial_tests_refuse_the_sharp_null_and_declared_tests_take_it():
    binary = ARMS + "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
    fisher = binary + (
        "let analysis = fisher(design=fixed(model=study), null=no_effect(model=study), "
        "alpha=1/20)\n"
    )
    assert [code for code, _ in diagnostics(fisher)] == ["type"]
    declared = (
        ARMS
        + STUDY
        + "let analysis = declared_test(design=fixed(model=study), null=no_effect(model=study), "
        'alpha=1/20, method="A permutation test")\n'
    )
    # A declared test takes any null on the author's word, such as a stratified
    # permutation test of the sharp null, and the checker re-derives its contract.
    compilation = compiled(declared)
    assert not compilation.diagnostics
    record = derivation(compilation)
    assert record["guarantee"]["grade"] == "declared"
    assert "treatment changes no participant's outcome" in record["guarantee"]["sentence"]
    assert check_derivation(record) == []


def test_an_assignment_that_does_not_declare_its_randomisation_is_refused():
    text = "let arms = assignment(n_control=20, n_treatment=20)\n" + STUDY + TEST
    ((code, message),) = diagnostics(text)
    assert code == "undeclared_randomisation"
    assert 'randomisation="complete"' in message and "40 participants" in message


@pytest.mark.parametrize("scheme", ["minimisation", "Complete", ""])
def test_only_known_schemes_can_be_declared(scheme):
    text = f'let arms = assignment(n_control=20, n_treatment=20, randomisation="{scheme}")\n'
    ((code, message),) = diagnostics(text)
    assert code == "domain" and "not supported yet" in message


def test_too_few_clusters_to_ever_reject_is_refused():
    ((code, message),) = diagnostics(CLINICS.format(c=2) + STUDY + TEST)
    assert code == "never_rejects"
    assert "6 equally likely splits" in message and "at least 20 splits" in message
    # Three clusters per arm give exactly 20 splits: rejection is possible at 1/20.
    assert diagnostics(CLINICS.format(c=3) + STUDY + TEST) == []


def test_a_zero_level_is_refused():
    assert [code for code, _ in diagnostics(ARMS + STUDY + TEST.replace("1/20", "0"))] == ["domain"]


def test_too_many_units_are_refused():
    size = MAX_UNITS // 2 + 1
    text = (
        f'let arms = assignment(n_control={size}, n_treatment={size}, randomisation="complete")\n'
        + STUDY
        + TEST
    )
    assert [code for code, _ in diagnostics(text)] == ["domain"]


def test_data_dependent_stopping_leaves_an_obligation(tmp_path):
    text = ARMS + STUDY + TEST.replace("fixed(", "adaptive(") + "verify typeI(analysis)\n"
    compilation = compiled(text)
    assert [d.code for d in compilation.diagnostics] == ["sampling_scope"]
    record = derivation(compilation)
    assert [item["rule"] for item in record["obligations"]] == ["fixed-sampling"]
    assert check_derivation(record) == []
    report = check_source(Source(USES + text, "study.stat"), project=tmp_path)
    assert report["requests"][0]["status"] == "unresolved_obligation"


def test_the_model_records_its_randomisation_only_when_declared():
    plain = compiled("let arms = assignment(n_control=20, n_treatment=20)\n" + STUDY)
    declared = compiled(ARMS + STUDY + "let scheme = arms.randomisation\n")
    assert not declared.diagnostics
    model = declared.program.to_dict()["bindings"][1]["value"]
    assert model["randomisation"] == "complete"
    assert "randomisation" not in plain.program.to_dict()["bindings"][1]["value"]
    assert declared.program.bindings[-1].value == "complete"


def tamper(record, change):
    altered = copy.deepcopy(record)
    change(altered)
    return altered


def _no_scheme(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        del model["randomisation"]


def _blocked(record):
    record["subject"]["design"]["model"]["randomisation"] = "blocked"
    record["subject"]["null"]["model"]["randomisation"] = "blocked"
    record["steps"][3]["facts"]["randomisation"] = "blocked"
    record["steps"][3]["conclusion"] = record["steps"][3]["conclusion"].replace(
        "complete", "blocked"
    )


def _two_clusters(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        model.update(clusters_control=2, clusters_treatment=2)


def _mean_null(record):
    record["subject"]["null"]["predicate"] = "equal_means"


def _more_splits(record):
    record["steps"][4]["facts"]["splits"] = "1000000"
    record["steps"][4]["conclusion"] = record["steps"][4]["conclusion"].replace("924", "1000000")


def _cited_contract(record):
    record["contract"] = "tests.t/t_test"


def _fewer_assumptions(record):
    record["assumptions"] = record["assumptions"][:2]


def _no_sampling_step(record):
    record["steps"] = record["steps"][:-1]


def _a_guarantee(record):
    record["guarantee"] = {"grade": "cited", "sentence": "anything"}


@pytest.mark.parametrize(
    "change",
    [
        _no_scheme,
        _blocked,
        _two_clusters,
        _mean_null,
        _more_splits,
        _cited_contract,
        _fewer_assumptions,
        _no_sampling_step,
        _a_guarantee,
    ],
)
def test_the_checker_rejects_tampered_randomisation_derivations(change):
    record = derivation(compiled(CLINICS.format(c=6) + STUDY + TEST))
    assert check_derivation(record) == []
    assert check_derivation(tamper(record, change)) != []


@pytest.mark.parametrize(
    "arguments",
    [
        (4, 2, Fraction(1, 20)),  # 6 splits: never rejects
        (10, 0, Fraction(1, 20)),  # an empty arm
        (10, 10, Fraction(1, 20)),
        (MAX_UNITS + 2, 1, Fraction(1, 2)),
        (10, 5, Fraction(0)),
    ],
)
def test_invalid_designs_have_no_payload(arguments):
    units, treated, alpha = arguments
    with pytest.raises(ValueError):
        RandomisationTest(units, treated, alpha, "participant", "two_arm_continuous", 10, 10)


def test_the_proof_names_the_declared_numbers_and_the_general_theorem():
    test = RandomisationTest(40, 20, Fraction(1, 20), "participant", "two_arm_continuous", 20, 20)
    proof = render_randomisation_proof(test, "a" * 64)
    assert "def units : ℕ := 40" in proof and "def treatedUnits : ℕ := 20" in proof
    assert "card = 137846528820" in proof
    assert "Randomisation.typeI_of_level" in proof
    assert "STATCLAIM_CHECKED " + "a" * 64 in proof
    with pytest.raises(ValueError):
        render_randomisation_proof(test, "not a digest")


@pytest.mark.parametrize("alpha,needed", [(Fraction(1, 20), 20), (Fraction(3, 40), 14)])
def test_splits_needed(alpha, needed):
    assert splits_needed(alpha) == needed
    assert Fraction(1, needed) <= alpha < Fraction(1, needed - 1)


def test_the_example_compiles_and_every_derivation_passes():
    path = ROOT / "examples/randomisation.stat"
    compilation = compile_source(Source(path.read_text(), str(path)))
    assert compilation.status == "elaborated"
    assert [check_derivation(d.to_dict()) for d in compilation.derivations] == [[], []]


SITES = "strata=[stratum(control=8, treatment=8), stratum(control=12, treatment=12)]"


@pytest.mark.parametrize(
    "declaration,count,groups",
    [
        (f'randomisation="stratified", {SITES}', comb(16, 8) * comb(24, 12), 2),
        ('randomisation="blocked", block_size=4', 6**10, 10),
        (f'randomisation="blocked", block_size=4, {SITES}', 6**10, 10),
    ],
)
def test_stratified_and_blocked_randomisation_give_checked_derivations(declaration, count, groups):
    arms = f"let arms = assignment(n_control=20, n_treatment=20, {declaration})\n"
    compilation = compiled(arms + STUDY + TEST)
    assert not compilation.diagnostics
    record = derivation(compilation)
    assert check_derivation(record) == []
    assert record["steps"][4]["facts"]["splits"] == str(count)
    test = compilation.program.bindings[-1].value.lower()
    assert test.splits == count and len(test.groups) == groups
    claimed = USES + arms + STUDY + TEST + "verify typeI(analysis)\n"
    (claim,) = inspect_program(compile_source(Source(claimed, "s.stat")))
    assert claim["identified_assumptions"][0]["id"] == "stratified_randomisation"


def test_pair_matched_clusters_are_blocks_of_two():
    arms = (
        "let arms = cluster_assignment(clusters_control=6, clusters_treatment=6, n_control=120, "
        'n_treatment=120, randomisation="blocked", block_size=2)\n'
    )
    compilation = compiled(arms + STUDY + TEST)
    assert not compilation.diagnostics
    assert compilation.program.bindings[-1].value.lower().splits == 64
    assert check_derivation(derivation(compilation)) == []


@pytest.mark.parametrize(
    "declaration,fragment",
    [
        (SITES, "declare randomisation="),
        ("block_size=4", "declare randomisation="),
        (f'randomisation="complete", {SITES}', "no strata or blocks"),
        ('randomisation="stratified", strata=[stratum(control=20, treatment=20)]', "two strata"),
        ('randomisation="stratified", block_size=4, ' + SITES, 'randomisation="blocked"'),
        ('randomisation="blocked"', "needs block_size"),
        ('randomisation="blocked", block_size=1', "needs block_size"),
        ('randomisation="blocked", block_size=6', "whole blocks of 6"),
        (
            'randomisation="stratified", '
            "strata=[stratum(control=8, treatment=8), stratum(control=10, treatment=12)]",
            "add up to 18 control and 20 treatment",
        ),
        ('randomisation="stratified", strata=[1, 2]', "Each stratum must be stratum"),
    ],
)
def test_strata_and_blocks_that_do_not_describe_a_randomisation_are_refused(declaration, fragment):
    text = f"let arms = assignment(n_control=20, n_treatment=20, {declaration})\n"
    (code, message), *_ = diagnostics(text)
    assert code in ("domain", "type") and fragment in message


def test_a_stratum_needs_a_unit():
    text = "let s = stratum(control=0, treatment=0)\n"
    assert [code for code, _ in diagnostics(text)] == ["domain"]


def test_too_many_small_blocks_still_cannot_reach_a_tiny_level():
    arms = (
        "let arms = cluster_assignment(clusters_control=2, clusters_treatment=2, n_control=60, "
        'n_treatment=60, randomisation="blocked", block_size=2)\n'
    )
    ((code, message), *_) = diagnostics(arms + STUDY + TEST)
    assert code == "never_rejects" and "4 equally likely splits" in message


def _strata_off(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        model["strata"] = [[8, 8], [12, 10]]
    record["steps"][3]["facts"]["strata"] = [[8, 8], [12, 10]]


def _blocks_changed(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        model["block_size"] = 2
    record["steps"][3]["facts"]["block_size"] = 2


def _called_complete(record):
    for model in (record["subject"]["design"]["model"], record["subject"]["null"]["model"]):
        model["randomisation"] = "complete"
    record["steps"][3]["facts"]["randomisation"] = "complete"
    record["steps"][3]["conclusion"] = record["steps"][3]["conclusion"].replace(
        "blocked", "complete"
    )


@pytest.mark.parametrize("change", [_strata_off, _blocks_changed, _called_complete])
def test_the_checker_rejects_tampered_strata_and_blocks(change):
    arms = (
        'let arms = assignment(n_control=20, n_treatment=20, randomisation="blocked", '
        f"block_size=4, {SITES})\n"
    )
    record = derivation(compiled(arms + STUDY + TEST))
    assert check_derivation(record) == []
    assert check_derivation(tamper(record, change)) != []


def test_the_grouped_proof_lists_every_group():
    test = RandomisationTest(
        40,
        20,
        Fraction(1, 20),
        "participant",
        "two_arm_continuous",
        20,
        20,
        "blocked",
        block_size=4,
    )
    proof = render_randomisation_proof(test, "b" * 64)
    assert "def groups : Randomisation.Groups := [" + ", ".join(["(4, 2)"] * 10) + "]" in proof
    assert f"card = {6**10}" in proof and "groupedTypeI_of_level" in proof


def test_the_stratified_example_compiles():
    path = ROOT / "examples/stratified_randomisation.stat"
    compilation = compile_source(Source(path.read_text(), str(path)))
    assert compilation.status == "elaborated"
    assert [check_derivation(d.to_dict()) for d in compilation.derivations] == [[], []]


DRAWN = TEST.replace("alpha=1/20)", "alpha=1/20, draws={draws})")


def test_drawn_assignments_give_a_checked_monte_carlo_derivation():
    compilation = compiled(ARMS + STUDY + DRAWN.format(draws=9999) + "verify typeI(analysis)\n")
    assert not compilation.diagnostics
    record = derivation(compilation)
    assert check_derivation(record) == []
    assert [step["rule"] for step in record["steps"]][4] == "can-reject-drawn"
    assert record["steps"][4]["facts"]["smallest"] == "1/10000"
    assert record["subject"]["draws"] == 9999
    (claim,) = inspect_program(compilation)
    ids = [item["id"] for item in claim["identified_assumptions"]]
    assert "analysed_with_draws" in ids and "analysed_as_randomised" not in ids
    test = compilation.program.bindings[-1].value.lower()
    assert test.smallest_p_value == Fraction(1, 10000)


def test_draws_work_with_strata_and_with_few_splits():
    blocked = (
        "let arms = assignment(n_control=20, n_treatment=20, "
        'randomisation="blocked", block_size=4)\n'
    )
    assert not compiled(blocked + STUDY + DRAWN.format(draws=999)).diagnostics
    # Two clusters per arm give 6 splits; drawn assignments can still reach 1/20.
    clinics = CLINICS.format(c=2) + STUDY + DRAWN.format(draws=999)
    compilation = compiled(clinics)
    assert not compilation.diagnostics
    assert check_derivation(derivation(compilation)) == []


@pytest.mark.parametrize("draws,code", [(18, "never_rejects"), (0, "domain"), (19, None)])
def test_too_few_draws_to_reach_the_level_are_refused(draws, code):
    found = [c for c, _ in diagnostics(ARMS + STUDY + DRAWN.format(draws=draws))]
    assert found == ([code] if code else [])


def _more_draws(record):
    record["subject"]["draws"] = 99
    record["steps"][4]["facts"].update(draws=99, smallest="1/100")


def _counted_exactly(record):
    del record["subject"]["draws"]


def _exact_rule(record):
    record["steps"][4]["rule"] = "can-reject"


def _exact_assumption(record):
    record["assumptions"][2] = record["assumptions"][2].split(";")[0] + (
        "; the p-value counts every split, not a random sample of splits."
    )


@pytest.mark.parametrize("change", [_more_draws, _counted_exactly, _exact_rule, _exact_assumption])
def test_the_checker_rejects_tampered_monte_carlo_derivations(change):
    record = derivation(compiled(ARMS + STUDY + DRAWN.format(draws=9999)))
    assert check_derivation(record) == []
    assert check_derivation(tamper(record, change)) != []


def test_drawn_proofs():
    test = RandomisationTest(
        40, 20, Fraction(1, 20), "participant", "two_arm_continuous", 20, 20, draws=9999
    )
    proof = render_randomisation_proof(test, "c" * 64)
    assert "def draws : ℕ := 9999" in proof
    assert "Randomisation.drawnRejection_le_of_level" in proof
    assert "MeasureTheory.Measure.pi (fun _ : Fin (draws + 1)" in proof
    with pytest.raises(ValueError):
        RandomisationTest(40, 20, Fraction(1, 20), "participant", "x", 20, 20, draws=0)


FAMILY_USES = "use multiplicity.bonferroni\nuse multiplicity.fixed_sequence\n"
FAMILY_USES += "use designs.group_sequential\nuse multiplicity.graphical\n"
MEMBERS = (
    ARMS
    + STUDY
    + "let response = two_arm(assignment=arms, outcome=binary_outcome())\n"
    + "let primary = randomisation_test(design=fixed(model=study), null=no_effect(model=study), "
    "alpha={alpha}, draws=9999)\n" + "let secondary = fisher(design=fixed(model=response), "
    "null=equal_proportions(model=response), alpha={alpha})\n"
)


@pytest.mark.parametrize(
    "combination,alpha",
    [
        ("bonferroni(analyses=[primary, secondary], alpha=1/20)", "1/40"),
        ("fixed_sequence(analyses=[primary, secondary], alpha=1/20)", "1/20"),
        (
            "graphical(analyses=[primary, secondary], weights=[1, 0], "
            "transitions=[[0, 1], [1, 0]], alpha=1/20)",
            "1/20",
        ),
    ],
)
def test_a_randomisation_test_can_join_families_sequences_and_graphs(combination, alpha):
    text = MEMBERS.format(alpha=alpha) + f"let family = {combination}\nverify familywise(family)\n"
    compilation = compile_source(Source(USES + FAMILY_USES + text, "study.stat"))
    assert not compilation.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in compilation.derivations)
    record = next(d for d in compilation.derivations if d.name == "family").to_dict()
    member = next(m for m in record["guarantee"]["members"] if m["name"] == "primary")
    assert member["grade"] == "proved"
    assert member["basis"] == "tests.randomisation/randomisation_test"
    # Its steps sit inside the family's derivation, so a change to its design is caught.
    altered = copy.deepcopy(record)
    del altered["subject"]["analyses"][0]["analysis"]["design"]["model"]["randomisation"]
    assert check_derivation(altered) != []


def test_a_randomisation_test_cannot_be_a_look():
    text = (
        MEMBERS.format(alpha="1/40")
        + "let late = randomisation_test(design=fixed(model=study), null=no_effect(model=study), "
        "alpha=1/40, draws=9999)\n"
        + "let looks = alpha_spending(looks=[primary, late], alpha=1/20)\n"
    )
    (diagnostic, *_) = compile_source(Source(USES + FAMILY_USES + text, "s.stat")).diagnostics
    assert diagnostic.code == "type" and "cannot be a look" in diagnostic.message
