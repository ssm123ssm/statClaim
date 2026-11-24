"""The Lean translation covers the whole language. See docs/proposals/lean-translation.md."""

import importlib.util
from pathlib import Path

import pytest

from statclaim.language import MODULES, OPERATION_BACKENDS, OPERATIONS
from statclaim.lean_translation.table import PLANNED, ROLES, TABLE, InLean, NotInLean, summary
from statclaim.methods import METHODS, OBSERVATIONAL

ROOT = Path(__file__).resolve().parents[1]
CONSTRUCTORS = {c.name: c for module in MODULES.values() for c in module.constructors}


def test_every_constructor_and_operation_is_classified():
    names = set(CONSTRUCTORS) | set(OPERATIONS)
    assert sorted(names - set(TABLE)) == [], "Add these to lean_translation/table.py."
    assert sorted(set(TABLE) - names) == [], "These are no longer in the language."
    assert sum(summary().values()) == len(TABLE)


def test_entries_are_well_formed():
    for name, entry in TABLE.items():
        if isinstance(entry, InLean):
            assert entry.role in ROLES, name
            assert entry.lean and len(set(entry.lean)) == len(entry.lean), name
        else:
            assert isinstance(entry, NotInLean) and entry.reason.endswith("."), name


def test_named_lean_files_exist_or_are_planned():
    for name, entry in TABLE.items():
        for path in entry.lean if isinstance(entry, InLean) else ():
            assert (ROOT / path).is_file() or path in PLANNED, (name, path)
    built = [path for path in PLANNED if (ROOT / path).exists()]
    assert built == [], "These exist now; remove them from PLANNED."


def test_every_lean_module_gives_meaning_to_some_constructor():
    named = {path for entry in TABLE.values() if isinstance(entry, InLean) for path in entry.lean}
    modules = {p.relative_to(ROOT).as_posix() for p in (ROOT / "StatClaim/Modules").glob("*.lean")}
    assert sorted(modules - named) == []


def test_cited_and_declared_tests_are_premises():
    for name, constructor in CONSTRUCTORS.items():
        entry = TABLE[name]
        premise = isinstance(entry, InLean) and entry.role == "premise"
        assert premise == (constructor.result in ("CitedAnalysis", "CitedAssociation")), name
    for key in (*METHODS, *OBSERVATIONAL):
        entry = TABLE[key]
        assert isinstance(entry, InLean) and "StatClaim/Generated/Methods.lean" in entry.lean


def test_only_operations_that_build_proofs_are_in_lean():
    for name, backend in OPERATION_BACKENDS.items():
        assert isinstance(TABLE[name], InLean) == (backend == "lean"), name


def test_generated_method_premises_are_current():
    """StatClaim/Generated/Methods.lean is the method registry, regenerated."""
    path = ROOT / "scripts/update_lean_premises.py"
    spec = importlib.util.spec_from_file_location("update_lean_premises", path)
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    assert (ROOT / "StatClaim/Generated/Methods.lean").read_text() == generator.render(), (
        "Run uv run python scripts/update_lean_premises.py."
    )


def corpus_checker():
    path = ROOT / "scripts/check_lean_translation.py"
    spec = importlib.util.spec_from_file_location("check_lean_translation", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_every_accepted_program_translates_and_says_what_it_leaves_out():
    checker = corpus_checker()
    translated = claims = 0
    for path in checker.corpus():
        result = checker.translation(path)
        if result is None:
            continue
        translated += 1
        claims += len(result.claims)
        assert all(reason.endswith(".") for reason in result.skipped.values()), path
        assert set(result.claims.values()) <= {"proved", "conditional", "cited", "declared"}, path
    assert translated >= 100 and claims >= 30


def test_pinned_translations_are_current():
    checker = corpus_checker()
    for path in checker.PINNED:
        result = checker.translation(ROOT / path)
        assert checker.pinned(path).read_text() == result.lean, (
            f"{path}: run scripts/check_lean_translation.py --update and review the diff."
        )


def test_claims_carry_their_grades_and_unresolved_claims_say_why():
    checker = corpus_checker()
    grades = {
        path: checker.translation(ROOT / path).claims
        for path in ("examples/paper/fisher_design.stat", "examples/t_test.stat")
    }
    assert grades["examples/paper/fisher_design.stat"] == {"verification_claim": "proved"}
    assert grades["examples/t_test.stat"] == {
        "checked_claim": "cited",
        "approximate_claim": "cited",
    }
    declared = checker.translation(ROOT / "examples/declared_test.stat")
    assert "declared" in declared.claims.values()
    survey = checker.translation(ROOT / "examples/complex_survey.stat")
    assert survey.claims == {"checked_claim": "cited"} and survey.skipped == {}
    adaptive = checker.translation(ROOT / "examples/paper/fisher_adaptive.stat")
    assert adaptive.claims == {}
    assert "needs a justified sampling law" in adaptive.skipped["verification"]
    family = checker.translation(ROOT / "examples/mixed_endpoints.stat")
    assert family.claims == {"family_claim": "conditional", "primary_claim": "proved"}
    assert family.skipped == {}
    assert checker.translation(ROOT / "examples/two_outcomes.stat").claims == {
        "request_1_claim": "proved"
    }
    sequence = checker.translation(ROOT / "examples/trial_models.stat")
    assert sequence.claims["overall_claim"] == "conditional"
    assert "sequenceClaim" in sequence.lean
    looks = checker.translation(ROOT / "replication/comparison/sequential.stat")
    assert looks.claims == {"error_claim": "conditional"} and looks.skipped == {}
    # A graph rests on its own cited premise; a hierarchy that nests it is conditional.
    copd = checker.translation(ROOT / "replication/copd/design_cited.stat")
    assert copd.claims == {
        "primary_error_claim": "cited",
        "overall_error_claim": "conditional",
        "onset_error_claim": "cited",
    }
    assert copd.owns["primary_error_claim"] == "cited_graph_rule" and copd.skipped == {}
    assert "inspiratory_capacity_ni_test" in copd.lean  # one declaration, one test
    trial = checker.translation(ROOT / "examples/confirmatory_trial.stat")
    assert trial.claims["overall_claim"] == "conditional"  # looks nested in a sequence
    # Exact tests are proved by their modules, with their numerical checks in Lean.
    exact = {
        "examples/one_sided.stat": {
            "guarantee_claim": "proved",
            "sizing_claim": "proved",
            "outcome_claim": "proved",
        },
        "examples/non_inferiority.stat": {"guarantee_claim": "proved", "outcome_claim": "proved"},
        "examples/case_control.stat": {"checked_claim": "proved", "odds_claim": "proved"},
        "examples/cross_sectional.stat": {
            "survey_checked_claim": "proved",
            "cohort_checked_claim": "proved",
            "prevalence_claim": "proved",
        },
        "examples/randomisation.stat": {"individual_claim": "proved", "by_clinic_claim": "proved"},
        "examples/incidence_rates.stat": {
            "design_claim_claim": "proved",
            "result_claim": "proved",
            "ratio_claim": "proved",
        },
        "examples/tutorial/25_matched_pairs.stat": {
            "design_claim_claim": "proved",
            "tested_claim": "proved",
            "odds_claim": "proved",
        },
    }
    for path, claims in exact.items():
        assert checker.translation(ROOT / path).claims == claims, path
    # A test of association with fixed groups is Fisher's test on two binomial counts.
    assert (
        "Fisher.analysis analysis_groups"
        in checker.translation(ROOT / "examples/case_control.stat").lean
    )
    adaptive_exact = checker.translation(ROOT / "examples/one_sided.stat")
    assert "FisherOneSided.typeI_of_hints" in adaptive_exact.lean
    # Results for observed counts: each part is a theorem the template checks today.
    assert adaptive_exact.claims["outcome_claim"] == "proved"
    result = checker.translation(ROOT / "examples/fisher_result.stat")
    assert result.claims == {"request_2_claim": "proved"}  # calculate requests claim nothing
    assert "StatClaim.hypergeometricPValue 100 100 35 10 =" in result.lean
    # The other results and the intervals, each in its template's parts.
    observed = {
        "examples/cohort.stat": {"result_claim": "proved", "ratio_claim": "proved"},
        "examples/matched_case_control.stat": {"result_claim": "proved", "odds_claim": "proved"},
        "examples/difference_interval.stat": {"verification_claim": "proved"},
        "examples/one_sample_result.stat": {"verification_claim": "proved"},
        "examples/two_stage_result.stat": {"verification_claim": "proved"},
    }
    for path, claims in observed.items():
        assert checker.translation(ROOT / path).claims == claims, path
    # Plans: the design verify would certify, a declared one or the one a search selects.
    plans = checker.translation(ROOT / "examples/observational_power.stat")
    assert plans.claims == {
        "smallest_claim": "proved",
        "fewest_pairs_claim": "proved",
        "rates_power_claim": "proved",
        "survey_power_claim": "proved",
    }
    missed = checker.translation(ROOT / "examples/planning.stat")
    assert missed.claims == {"sizing_verification_claim": "proved"}
    assert "power falls short" in missed.skipped["verification"]


def test_certificates_take_their_statements_from_one_place():
    """The templates of results, intervals and randomisation tests write no claimed theorem
    themselves: each comes from lean_translation/statements.py, as the translator's do."""
    import re

    claimed = re.compile(
        r"theorem checked_(counts|support|p_value|table_probability|decision|interval|"
        r"coverage|tails|interim|critical)\b"
    )
    for name in ("proof", "association", "incidence", "matched", "randomisation", "planning"):
        source = (ROOT / f"src/statclaim/{name}.py").read_text()
        assert not claimed.search(source), name
    # Nor do the planning templates, nor any Type I statement outside the two-sided design
    # and family templates, whose claims the translator states on the program's objects.
    planned = re.compile(r"theorem checked_(typeI|power|smaller|stages|critical|sizes|size)\b")
    for name in ("planning", "observational_planning", "association", "incidence", "matched"):
        source = (ROOT / f"src/statclaim/{name}.py").read_text()
        assert not planned.search(source), name
    source = (ROOT / "src/statclaim/randomisation.py").read_text()
    assert "theorem checked_typeI" not in source


def test_every_exact_claim_is_checked_against_its_template():
    """Results, intervals and plans are proved from their templates' own theorems, which
    shows the two agree; each Type I claim gets an example deriving its template's."""
    checker = corpus_checker()
    accepted = [path for path in checker.corpus() if checker.translation(path) is not None]
    assert sum(checker.exact_claims(path) for path in accepted) == 87
    examples = [text for path in accepted for text in checker.equivalences(path)]
    assert len(examples) == 34
    assert all("type_of% @template_" in text for text in examples)


def test_a_grade_follows_from_the_premises_a_proof_uses():
    from statclaim.lean_translation.grades import grade

    own_cited, own_declared = "cited_test_level", "declared_test_level"
    assert grade(None, []) == "proved"
    assert grade(own_cited, [own_cited]) == "cited"
    assert grade(own_declared, [own_declared]) == "declared"
    # A combination resting on its members' premises is conditional, whichever kind.
    assert grade(None, ["cited_first_level"]) == "conditional"
    assert grade(None, ["declared_first_level", "cited_second_level"]) == "conditional"
    # A claim whose proof uses no cited or declared premise is proved, even if it has one.
    assert grade(own_cited, []) == "proved"
    # Its own premise decides, even beside members' premises.
    assert grade(own_cited, [own_cited, "declared_other_level"]) == "cited"


def test_the_checker_reports_a_grade_the_proof_does_not_support():
    checker = corpus_checker()
    path = ROOT / "examples/two_outcomes.stat"
    result = checker.translation(path)
    name = checker.label(path)
    honest = f"STATCLAIM_PREMISES {name} request_1_claim: \n"
    assert checker.grade_problems({name: (path, result)}, honest) == []
    # A proof of the proved family that used a cited premise would be conditional.
    overstated = f"STATCLAIM_PREMISES {name} request_1_claim: cited_other_level\n"
    assert checker.grade_problems({name: (path, result)}, overstated)
    assert checker.grade_problems({name: (path, result)}, "")  # no premises listed


@pytest.mark.lean
def test_lean_rejects_a_translation_that_breaks_a_contract_or_overstates_a_claim(tmp_path):
    import subprocess

    text = corpus_checker().translation(ROOT / "examples/t_test.stat").lean
    welch = "(plan_compatible i) (margin i) i.welch_test"
    premise = "premises.cited_welch_level"
    mutations = {
        "too few participants": ("t_test.minTotal ≤ 60 + 60", "t_test.minTotal ≤ 1 + 1"),
        "an unsupported null": (
            "NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls",
            "NullKey.mean_difference_at_least ∈ StatClaim.Generated.Methods.t_test.nulls",
        ),
        "a large-sample claim stated at the level": (
            f"{welch} ((↑((1 : ℚ) / 40) : ℝ) + i.welch_slack) :=\n"
            f"  StatClaim.Interface.typeI_of_premise (plan_compatible i) {premise}",
            f"{welch} (↑((1 : ℚ) / 40) : ℝ) :=\n"
            f"  StatClaim.Interface.typeI_of_finite_premise (plan_compatible i) rfl {premise}",
        ),
    }
    survey = corpus_checker().translation(ROOT / "examples/complex_survey.stat").lean
    family = corpus_checker().translation(ROOT / "examples/mixed_endpoints.stat").lean
    cases = [(text, label, change) for label, change in mutations.items()]
    graph = corpus_checker().translation(ROOT / "examples/recycling.stat").lean
    cases.append(
        (
            graph,
            "a graph whose starting weights sum to more than one",
            (
                "((1 : ℚ) / 2) + ((1 : ℚ) / 2) + (0 : ℚ) ≤ 1",
                "((3 : ℚ) / 5) + ((1 : ℚ) / 2) + (0 : ℚ) ≤ 1",
            ),
        )
    )
    randomisation = corpus_checker().translation(ROOT / "examples/randomisation.stat").lean
    cases.append(
        (
            randomisation,
            "a level no randomisation p-value can reach",
            ("(1 : ℚ) / 924 ≤ ((1 : ℚ) / 20)", "(1 : ℚ) / 924 ≤ ((1 : ℚ) / 1000)"),
        )
    )
    cases.append(
        (
            randomisation,
            "a wrong count of possible assignments",
            (
                "(StatClaim.Modules.Randomisation.splits 12 6).card = 924",
                "(StatClaim.Modules.Randomisation.splits 12 6).card = 925",
            ),
        )
    )
    result = corpus_checker().translation(ROOT / "examples/fisher_result.stat").lean
    cases.append(
        (
            result,
            "a misreported p-value",
            # The claim's own statement, after the template's proof material.
            (
                "(19912805355158606332329 : ℚ) / 2341699062001756564467919) ∧",
                "(19912805355158606332328 : ℚ) / 2341699062001756564467919) ∧",
            ),
        )
    )
    cases.append(
        (
            result,
            "a reversed decision",
            ("((1 : ℚ) / 20)) ↔ True)", "((1 : ℚ) / 20)) ↔ False)"),
        )
    )
    plan = corpus_checker().translation(ROOT / "examples/paper/simon_design.stat").lean
    power = "StatClaim.ratPoint 1 4 (by decide) (by decide))\n      "
    cases.append(
        (
            plan,
            "a plan claiming more power than its design has",
            (
                f"{power}(((9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)))",
                f"{power}(((99 : ℕ) : ℝ) / ((100 : ℕ) : ℝ)))",
            ),
        )
    )
    cases.append(
        (
            plan,
            "a plan whose stated design is not the one checked",
            (
                "StatClaim.Modules.TwoStageBinomial.thresholdDesign 9 15 0 2",
                "StatClaim.Modules.TwoStageBinomial.thresholdDesign 9 15 0 1",
            ),
        )
    )
    interval = corpus_checker().translation(ROOT / "examples/difference_interval.stat").lean
    cases.append(
        (
            interval,
            "an interval narrower than its data allow",
            (
                "((6443 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - ((1189",
                "((6000 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) - ((1189",
            ),
        )
    )
    margin = corpus_checker().translation(ROOT / "examples/non_inferiority.stat").lean
    cases.append(
        (
            margin,
            "a margin test that rejects more often than its level allows",
            (
                "analysis_thresholds : List ℕ := [0, 0, 2, 3,",
                "analysis_thresholds : List ℕ := [0, 0, 0, 0,",
            ),
        )
    )
    sequence = corpus_checker().translation(ROOT / "examples/trial_models.stat").lean
    cases.append(
        (
            sequence,
            "a fixed sequence claimed below its members' level",
            (
                "((↑((1 : ℚ) / 40) : ℝ) + ∑ k, ![i.lung_function_slack",
                "((↑((1 : ℚ) / 80) : ℝ) + ∑ k, ![i.lung_function_slack",
            ),
        )
    )
    cases.append(
        (
            family,
            "a family claimed at less than its members' levels sum to",
            ("((↑((1 : ℚ) / 20) : ℝ) + ∑ k", "((↑((1 : ℚ) / 40) : ℝ) + ∑ k"),
        )
    )
    cases.append(
        (
            survey,
            "a design the method does not fit",
            ("ObservationalDesign.cross_sectional", "ObservationalDesign.case_control"),
        )
    )
    # One false number per exact module that a run proves, in the claim's own statement.
    matched = corpus_checker().translation(ROOT / "examples/matched_case_control.stat").lean
    cases.append(
        (
            matched,
            "a reversed McNemar decision",
            (
                "220 (analysis_level.value : ℝ)) ↔ False) :=",
                "220 (analysis_level.value : ℝ)) ↔ True) :=",
            ),
        )
    )
    rates = corpus_checker().translation(ROOT / "examples/incidence_rates.stat").lean
    cases.append(
        (
            rates,
            "a reversed rate-test decision",
            ("(test_level.value : ℝ))) ↔ False) :=", "(test_level.value : ℝ))) ↔ True) :="),
        )
    )
    blocks = corpus_checker().translation(ROOT / "examples/stratified_randomisation.stat").lean
    cases.append(
        (
            blocks,
            "a wrong count of assignments by blocks",
            ("]).card = 2176782336", "]).card = 2176782337"),
        )
    )
    for source, label, (old, new) in cases:
        assert old in source, label
        lean_file = tmp_path / "Mutated.lean"
        lean_file.write_text(
            f"import StatClaim\nnamespace Mutated\n{source.replace(old, new, 1)}end Mutated\n"
        )
        run = subprocess.run(["lake", "env", "lean", str(lean_file)], cwd=ROOT, capture_output=True)
        assert run.returncode != 0, f"Lean accepted {label}"


def rejection_checker():
    path = ROOT / "scripts/check_lean_rejections.py"
    spec = importlib.util.spec_from_file_location("check_lean_rejections", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_every_program_python_refuses_has_an_expected_lean_outcome():
    """Test 3: each injected error and each refused corpus program says what Lean does."""
    from statclaim.lean_translation.rejection import OUTCOMES

    checker = rejection_checker()
    asked = checker.asked_all()
    assert sorted(asked) == sorted(checker.EXPECTED)
    for key, item in asked.items():
        expected, reason = checker.EXPECTED[key]
        assert expected in OUTCOMES, key
        assert (expected == "accepted") == bool(reason), key
        # Only a program with no typed form stays out of Lean.
        assert (item.denotation is None) == (expected == "untyped"), key
        assert item.refused, key
        if expected == "refuted":
            assert item.denotation.refuted and "Lean proves it has none" in " ".join(
                item.denotation.skipped.values()
            ), key


def test_deferred_checks_stay_deferred_only_while_asked():
    from statclaim.language_compiler import compile_source
    from statclaim.language_syntax import Source
    from statclaim.lean_translation.rejection import ask

    source = Source((ROOT / "examples/hypothesis_mismatch.stat").read_text(), "mismatch.stat")
    asked = ask(source, "mismatch")
    assert [d.code for d in asked.deferred] == ["hypothesis_mismatch"]
    assert asked.denotation is not None and "analysis_null" in asked.lean
    # Outside ask(), the same program is rejected as before.
    compilation = compile_source(source)
    assert compilation.status == "invalid"
    assert [d.code for d in compilation.diagnostics] == ["hypothesis_mismatch"]


def test_a_design_without_a_sampling_law_is_refuted_in_lean():
    checker = corpus_checker()
    adaptive = checker.translation(ROOT / "examples/paper/fisher_adaptive.stat")
    assert "theorem design_no_law :" in adaptive.lean
    assert "StatClaim.Core.no_compatibility_without_law" in adaptive.lean


# Every kind of claim `verify` certifies, as language_runner dispatches them.
VERIFIED_SUBJECTS = {
    "AnalysisIR",
    "AssociationAnalysisIR",
    "AssociationResultIR",
    "CitedAnalysisIR",
    "CitedAssociationIR",
    "ComposedFamilyIR",
    "DifferenceIntervalIR",
    "EffectIntervalIR",
    "FamilyIR",
    "FeasibilityIR",
    "IntervalIR",
    "MatchedAnalysisIR",
    "MatchedIntervalIR",
    "MatchedResultIR",
    "ObservationIR",
    "OneSampleObservationIR",
    "ProportionIR",
    "RandomisationAnalysisIR",
    "RateAnalysisIR",
    "RateRatioIR",
    "RateResultIR",
    "SequentialIR",
    "SizingIR",
    "TwoStageObservationIR",
}
# Why a verified claim may stay out of Lean: Python's open requirement, a design Lean
# proves has no sampling law, or a plan that misses its target.
REFUSALS = ("needs a justified sampling law", "exceeds the requested", "falls short of")


def test_every_kind_of_verified_claim_translates_unless_refused():
    checker = corpus_checker()
    kinds = set()
    for path in checker.corpus():
        program = checker.compiled(path)
        if program is None:
            continue
        result = checker.translation(path)
        stated = set(result.requests.values())
        holders = {
            b.value.request_id: b.name
            for b in program.bindings
            if type(b.value).__name__ == "VerificationResultIR"
        }
        for index, request in enumerate(program.requests, 1):
            if request.operation != "verify":
                continue
            kinds.add(type(request.claim.subject).__name__)
            if index in stated:
                continue
            reason = result.skipped[holders.get(index, f"request_{index}")]
            assert any(words in reason for words in REFUSALS), (path, reason)
    assert kinds == VERIFIED_SUBJECTS, "Add a corpus example of each kind of verified claim."
