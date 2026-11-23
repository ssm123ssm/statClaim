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
        assert set(result.claims.values()) <= {"proved", "cited", "declared"}, path
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
    assert "supplies no sampling law" in adaptive.skipped["verification"]


@pytest.mark.lean
def test_lean_rejects_a_translation_that_breaks_a_contract_or_overstates_a_claim(tmp_path):
    import subprocess

    text = corpus_checker().translation(ROOT / "examples/t_test.stat").lean
    welch = "(plan_compatible i) (margin i) i.welch_test"
    mutations = {
        "too few participants": ("t_test.minTotal ≤ 60 + 60", "t_test.minTotal ≤ 1 + 1"),
        "an unsupported null": (
            "NullKey.equal_means ∈ StatClaim.Generated.Methods.t_test.nulls",
            "NullKey.mean_difference_at_least ∈ StatClaim.Generated.Methods.t_test.nulls",
        ),
        "a large-sample claim stated at the level": (
            f"{welch} ((↑((1 : ℚ) / 40) : ℝ) + i.welch_slack) :=\n"
            "  StatClaim.Interface.typeI_of_premise (plan_compatible i) premises.welch_level",
            f"{welch} (↑((1 : ℚ) / 40) : ℝ) :=\n"
            "  StatClaim.Interface.typeI_of_finite_premise (plan_compatible i) rfl "
            "premises.welch_level",
        ),
    }
    survey = corpus_checker().translation(ROOT / "examples/complex_survey.stat").lean
    cases = [(text, label, change) for label, change in mutations.items()]
    cases.append(
        (
            survey,
            "a design the method does not fit",
            ("ObservationalDesign.cross_sectional", "ObservationalDesign.case_control"),
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
