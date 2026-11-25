"""The Lean semantics classifies the whole language. See docs/proposals/lean-translation.md."""

import importlib.util
from pathlib import Path

from statclaim.language import MODULES, OPERATION_BACKENDS, OPERATIONS
from statclaim.lean_translation.table import PLANNED, ROLES, TABLE, InLean, NotInLean, summary
from statclaim.methods import METHODS, OBSERVATIONAL

ROOT = Path(__file__).resolve().parents[1]
CONSTRUCTORS = {c.name: c for module in MODULES.values() for c in module.constructors}


def test_every_constructor_and_operation_is_classified():
    names = set(CONSTRUCTORS) | set(OPERATIONS)
    assert set(TABLE) == names
    missing = sorted(name for name, entry in TABLE.items() if entry is None)
    assert missing == [], "Give these constructors lean=... where the registry defines them."
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


def test_every_python_rejection_has_an_expected_lean_outcome():
    from statclaim.lean_translation.rejection import OUTCOMES

    path = ROOT / "scripts/check_lean_rejections.py"
    spec = importlib.util.spec_from_file_location("check_lean_rejections", path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    asked = checker.asked_all()
    assert asked.keys() == checker.EXPECTED.keys()
    for key, item in asked.items():
        expected, reason = checker.EXPECTED[key]
        assert expected in OUTCOMES and item.refused, key
        assert (expected == "accepted") == bool(reason), key
        assert bool(item.semantic) == (expected not in ("uncovered", "untyped")), key
        if expected == "refuted":
            assert "Program.refuted program" in item.semantic, key


def test_deferred_contracts_remain_errors_outside_the_rejection_check():
    from statclaim.language_compiler import compile_source
    from statclaim.language_syntax import Source
    from statclaim.lean_translation.rejection import ask

    source = Source((ROOT / "examples/hypothesis_mismatch.stat").read_text(), "mismatch.stat")
    asked = ask(source, "mismatch")
    assert [d.code for d in asked.deferred] == ["hypothesis_mismatch"]
    assert "theorem contracts : program.Contracts" in asked.semantic
    compiled = compile_source(source)
    assert compiled.status == "invalid"
    assert [d.code for d in compiled.diagnostics] == ["hypothesis_mismatch"]
