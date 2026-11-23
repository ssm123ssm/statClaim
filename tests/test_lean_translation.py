"""The Lean translation covers the whole language. See docs/proposals/lean-translation.md."""

from pathlib import Path

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
