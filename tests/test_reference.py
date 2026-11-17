"""The generated reference is complete: codes, grammar, values and signatures."""

import ast
import json
from pathlib import Path

import pytest

from statclaim.catalogue import catalogue, render_catalogue
from statclaim.cli import main
from statclaim.language import MODULES, elaborate
from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source, parse
from statclaim.language_values import STATUS_GRADES
from statclaim.methods import ASSUMPTIONS, METHODS
from statclaim.methods.core import GRADES
from statclaim.reference import (
    DIAGNOSTICS,
    ENUMERATIONS,
    GRAMMAR_ACCEPTS,
    GRAMMAR_REJECTS,
    PROGRAM_STATUSES,
    RESULT_STATUSES,
)

ROOT = Path(__file__).resolve().parents[1]


def codes_in_source() -> set[str]:
    """Every diagnostic code written as a literal anywhere in the package."""
    found = set()
    for path in sorted((ROOT / "src/statclaim").rglob("*.py")):
        if path.name == "reference.py":
            continue
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Call):
                name = getattr(node.func, "id", getattr(node.func, "attr", None))
                first = node.args[0] if node.args else None
                if (
                    name in ("fail", "Diagnostic")
                    and isinstance(first, ast.Constant)
                    and isinstance(first.value, str)
                ):
                    found.add(first.value)
                if name == "_unmet" and len(node.args) >= 3:
                    found.add(node.args[2].value)
                found |= {
                    k.value.value
                    for k in node.keywords
                    if k.arg == "code" and isinstance(k.value, ast.Constant)
                }
    return found


def test_every_diagnostic_code_is_documented_and_none_is_stale():
    used = codes_in_source() | {"verification"}
    assert used == set(DIAGNOSTICS), (
        "Add new codes to reference.DIAGNOSTICS and remove unused ones: "
        f"undocumented {sorted(used - set(DIAGNOSTICS))}, stale {sorted(set(DIAGNOSTICS) - used)}"
    )
    assert {severity for severity, _ in DIAGNOSTICS.values()} == set(
        ENUMERATIONS["Diagnostic.severity"]
    )


@pytest.mark.parametrize("text", GRAMMAR_ACCEPTS)
def test_grammar_examples_parse(text):
    statements, errors = parse(Source(text + "\n"))
    assert errors == [] and statements


@pytest.mark.parametrize("text", GRAMMAR_REJECTS)
def test_text_outside_the_grammar_is_rejected(text):
    _, diagnostics = elaborate(Source(text + "\n"))
    assert diagnostics and diagnostics[0].severity == "error"


def test_statuses_and_grades_cover_what_the_code_can_produce():
    assert set(STATUS_GRADES) <= set(RESULT_STATUSES)
    assert set(STATUS_GRADES.values()) <= set(GRADES)
    assert set(STATUS_GRADES) <= set(PROGRAM_STATUSES)
    # Statuses the compiler itself can give.
    for path, expected in (
        ("fisher.stat", "elaborated"),
        ("overallocated.stat", "unresolved_obligation"),
    ):
        status = compile_source(Source((ROOT / "examples" / path).read_text())).status
        assert status == expected and status in PROGRAM_STATUSES
    assert compile_source(Source("let x = \n")).status == "invalid"


def test_reference_lists_every_constructor_method_and_assumption():
    data = catalogue()
    text = render_catalogue()
    for module in MODULES.values():
        for constructor in module.constructors:
            assert f"- `{constructor.name}(" in text
    typed = {c["name"]: c for m in data["modules"] for c in m["constructors"]}
    assert typed["bonferroni"]["optional"] == ["joint_law"]
    assert "joint_law?: string" in typed["bonferroni"]["typed_signature"]
    assert {m["key"] for m in data["cited_methods"]} == set(METHODS)
    assert {a["id"] for a in data["assumptions"]} == set(ASSUMPTIONS)
    for method in data["cited_methods"]:
        assert set(method["assumptions"]) <= set(ASSUMPTIONS) and method["references"]
    for heading in (
        "## Grammar",
        "## Value types",
        "## Statuses and other fixed values",
        "## Cited methods",
        "## Assumptions",
        "## Limits",
        "## Diagnostic codes",
    ):
        assert heading in text


def test_json_catalogue_carries_the_same_reference(capsys):
    assert main(["catalogue", "--json"]) == 0
    data = json.loads(capsys.readouterr().out)
    assert data["diagnostics"]["hypothesis_mismatch"]["severity"] == "error"
    assert data["result_statuses"].keys() >= {"verified", "conditional", "cited"}
    assert "2 to 20" in data["limits"].values()
