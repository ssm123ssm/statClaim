"""Catalogue must follow language registries, including newly added modules."""

import json

import pytest

from statclaim.catalogue import catalogue, render_catalogue
from statclaim.cli import main
from statclaim.language import MODULES, OPERATIONS, Module
from statclaim.language_compiler import compile_source
from statclaim.language_fields import SCHEMAS
from statclaim.language_syntax import Source
from statclaim.reference import PARAMETER_CHOICES


def test_inventory_includes_every_constructor_and_public_schema():
    data = catalogue()
    assert {m["name"] for m in data["modules"]} == set(MODULES)
    assert {o["name"] for o in data["operations"]} == set(OPERATIONS)
    assert sum(len(m["constructors"]) for m in data["modules"]) == sum(
        len(m.constructors) for m in MODULES.values()
    )
    assert all(o["fields"] for o in data["objects"])
    fisher = next(m for m in data["modules"] if m["name"] == "tests.fisher")
    contract = next(c for c in fisher["constructors"] if c["name"] == "fisher")["contract"]
    assert contract["supported_predicates"] == ["equal_proportions"]
    assert "Option[Evidence]" in render_catalogue()


def test_unclassified_new_module_fails(monkeypatch):
    monkeypatch.setitem(MODULES, "new.module", Module("new.module", ()))
    with pytest.raises(ValueError, match="Classify every module"):
        catalogue()


def test_unclassified_field_bearing_type_fails(monkeypatch):
    class NewObject:
        pass

    monkeypatch.setitem(SCHEMAS, NewObject, {})
    with pytest.raises(ValueError, match="Classify every public object"):
        catalogue()


def test_cli_catalogue_json_is_pure(capsys, monkeypatch):
    def no_execution(*args, **kwargs):
        pytest.fail("Catalogue must not execute subprocesses")

    monkeypatch.setattr("subprocess.run", no_execution)
    assert main(["catalogue", "--json"]) == 0
    assert len(json.loads(capsys.readouterr().out)["modules"]) == len(MODULES)
    assert main(["catalog"]) == 0
    assert "# Language reference and catalogue" in capsys.readouterr().out


def test_every_string_input_has_fixed_choices_or_free_text():
    free_text = {"name", "method", "reference"}
    strings = {
        parameter
        for module in catalogue()["modules"]
        for constructor in module["constructors"]
        for parameter, kind in constructor["parameters"].items()
        if kind == "string"
    }
    assert strings - free_text == set(PARAMETER_CHOICES)
    two_arm = next(m for m in catalogue()["modules"] if m["name"] == "models.two_arm_binomial")
    entry = next(c for c in two_arm["constructors"] if c["name"] == "two_arm_binomial")
    assert entry["choices"] == {
        "better": ["higher", "lower"],
        "population": list(PARAMETER_CHOICES["population"]),
    }


def _compiles(text):
    return compile_source(Source(text)).status != "invalid"


@pytest.mark.parametrize("model", ["binomial", "continuous", "survival"])
def test_listed_model_choices_compile(model):
    for value in PARAMETER_CHOICES["better"]:
        call = f'two_arm_{model}(n_control=10, n_treatment=10, better="{value}")'
        assert _compiles(f"use models.two_arm_{model}\nlet m = {call}\n")
    for value in PARAMETER_CHOICES["population"]:
        call = f'two_arm_{model}(n_control=10, n_treatment=10, population="{value}")'
        assert _compiles(f"use models.two_arm_{model}\nlet m = {call}\n")
    assert not _compiles(
        f"use models.two_arm_{model}\nlet m = two_arm_{model}(n_control=10, n_treatment=10, "
        'better="sideways")\n'
    )


def test_listed_search_and_declared_choices_compile():
    for value in PARAMETER_CHOICES["criterion"]:
        call = f'two_stage_designs(null_rate=1/5, max_total=45, criterion="{value}")'
        assert _compiles(f"use designs.two_stage\nlet c = {call}\n")
    for value in PARAMETER_CHOICES["scope"]:
        text = (
            "use models.two_arm_continuous\nuse sampling\nuse tests.declared\n"
            "let m = two_arm_continuous(n_control=10, n_treatment=10)\n"
            "let a = declared_test(design=fixed(model=m), null=equal_means(model=m), "
            f'alpha=1/20, method="Our test", scope="{value}")\n'
        )
        assert _compiles(text)
