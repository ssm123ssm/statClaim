"""Catalogue must follow language registries, including newly added modules."""

import json

import pytest

from statclaim.catalogue import catalogue, render_catalogue
from statclaim.cli import main
from statclaim.language import MODULES, OPERATIONS, Module
from statclaim.language_fields import SCHEMAS


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
