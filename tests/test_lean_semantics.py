"""The program as Lean data, and the check that it is the canonical program. See
docs/proposals/lean-semantics.md."""

import copy
import importlib.util
import json
import math
import re
import shutil
import subprocess
from pathlib import Path

import pytest

from statclaim.language_compiler import compile_source
from statclaim.lean_translation.certificate import Source
from statclaim.lean_translation.data import (
    CANONICAL,
    MARKER,
    Outside,
    binding_problem,
    declarations,
    program_data,
    report,
    same_json,
    verify_claims,
)

ROOT = Path(__file__).resolve().parents[1]


def canonical(path: str) -> dict:
    return compile_source(Source((ROOT / path).read_text(), path)).program.to_dict()


def semantics_checker():
    path = ROOT / "scripts/check_lean_semantics.py"
    spec = importlib.util.spec_from_file_location("check_lean_semantics", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_every_program_is_written_as_data_or_says_why_not():
    found, outside = semantics_checker().covered()
    assert {"examples/mixed_endpoints.stat", "replication/copd/design_cited.stat"} <= set(found)
    assert all(reason.endswith(".") for reason in outside)
    for _, program, data in found.values():
        assert data.startswith("def program : StatClaim.Semantics.Program")
        requests = re.findall(
            r"^  \.(typeI|familywise|result|checkedResult|interval|planned) ", data, re.MULTILINE
        )
        assert len(requests) == len(verify_claims(program))


def test_frozen_claims_have_pinned_sources():
    checker = semantics_checker()
    frozen = checker.fixtures()
    assert len(frozen) >= 80
    for name, (text, statement) in frozen.items():
        assert "Old.Claims i ↔" in statement
        assert compile_source(Source(text, name)).status != "invalid"


def test_reference_statements_cover_every_request_and_test_constructor():
    syntax = (ROOT / "StatClaim/Semantics/Syntax.lean").read_text()
    reference = (ROOT / "tests/lean/SemanticsReference.lean").read_text()
    for type_name in ("Request", "Test"):
        body = syntax.split(f"inductive {type_name} where\n", 1)[1].split("\n\n", 1)[0]
        constructors = re.findall(r"^  \| (\w+)", body, flags=re.M)
        assert constructors
        missing = [
            name
            for name in constructors
            if not re.search(rf"\b{type_name}\.{name}\b", reference)
            and not re.search(rf"\(\.{name} ", reference)
        ]
        assert not missing, (type_name, missing)


def test_the_writer_refuses_what_it_does_not_read():
    program = canonical("examples/mixed_endpoints.stat")
    family = verify_claims(program)[0]["subject"]

    def changed(change) -> dict:
        copied = copy.deepcopy(program)
        change(verify_claims(copied)[0]["subject"])
        return copied

    def one_sided(subject):
        subject["analyses"][0]["analysis"]["alternative"] = "unknown"

    def unknown_model_field(subject):
        subject["analyses"][1]["analysis"]["design"]["model"]["visits"] = 3

    def other_combination(subject):
        subject["method"] = "gatekeeping"

    def no_alpha(subject):
        del subject["alpha"]

    for change in (one_sided, unknown_model_field, other_combination, no_alpha):
        with pytest.raises(Outside):
            program_data(changed(change))
    assert family["method"] == "bonferroni"  # the original is unchanged


def test_observational_studies_are_written_with_what_they_declare():
    program = canonical("examples/complex_survey.stat")
    data = program_data(program)
    assert '.associated "weighted" StatClaim.Generated.Methods.survey_linear' in data
    assert "survey := .weighted" in data and '["age", "sex", "income"]' in data

    def changed(change) -> dict:
        copied = copy.deepcopy(program)
        change(verify_claims(copied)[0]["subject"]["design"]["model"])
        return copied

    def unknown_field(study):
        study["region"] = "north"

    def unknown_scale(study):
        study["outcome_scale"] = "ordinal"

    for change in (unknown_field, unknown_scale):
        with pytest.raises(Outside):
            program_data(changed(change))


def test_a_cited_test_of_association_is_certified_through_the_semantics():
    from statclaim.language_syntax import Source as SyntaxSource
    from statclaim.lean_translation import certificate

    path = "examples/complex_survey.stat"
    inputs = certificate.payload(SyntaxSource((ROOT / path).read_text(), path))
    assert certificate.semantic(inputs) is not None
    [claim] = certificate.claims(inputs)
    assert (claim["claim"], claim["grade"], claim["premise"]) == (
        "typeI(weighted)",
        "cited",
        "cited_weighted_level",
    )


def test_binding_compares_the_printed_form_with_the_canonical_claims():
    program = canonical("examples/mixed_endpoints.stat")
    claims = {"claims": verify_claims(program), "declarations": declarations(program)}
    name = "examples/mixed_endpoints.stat"
    line = f"x.lean:1:0: info: {MARKER} {name} {json.dumps(claims)}"
    assert binding_problem(line, name, program) is None
    tampered = copy.deepcopy(claims)
    tampered["claims"][0]["subject"]["alpha"] = "1/40"
    assert binding_problem(f"{MARKER} {name} {json.dumps(tampered)}", name, program)
    assert binding_problem("", name, program)
    with pytest.raises(ValueError):
        report("a{b}")


def test_binding_compares_json_values_with_their_types():
    assert same_json({"a": [True, "1/20"], "b": 2}, {"b": 2, "a": [True, "1/20"]})
    assert not same_json({"reject_null": True}, {"reject_null": 1})
    assert not same_json({"n": 1}, {"n": "1"})


def test_the_writer_gives_every_probability_in_lowest_terms():
    data = program_data(canonical("examples/observational_power.stat"))
    fractions = re.findall(r"⟨(\d+), (\d+), by decide, by decide, by decide⟩", data)
    assert fractions
    assert all(math.gcd(int(num), int(den)) == 1 for num, den in fractions)


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_prints_the_canonical_program_and_catches_a_writer_mistake(tmp_path):
    name = "replication/copd/design_cited.stat"
    program = canonical(name)
    data = program_data(program)
    # A writer that misread the onset test's arm sizes.
    wrong = data.replace("sizes := ⟨500, 500,", "sizes := ⟨500, 499,", 1)
    assert wrong != data
    outputs = []
    for index, text in enumerate((data, wrong)):
        file = tmp_path / f"Program{index}.lean"
        file.write_text(
            f"import StatClaim\n\nnamespace P{index}\n\n{text}\n{report(name)}end P{index}\n"
        )
        run = subprocess.run(
            ["lake", "env", "lean", str(file)], cwd=ROOT, capture_output=True, text=True
        )
        assert run.returncode == 0, run.stdout + run.stderr
        outputs.append(run.stdout + run.stderr)
    assert binding_problem(outputs[0], name, program) is None
    assert binding_problem(outputs[1], name, program) is not None


@pytest.mark.lean
@pytest.mark.skipif(not shutil.which("lake"), reason="Lean required")
def test_lean_refuses_data_outside_canonical_form(tmp_path):
    name = "examples/randomisation_family.stat"
    data = program_data(canonical(name))
    # A writer that forgot that a conditional family assumes its exact members.
    unwrapped = data.replace(".member (", "(", 1)
    assert unwrapped != data
    for index, (text, accepted) in enumerate(((data, True), (unwrapped, False))):
        file = tmp_path / f"Canonical{index}.lean"
        file.write_text(
            f"import StatClaim\n\nnamespace C{index}\n\n{text}\n{CANONICAL}\nend C{index}\n"
        )
        run = subprocess.run(
            ["lake", "env", "lean", str(file)], cwd=ROOT, capture_output=True, text=True
        )
        assert (run.returncode == 0) == accepted, run.stdout + run.stderr


def test_every_cited_combination_is_a_registry_rule():
    """Lean reads cited ways of combining as data (`Test.procedure`), generated from
    composition.CITED_RULES; each rule's keys sit between the combination's own, in the
    increasing order Lean prints."""
    from statclaim.composition import CITED_RULES, MODES
    from statclaim.methods.boundaries import SPENDING

    assert {rule.mode for rule in CITED_RULES} == {
        key for key, mode in MODES.items() if mode.theorem is None
    }
    for rule in CITED_RULES:
        assert rule.fields[0] == ("method", MODES[rule.mode].method)
        keys = [key for key, _ in rule.fields]
        assert keys == sorted(set(keys))
        assert all("composition" < key < "transitions" and key != "test" for key in keys)
    spending = {dict(rule.fields).get("spending") for rule in CITED_RULES}
    assert set(SPENDING) <= spending


def test_cited_combinations_are_written_as_procedures():
    graph = program_data(canonical("examples/recycling.stat"))
    assert re.search(r'\.procedure "\w+" \.graphical\n', graph)
    looks = canonical("examples/group_sequential.stat")
    assert '.procedure "trial" .spending_obrien_fleming\n' in program_data(looks)
    # A spending function the registry does not list is outside the semantics.
    unknown = copy.deepcopy(looks)
    for binding in unknown["bindings"]:
        if binding["name"] == "trial":
            binding["value"]["spending"] = "hwang_shih_decani"
    for request in unknown["requests"]:
        request["claim"]["subject"]["spending"] = "hwang_shih_decani"
    with pytest.raises(Outside, match="group_sequential"):
        program_data(unknown)


def test_every_kind_of_test_and_combination_is_declared():
    """Lean declares tests and combinations and checks their contracts; every other value
    is read inside the tests and claims that use it."""
    import inspect

    from statclaim.language import ir
    from statclaim.lean_translation.data import DECLARATIONS

    tests = {
        name
        for name, kind in inspect.getmembers(ir, inspect.isclass)
        if kind.__module__ == ir.__name__
        and issubclass(kind, (ir.LevelTestIR, ir.FamilyLikeIR))
        and kind not in (ir.LevelTestIR, ir.FamilyLikeIR)
    }
    assert tests <= set(DECLARATIONS)


def test_a_planning_point_bound_by_name_is_read_where_it_is_used():
    text = (
        "use models.two_arm_survival\nuse sampling\nuse tests.survival\nuse planning\n"
        "let lifetimes = two_arm_survival(n_control=200, n_treatment=200)\n"
        "let ranked = log_rank(design=fixed(model=lifetimes), "
        "null=equal_survival(model=lifetimes), alpha=1/20)\n"
        "let point = hazard_ratio(value=7/10, events=200)\n"
        "let target = power_target(at=point, minimum=4/5, maximum_typeI=1/20)\n"
        "verify typeI(ranked)\ncalculate meets(analysis=ranked, target=target)\n"
    )
    program = compile_source(Source(text, "bound.stat")).program.to_dict()
    assert [entry["name"] for entry in declarations(program)] == ["ranked"]
    assert program_data(program).startswith("def program")
