"""The program as Lean data, and the check that it is the canonical program. See
docs/proposals/lean-semantics.md."""

import copy
import importlib.util
import json
import re
import shutil
import subprocess
from pathlib import Path

import pytest

from statclaim.language_compiler import compile_source
from statclaim.lean_translation.certificate import Source
from statclaim.lean_translation.data import (
    MARKER,
    Outside,
    binding_problem,
    declarations,
    fixed,
    program_data,
    report,
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
        requests = re.findall(r"^  \.(typeI|familywise) ", data, re.MULTILINE)
        assert len(requests) == len(verify_claims(program))


def test_todays_translation_of_every_covered_program_can_be_restated():
    """The agreement check needs each abstract part and premise of today's translation
    traced to a model, test or graph of the canonical program."""
    checker = semantics_checker()
    found, _ = checker.covered()
    for path, program, _ in found.values():
        text = checker.agreement(path, program)
        assert text.startswith("namespace Old")
        stated = any(fixed(claim["subject"]) for claim in verify_claims(program))
        assert ("Old.Claims i ↔" in text) == stated


def test_the_writer_refuses_what_it_does_not_read():
    program = canonical("examples/mixed_endpoints.stat")
    family = verify_claims(program)[0]["subject"]

    def changed(change) -> dict:
        copied = copy.deepcopy(program)
        change(verify_claims(copied)[0]["subject"])
        return copied

    def one_sided(subject):
        subject["analyses"][0]["analysis"]["alternative"] = "greater"

    def unknown_model_field(subject):
        subject["analyses"][1]["analysis"]["design"]["model"]["visits"] = 3

    def other_combination(subject):
        subject["method"] = "alpha_spending"

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
