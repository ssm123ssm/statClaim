"""A two-arm model is built from an assignment and an outcome; one call is shorthand."""

import subprocess
from pathlib import Path

import pytest

from statclaim.contract_reports import explain, impact
from statclaim.language import ModelIR, OutcomeModelIR, normalize
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import inspect_program
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]
SHARED = (ROOT / "examples/shared_assignment.stat").read_text()
SEPARATE = (ROOT / "examples/mixed_endpoints.stat").read_text()
USES = "use models.two_arm_binomial\nuse models.two_arm_continuous\nuse models.two_arm_survival\n"


def compiled(text):
    return compile_source(Source(text, "study.stat"))


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


def values(text):
    compilation = compiled(text)
    assert not compilation.diagnostics, compilation.diagnostics
    return {binding.name: binding.value for binding in compilation.program.bindings}


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize(
    ("kind", "shorthand", "model_type"),
    [
        ("binary", "two_arm_binomial", ModelIR),
        ("continuous", "two_arm_continuous", OutcomeModelIR),
        ("survival", "two_arm_survival", OutcomeModelIR),
    ],
)
@pytest.mark.parametrize("better", [None, "higher", "lower"])
def test_pieces_and_the_one_call_spelling_give_the_same_model(kind, shorthand, model_type, better):
    declared = f'better="{better}"' if better else ""
    sizes = "n_control=30, n_treatment=45"
    found = values(
        USES + f"let arms = assignment({sizes})\n"
        f"let measured = {kind}_outcome({declared})\n"
        "let pieces = two_arm(assignment=arms, outcome=measured)\n"
        f"let short = {shorthand}({sizes}{', ' + declared if declared else ''})\n"
    )
    assert type(found["pieces"]) is model_type
    assert found["pieces"] == found["short"]
    assert normalize(found["pieces"]) == normalize(found["short"])


@pytest.mark.parametrize(
    ("kind", "shorthand"),
    [
        ("binary", "two_arm_binomial"),
        ("continuous", "two_arm_continuous"),
        ("survival", "two_arm_survival"),
    ],
)
def test_the_one_call_spelling_takes_a_population_and_a_name(kind, shorthand):
    sizes = "n_control=30, n_treatment=45"
    found = values(
        USES + f'let arms = assignment({sizes}, population="per_protocol")\n'
        f'let measured = {kind}_outcome(name="primary")\n'
        "let pieces = two_arm(assignment=arms, outcome=measured)\n"
        f'let short = {shorthand}({sizes}, population="per_protocol", name="primary")\n'
    )
    assert found["pieces"] == found["short"]
    assert normalize(found["pieces"]) == normalize(found["short"])
    assert found["short"].assignment.population == "per_protocol"
    assert found["short"].measured.name == "primary"


def test_sharing_an_assignment_changes_no_claim_or_contract():
    """The example states its sizes once; its claims match separate declarations."""
    separate = SEPARATE.replace(
        "two_arm_binomial(n_control=120, n_treatment=120)",
        'two_arm_binomial(n_control=120, n_treatment=120, better="higher")',
    ).replace(
        "two_arm_continuous(n_control=120, n_treatment=120)",
        'two_arm_continuous(n_control=120, n_treatment=120, better="lower")',
    )
    # The one-call models cannot name their outcomes, so compare without the names.
    unnamed = SHARED.replace(', name="response"', "").replace(', name="symptom score"', "")
    shared, separate = compiled(unnamed), compiled(separate)
    assert not shared.diagnostics and not separate.diagnostics
    assert [normalize(r.claim) for r in shared.program.requests] == [
        normalize(r.claim) for r in separate.program.requests
    ]
    assert [e["derivation"] for e in explain(shared)] == [
        e["derivation"] for e in explain(separate)
    ]
    assert [c["best_status"] for c in inspect_program(shared)] == ["conditional", "verified"]


def test_a_model_depends_on_its_pieces_and_a_size_change_reaches_every_claim():
    bindings = {b.name: b for b in compiled(SHARED).program.bindings}
    assert bindings["responders"].dependencies == ("arms",)
    assert bindings["scores"].dependencies == ("arms",)
    changed = SHARED.replace("n_treatment=120", "n_treatment=150")
    result = impact(compiled(SHARED), compiled(changed))
    kinds = {entry["name"]: entry["change"] for entry in result["declarations"]}
    assert kinds["arms"] == "changed directly"
    for name in ("responders", "scores", "response", "symptoms", "endpoints"):
        assert kinds[name] == "affected through a dependency"
    assert {claim["subject"] for claim in result["claims"]} == {"endpoints", "response"}


def test_the_pieces_are_public_fields():
    found = values(
        USES + "let arms = assignment(n_control=30, n_treatment=45)\n"
        'let trial = two_arm(assignment=arms, outcome=continuous_outcome(better="lower"))\n'
        "let control = trial.assignment.n_control\n"
        "let kind = trial.outcome.kind\n"
        "let better = trial.outcome.better\n"
        "let treatment = trial.n_treatment\n"
        "let short = two_arm_binomial(n_control=5, n_treatment=6)\n"
        "let short_kind = short.outcome.kind\n"
    )
    assert (found["control"], found["kind"], found["better"]) == (30, "continuous", "lower")
    assert (found["treatment"], found["short_kind"]) == (45, "binary")


def test_the_binary_pieces_give_the_lean_backed_model():
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.fisher\n"
        "let arms = assignment(n_control=20, n_treatment=20)\n"
        "let study = two_arm(assignment=arms, outcome=binary_outcome())\n"
        "let analysis = fisher(design=fixed(model=study), null=equal_proportions(model=study), "
        "alpha=1/20)\n"
    )
    assert codes(text) == []
    # A continuous outcome gives a model the binomial nulls refuse.
    wrong = text.replace("use sampling\n", "use sampling\nuse models.two_arm_continuous\n")
    assert codes(wrong.replace("binary_outcome()", "continuous_outcome()")) == ["type"]


@pytest.mark.parametrize(
    ("line", "code"),
    [
        ("let bad = assignment(n_control=0, n_treatment=5)", "domain"),
        ('let bad = continuous_outcome(better="up")', "domain"),
        ("let bad = two_arm(assignment=continuous_outcome(), outcome=arms)", "type"),
        ("let bad = two_arm(assignment=arms)", "arguments"),
        ('let bad = two_arm_binomial(n_control=3, n_treatment=5, population="itt")', "domain"),
        ('let bad = two_arm_continuous(n_control=3, n_treatment=5, name=" ")', "domain"),
        # Randomisation needs the assignment piece.
        (
            'let bad = two_arm_survival(n_control=3, n_treatment=5, randomisation="complete")',
            "arguments",
        ),
    ],
)
def test_malformed_pieces_are_refused(line, code):
    base = USES + "let arms = assignment(n_control=3, n_treatment=5)\n"
    assert codes(base + line + "\n") == [code]


def test_the_direction_check_reads_the_outcome_piece():
    text = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\n"
        "let arms = assignment(n_control=50, n_treatment=50)\n"
        'let study = two_arm(assignment=arms, outcome=continuous_outcome(better="lower"))\n'
        "let null = mean_difference_at_most(model=study, value=0)\n"
    )
    assert codes(text) == ["direction_mismatch"]
    assert codes(text.replace("_at_most", "_at_least")) == []
