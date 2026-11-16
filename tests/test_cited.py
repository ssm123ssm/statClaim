"""Contract-tier analyses: checked against their contract, cited, never verified."""

import json
import subprocess
from pathlib import Path

import pytest

from statclaim.cli import main
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.language_values import Evidence, VerificationResult
from statclaim.methods import ASSUMPTIONS, METHODS
from statclaim.methods.core import SCOPES
from statclaim.verification import digest

ROOT = Path(__file__).resolve().parents[1]
HEAD = (
    "use models.two_arm_continuous\nuse sampling\nuse tests.t\n"
    "let study = two_arm_continuous(n_control=60, n_treatment=60)\n"
)
FIXED = HEAD + "let plan = fixed(model=study)\n"
EQUAL = FIXED + "let null = equal_means(model=study)\n"


def run(text, tmp_path):
    return check_source(Source(text, "cited.stat"), project=ROOT, output=tmp_path / "run")


def codes(text):
    return [d.code for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_every_method_states_scope_assumptions_and_references():
    for method in METHODS.values():
        assert method.scope in SCOPES
        assert method.assumptions and method.references
        assert all(ASSUMPTIONS[item.id] is item for item in method.assumptions)
    assert METHODS["t_test"].scope == "finite_sample"
    assert METHODS["welch_test"].scope == "asymptotic"


def test_changing_a_method_requires_a_new_version():
    """Evidence records the method version, so a silent change would mislead."""
    recorded = json.loads((ROOT / "tests/fixtures/method_versions.json").read_text())
    current = {
        key: {"version": method.version, "sha256": digest(repr(method).encode())}
        for key, method in METHODS.items()
    }
    assert current == recorded, (
        "A cited method changed. Bump its version, then run "
        "'uv run python scripts/update_method_versions.py'."
    )


def test_cited_claim_gives_cited_evidence_without_lean_or_certificate(tmp_path):
    text = (
        EQUAL
        + "let analysis = t_test(design=plan, null=null, alpha=1/20)\n"
        + "let checked = verify(typeI(analysis))\n"
        + "let file = checked.evidence.certificate.file\n"
        + "let scope = checked.claim.scope\n"
    )
    report = run(text, tmp_path)
    value = report["values"]["checked"]
    assert report["status"] == value["status"] == "cited"
    assert not report["backend_invoked"] and not report["certificate_issued"]
    evidence = value["evidence"]
    assert evidence["grade"] == "cited" and evidence["certificate"] is None
    assert evidence["scope"] == report["values"]["scope"] == "finite_sample"
    assert evidence["guarantee"] == {
        "quantity": "type_I_error",
        "relation": "equals",
        "bound": "1/20",
        "null": "mean_treatment = mean_control",
        "scope": "finite_sample",
    }
    assert evidence["sources"] == ["literature"] and evidence["machine_checked"] == "contract"
    assert evidence["method"] == {
        "key": "t_test",
        "version": 1,
        "title": "Two-sided pooled-variance t-test",
    }
    assert {"id": "normal_outcomes", "kind": "distribution"}.items() <= evidence["assumptions"][
        3
    ].items()
    assert evidence["references"] == list(METHODS["t_test"].references)
    assert all(text.startswith("Cited, not checked") for text in evidence["established_properties"])
    assert report["values"]["file"] is None
    rendered = render_report(report, Source(text))
    assert "verified" not in rendered
    assert "cited from the literature; not machine-checked" in rendered


def test_approximate_guarantee_is_worded_and_scoped_differently(tmp_path):
    text = (
        FIXED
        + "let margin = mean_difference_at_most(model=study, value=-2)\n"
        + "let welch = welch_test_one_sided(design=plan, null=margin, alpha=1/40)\n"
        + "let checked = verify(typeI(welch))\n"
    )
    evidence = run(text, tmp_path)["values"]["checked"]["evidence"]
    assert evidence["scope"] == "asymptotic"
    assert (
        "No bound is claimed at the declared sample sizes" in evidence["established_properties"][0]
    )


def test_cited_evidence_can_never_back_a_verified_result():
    claim = (
        compile_source(Source(EQUAL + "verify typeI(t_test(design=plan, null=null, alpha=1/20))\n"))
        .program.requests[0]
        .claim
    )
    cited = Evidence(claim, None, (), ("assumed",), "cited", ("reference",))
    assert VerificationResult(1, claim, "snapshot", "cited", cited).evidence is cited
    with pytest.raises(ValueError, match="checked by Lean"):
        VerificationResult(1, claim, "snapshot", "verified", cited)
    with pytest.raises(ValueError, match="carries a certificate"):
        Evidence(claim, None, (), (), "proved")
    with pytest.raises(ValueError, match="carries a certificate"):
        Evidence(claim, {"certificate_id": "x"}, (), (), "cited")


@pytest.mark.parametrize(
    "tail,code",
    [
        # A one-sided question put to the two-sided test, and the reverse.
        (
            "let null = mean_difference_at_most(model=study, value=0)\n"
            "let a = t_test(design=plan, null=null, alpha=1/20)\n",
            "hypothesis_mismatch",
        ),
        (
            "let null = equal_means(model=study)\n"
            "let a = welch_test_one_sided(design=plan, null=null, alpha=1/20)\n",
            "hypothesis_mismatch",
        ),
        # A null declared for a different study.
        (
            "let other = two_arm_continuous(n_control=10, n_treatment=10)\n"
            "let null = equal_means(model=other)\n"
            "let a = t_test(design=plan, null=null, alpha=1/20)\n",
            "model_mismatch",
        ),
        ("let null = equal_means(model=study)\nlet a = t_test(plan, null, alpha=0)\n", "domain"),
    ],
)
def test_contract_violations_are_reported_while_editing(tail, code):
    assert codes(FIXED + tail) == [code]


def test_binary_and_continuous_methods_do_not_mix():
    text = (
        "use models.two_arm_binomial\nuse tests.fisher\n"
        + EQUAL
        + "let binary = two_arm_binomial(n_control=60, n_treatment=60)\n"
        + "let a = fisher(design=plan, null=equal_proportions(model=binary), alpha=1/20)\n"
    )
    assert codes(text) == ["model_mismatch"]
    assert codes(
        EQUAL.replace("60, n_treatment=60", "1, n_treatment=1") + "let a = "
        "welch_test(design=plan, null=null, alpha=1/20)\n"
    ) == ["domain"]


def test_data_dependent_stopping_leaves_the_cited_claim_unresolved(tmp_path):
    text = (
        HEAD
        + "let plan = adaptive(model=study)\nlet null = equal_means(model=study)\n"
        + "let checked = verify(typeI(t_test(design=plan, null=null, alpha=1/20)))\n"
    )
    assert codes(text) == ["sampling_scope"]
    value = check_source(Source(text, "cited.stat"), project=ROOT)["values"]["checked"]
    assert value["status"] == "unresolved_obligation" and value["evidence"] is None


def test_example_runs_from_the_cli_without_lean(capsys):
    assert main(["check", str(ROOT / "examples/t_test.stat"), "--project", str(ROOT)]) == 0
    assert "Program status: cited" in capsys.readouterr().out
