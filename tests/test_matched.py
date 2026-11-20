"""Matched case-control studies: McNemar's test, observed pairs and the conditional odds ratio.

Nothing here starts Lean; tests/test_association_integration.py does.
"""

import copy
import subprocess
from fractions import Fraction
from math import comb
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.matched import (
    MatchedInterval,
    MatchedPairs,
    MatchedResult,
    MatchedTest,
    interval_assumptions,
    interval_payload,
    matched_assumptions,
    matched_payload,
    parse_interval_payload,
    parse_matched_payload,
    parse_result_payload,
    render_interval_proof,
    render_matched_proof,
    render_result_proof,
    result_assumptions,
    result_payload,
    tails,
)
from statclaim.methods.identify import identify

ROOT = Path(__file__).resolve().parents[1]
USES = (
    "use models.observational\nuse sampling\nuse tests.association\nuse estimation.observational\n"
)
STUDY = 'let paired = matched_case_control(pairs=150, exposure="smoking", outcome="lung cancer")\n'
TEST = (
    "let analysis = mcnemar(design=fixed(model=paired), null=no_association(model=paired), "
    "alpha=1/20)\n"
)
PAIRS = (
    "let seen = observed_pairs(model=paired, both_exposed=40, case_exposed_only=35, "
    "control_exposed_only=15, neither_exposed=60)\n"
)


def compiled(text):
    return compile_source(Source(USES + text, "study.stat"))


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_a_matched_study_compiles_with_a_checked_derivation():
    compilation = compiled(STUDY + TEST + PAIRS + "let claim = verify(typeI(analysis))\n")
    assert compilation.status == "elaborated", compilation.diagnostics
    record = next(d for d in compilation.derivations if d.name == "analysis").to_dict()
    assert record["contract"] == "tests.association/mcnemar"
    assert check_derivation(record) == []
    changed = copy.deepcopy(record)
    changed["subject"]["design"]["model"]["pairs"] = 151
    assert check_derivation(changed) != []
    changed = copy.deepcopy(record)
    changed["assumptions"] = changed["assumptions"][1:]
    assert check_derivation(changed) != []
    null = next(b.value for b in compilation.program.bindings if b.name == "analysis").hypothesis
    assert null.statement == "conditional_odds_ratio = 1"


@pytest.mark.parametrize(
    "declaration,code,fragment",
    [
        (
            "let t = fisher_exact(design=fixed(model=paired), null=no_association(model=paired), "
            "alpha=1/20)\n",
            "matched_design",
            "mcnemar",
        ),
        (
            "let t = observed_table(model=paired, exposed_cases=1, exposed_noncases=1, "
            "unexposed_cases=1, unexposed_noncases=147)\n",
            "matched_design",
            "observed_pairs",
        ),
        (
            "let c = cohort(exposed=10, unexposed=10)\n"
            "let t = mcnemar(design=fixed(model=c), null=no_association(model=c), alpha=1/20)\n",
            "type",
            "fisher_exact",
        ),
        (
            "let t = observed_pairs(model=paired, both_exposed=40, case_exposed_only=35, "
            "control_exposed_only=15, neither_exposed=61)\n",
            "domain",
            "add up to 151",
        ),
        (
            "let t = conditional_odds_ratio(pairs=observed_pairs(model=paired, both_exposed=50, "
            "case_exposed_only=0, control_exposed_only=0, neither_exposed=100), level=19/20)\n",
            "domain",
            "No pair is discordant",
        ),
        ("let t = matched_case_control(pairs=0)\n", "domain", "pairs must be"),
    ],
)
def test_matched_and_unmatched_analyses_do_not_mix(declaration, code, fragment):
    diagnostics = compiled(STUDY + declaration).diagnostics
    assert diagnostics[0].code == code
    assert fragment in diagnostics[0].message


def test_results_and_the_odds_ratio_calculate_exactly(tmp_path):
    text = (
        STUDY
        + TEST
        + PAIRS
        + "let found = calculate(matched_result(analysis=analysis, pairs=seen))\n"
        + "let odds = calculate(conditional_odds_ratio(pairs=seen, level=19/20))\n"
        + "let p = found.calculation.p_value\n"
    )
    report = check_source(Source(USES + text, "study.stat"), project=ROOT, output=tmp_path / "r")
    assert report["status"] == "calculated"
    found, odds = (request["report"]["calculation"] for request in report["requests"])
    expected = Fraction(2 * sum(comb(50, k) for k in range(35, 51)), 2**50)
    assert Fraction(found["p_value"]["fraction"]) == expected
    assert report["values"]["p"] == str(expected)
    assert Fraction(odds["estimate"]["fraction"]) == Fraction(35, 15)
    assert (
        Fraction(odds["lower"]["fraction"]) < Fraction(7, 3) < Fraction(odds["upper"]["fraction"])
    )


def test_tails_and_the_two_sided_p_value():
    assert tails(4, 2) == (11, 11)
    result = MatchedResult(MatchedTest(10, Fraction(1, 20)), MatchedPairs(10, (3, 2, 2, 3)))
    assert result.p_value == 1 and not result.reject_null
    result = MatchedResult(MatchedTest(10, Fraction(1, 20)), MatchedPairs(10, (0, 8, 0, 2)))
    assert result.p_value == Fraction(2, 2**8) and result.reject_null


TEST_OBJECT = MatchedTest(150, Fraction(1, 20), "smoking", "lung cancer")
OBSERVED = MatchedPairs(150, (40, 35, 15, 60), "smoking", "lung cancer")
NO_CONTROL = MatchedPairs(150, (40, 20, 0, 90), "smoking", "lung cancer")


def test_payloads_round_trip_and_reject_tampering():
    def version(payload):
        payload["analysis"]["test_version"] = "9"

    def decision(payload):
        payload["result"]["reject_null"] = False

    def lower(payload):
        payload["interval"]["lower"] = "0"

    for build, parse, value, tamper in [
        (matched_payload, parse_matched_payload, TEST_OBJECT, version),
        (result_payload, parse_result_payload, MatchedResult(TEST_OBJECT, OBSERVED), decision),
        (
            interval_payload,
            parse_interval_payload,
            MatchedInterval(OBSERVED, Fraction(19, 20)),
            lower,
        ),
    ]:
        payload = build(value)
        assert parse(copy.deepcopy(payload)) == value
        changed = copy.deepcopy(payload)
        tamper(changed)
        with pytest.raises(ValueError):
            parse(changed)


def test_proofs_and_assumptions():
    assert "Matched.typeI" in render_matched_proof(TEST_OBJECT, "a" * 64)
    result = MatchedResult(TEST_OBJECT, OBSERVED)
    proof = render_result_proof(result, "a" * 64)
    upper, lower = tails(50, 35)
    assert f"= {upper} ∧" in proof and "↔ True" in proof
    interval = MatchedInterval(NO_CONTROL, Fraction(19, 20))
    assert interval.bounds[1] is None and interval.estimate is None
    assert (
        "∧"
        not in render_interval_proof(interval, "a" * 64).split("checked_interval")[1].split(":=")[0]
    )
    for texts in (
        matched_assumptions(),
        result_assumptions(result),
        interval_assumptions(interval),
    ):
        assert all(identify(text)["id"] for text in texts)


def test_the_lesson_and_example_compile():
    for name in ("examples/tutorial/25_matched_pairs.stat", "examples/matched_case_control.stat"):
        path = ROOT / name
        compilation = compile_source(Source(path.read_text(), str(path)))
        assert compilation.status == "elaborated", (name, compilation.diagnostics)
