"""Which direction of the outcome is better: declared and checked, or listed as assumed."""

import copy
import subprocess
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods import METHODS
from statclaim.methods.power import two_means

ROOT = Path(__file__).resolve().parents[1]


def continuous(better=None, null="mean_difference_at_most(model=study, value=-3)"):
    declared = f', better="{better}"' if better else ""
    return (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse tests.mixed_model\n"
        "use planning\n"
        f"let study = two_arm_continuous(n_control=200, n_treatment=200{declared})\n"
        "let plan = fixed(model=study)\n"
        f"let null = {null}\n"
        "let analysis = mmrm_test_one_sided(design=plan, null=null, alpha=1/40)\n"
    )


def compiled(text):
    return compile_source(Source(text))


def codes(text):
    return [d.code for d in compiled(text).diagnostics]


def derivation(text, name="analysis"):
    return next(d for d in compiled(text).derivations if d.name == name).to_dict()


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_a_null_facing_the_wrong_way_is_refused_with_the_right_null_named():
    diagnostics = compiled(continuous("lower")).diagnostics
    assert [d.code for d in diagnostics][0] == "direction_mismatch"
    assert "mean_difference_at_least" in diagnostics[0].message
    at_least = "mean_difference_at_least(model=study, value=3)"
    assert codes(continuous("higher", at_least))[0] == "direction_mismatch"


def test_a_lower_is_better_outcome_uses_the_mirrored_null(tmp_path):
    text = continuous("lower", "mean_difference_at_least(model=study, value=3)")
    text += "let checked = verify(typeI(analysis))\n"
    assert codes(text) == []
    report = check_source(Source(text, "d.stat"), project=tmp_path, output=tmp_path / "run")
    value = report["values"]["checked"]
    assert value["status"] == "cited"
    assert "mean_treatment - mean_control >= 3" in value["evidence"]["guarantee"]["null"]
    ids = [item["id"] for item in value["evidence"]["assumptions"]]
    assert "lower_is_better" not in ids and "higher_is_better" not in ids
    record = derivation(text)
    assert check_derivation(record) == []
    step = next(s for s in record["steps"] if s["rule"] == "supported-null")
    assert step["facts"]["better"] == "lower"
    assert step["facts"]["supported"] == ["mean_difference_at_most", "mean_difference_at_least"]


@pytest.mark.parametrize(
    ("null", "assumed"),
    [
        ("mean_difference_at_most(model=study, value=-3)", "higher_is_better"),
        ("mean_difference_at_least(model=study, value=3)", "lower_is_better"),
    ],
)
def test_an_undeclared_direction_is_listed_as_assumed(null, assumed, tmp_path):
    text = continuous(None, null) + "let checked = verify(typeI(analysis))\n"
    report = check_source(Source(text, "d.stat"), project=tmp_path, output=tmp_path / "run")
    evidence = report["values"]["checked"]["evidence"]
    item = next(item for item in evidence["assumptions"] if item["id"] == assumed)
    assert item["kind"] == "meaning" and item["status"] == "assumed"
    record = derivation(text)
    assert check_derivation(record) == []
    assert assumed in record["guarantee"]["given"]
    assert any("declare better=" in text for text in record["assumptions"])


def test_two_sided_nulls_take_no_side():
    text = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\n"
        'let study = two_arm_continuous(n_control=50, n_treatment=50, better="lower")\n'
        "let analysis = t_test(design=fixed(model=study), null=equal_means(model=study), "
        "alpha=1/20)\n"
    )
    assert codes(text) == []
    assert not any("better" in t for t in derivation(text)["assumptions"])


def test_better_must_be_higher_or_lower():
    assert codes(continuous("smaller"))[0] == "domain"


def test_binary_lower_is_better_points_to_the_complementary_outcome():
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.difference\n"
        'let study = two_arm_binomial(n_control=100, n_treatment=100, better="lower")\n'
        "let null = proportion_difference_at_most(model=study, value=-1/10)\n"
    )
    diagnostics = compiled(text).diagnostics
    assert diagnostics[0].code == "direction_mismatch"
    assert "complementary outcome" in diagnostics[0].message
    higher = text.replace('better="lower"', 'better="higher"')
    higher += "let analysis = difference_test(design=fixed(model=study), null=null, alpha=1/40)\n"
    assert codes(higher) == []
    assert check_derivation(derivation(higher)) == []


def test_only_the_one_sided_continuous_tests_mirror():
    mirrored = {key for key, method in METHODS.items() if method.mirrored_null}
    assert mirrored == {"t_test_one_sided", "welch_test_one_sided", "mmrm_test_one_sided"}
    assert all(METHODS[key].version == 2 for key in mirrored)


def test_power_for_a_lower_is_better_test_mirrors_the_higher_one(tmp_path):
    lower = two_means({"value": 0, "sd": 15}, 300, 300, 4, 0.025, "lower")
    higher = two_means({"value": 0, "sd": 15}, 300, 300, -4, 0.025, "higher")
    assert lower.power == pytest.approx(higher.power)
    assert lower.critical == pytest.approx(-higher.critical)
    assert lower.direction == "below"
    text = continuous("lower", "mean_difference_at_least(model=study, value=3)")
    target = "power_target(at=mean_difference(value=0, sd=10), minimum=4/5, maximum_typeI=1/40)"
    report = check_source(
        Source(text + f"let power = calculate(meets(analysis=analysis, target={target}))\n"),
        project=tmp_path,
        output=tmp_path / "run",
    )
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["reject_when"] == "below"
    assert float(calculation["critical_estimate"]["decimal_approximation"]) < 3
    inside = target.replace("value=0", "value=4")
    assert codes(text + f"calculate(meets(analysis=analysis, target={inside}))\n") == [
        "alternative_in_null"
    ]
    claim = text + f"let claim = meets(analysis=analysis, target={target})\n"
    assert check_derivation(derivation(claim, "claim")) == []


def test_checker_rejects_a_direction_changed_after_the_fact():
    record = derivation(continuous("higher"))
    assert check_derivation(record) == []
    flipped = copy.deepcopy(record)
    flipped["subject"]["null"]["model"]["better"] = "lower"
    flipped["subject"]["design"]["model"]["better"] = "lower"
    for step in flipped["steps"]:
        if step["rule"] == "supported-null":
            step["facts"]["better"] = "lower"
    assert any("premise does not hold" in p for p in check_derivation(flipped))
    dropped = copy.deepcopy(derivation(continuous(None)))
    dropped["assumptions"] = [a for a in dropped["assumptions"] if "better" not in a]
    assert check_derivation(dropped)


def test_composed_families_carry_the_direction_assumption():
    text = continuous(None) + (
        "use multiplicity.bonferroni\n"
        "let other = mmrm_test_one_sided(design=plan, null=null, alpha=1/80)\n"
        "let first = mmrm_test_one_sided(design=plan, null=null, alpha=1/80)\n"
        "let family = bonferroni(analyses=[first, other], alpha=1/40)\n"
    )
    record = derivation(text, "family")
    assert check_derivation(record) == []
    assert any("Higher values of the outcome are better" in a for a in record["assumptions"])
