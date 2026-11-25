"""Group-sequential designs whose boundaries use the correlation between looks: the
boundaries against rpact and gsDesign, the contract, and the cited rule."""

import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods import boundaries

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/spending_boundaries_r.json").read_text())
EXAMPLE = ROOT / "examples/group_sequential.stat"


def program(looks: str, test: str = "t_test", spending: str = "obrien_fleming", alpha="1/20"):
    model = "two_arm_continuous" if test.startswith(("t_", "welch")) else "two_arm_binomial"
    null = "equal_means" if model == "two_arm_continuous" else "equal_proportions"
    lines = [
        f"use models.{model}",
        "use sampling",
        "use tests.t",
        "use tests.fisher",
        "use models.two_arm_survival",
        "use tests.survival",
        "use designs.group_sequential",
    ]
    names = []
    for index, (n, level) in enumerate(looks):
        lines.append(f"let m{index} = {model}(n_control={n}, n_treatment={n})")
        lines.append(
            f"let look{index} = {test}(design=fixed(model=m{index}), "
            f"null={null}(model=m{index}), alpha={level})"
        )
        names.append(f"look{index}")
    lines.append(
        f"let trial = group_sequential(looks=[{', '.join(names)}], alpha={alpha}, "
        f'spending="{spending}")'
    )
    return "\n".join(lines) + "\n"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


@pytest.mark.parametrize(
    "case", FIXTURE["cases"], ids=lambda c: f"{c['spending']}-{c['sides']}-{len(c['sizes'])}"
)
def test_boundaries_agree_with_rpact_and_gsdesign(case):
    """R values from replication/comparison/spending_boundaries_r.R; R is not needed here."""
    sizes = [tuple(size) for size in case["sizes"]]
    information = boundaries.information(sizes)
    alpha = float(Fraction(case["alpha"]))
    found = boundaries.boundaries(information, alpha, case["sides"], case["spending"])
    for ours, theirs, other in zip(found, case["critical"], case["gsdesign"], strict=True):
        assert ours == pytest.approx(theirs, abs=2e-6)
        assert ours == pytest.approx(other, abs=2e-6)
    levels = boundaries.levels(information, alpha, case["sides"], case["spending"])
    assert levels == pytest.approx(case["nominal"], abs=1e-7)
    stopped = boundaries.crossings(information, found, case["sides"], case["drift"])
    assert stopped == pytest.approx(case["stopped"], abs=2e-6)
    null = boundaries.crossings(information, found, case["sides"])
    assert null == pytest.approx(case["stopped_null"], abs=2e-6)
    assert sum(null) == pytest.approx(alpha, abs=1e-7)


def test_the_spending_functions_spend_the_whole_level():
    for spending in boundaries.SPENDING:
        for sides in (1, 2):
            assert boundaries.spent(spending, 0.05, 1.0, sides) == pytest.approx(0.05)
            assert boundaries.spent(spending, 0.05, 0.0, sides) == 0.0
            early = boundaries.spent(spending, 0.05, 0.3, sides)
            assert 0 < early < boundaries.spent(spending, 0.05, 0.7, sides) < 0.05


def test_levels_within_the_boundaries_compile_to_a_cited_design():
    compiled = compile_source(Source(program([(50, "3/1000"), (100, "6/125")])))
    assert compiled.status == "elaborated", compiled.diagnostics
    design = next(b.value for b in compiled.program.bindings if b.name == "trial")
    composition = design.lower()
    assert composition.rules.grade == "cited" and composition.scope == "asymptotic"
    assert [str(limit) for limit in composition.limits] == [
        "610129/200000000",
        "48999543/1000000000",
    ]
    assert composition.fits
    for derivation in compiled.derivations:
        assert check_derivation(derivation.to_dict()) == []


def test_planning_a_spending_design_is_checked_independently():
    source = EXAMPLE.read_text().replace(
        "let simulated = simulate(meets(analysis=trial, target=target), seed=2026)",
        "let claim = meets(analysis=trial, target=target)\n"
        "let simulated = simulate(claim, seed=2026)",
    )
    compiled = compile_source(Source(source))
    assert {d.name for d in compiled.derivations} >= {"trial", "claim"}
    for derivation in compiled.derivations:
        assert check_derivation(derivation.to_dict()) == [], derivation.name


def test_a_level_beyond_its_boundary_is_refused_with_the_levels_to_use():
    found = diagnostics(program([(50, "1/200"), (100, "9/200")]))
    assert [code for code, _ in found] == ["sequential_boundary"]
    message = found[0][1]
    assert "look0" in message and "look1" not in message.split(":")[0]
    assert "look0 alpha=61/20000" in message and "look1 alpha=48999/1000000" in message


def test_a_pocock_design_may_spend_more_than_the_union_bound():
    # Three looks at about 0.0217 each: 0.065 in all, but 0.05 with the correlation.
    looks = [(40, "217/10000"), (80, "217/10000"), (120, "216/10000")]
    compiled = compile_source(Source(program(looks, spending="pocock")))
    assert compiled.status == "elaborated", compiled.diagnostics
    sizes = [(n, n) for n, _ in looks]
    declared = [Fraction(level) for _, level in looks]
    assert sum(declared) > Fraction(1, 20)
    assert boundaries.overall(sizes, declared, 2) <= 0.05


def test_the_rule_needs_information_read_from_arm_sizes():
    text = program([(50, "3/1000"), (100, "6/125")], spending="haybittle")
    assert [code for code, _ in diagnostics(text)] == ["domain"]
    survival = (
        "use models.two_arm_survival\nuse sampling\nuse tests.survival\n"
        "use designs.group_sequential\n"
        "let m0 = two_arm_survival(n_control=50, n_treatment=50)\n"
        "let m1 = two_arm_survival(n_control=100, n_treatment=100)\n"
        "let a = log_rank(design=fixed(model=m0), null=equal_survival(model=m0), alpha=3/1000)\n"
        "let b = log_rank(design=fixed(model=m1), null=equal_survival(model=m1), alpha=6/125)\n"
        'let trial = group_sequential(looks=[a, b], alpha=1/20, spending="obrien_fleming")\n'
    )
    found = diagnostics(survival)
    assert [code for code, _ in found] == ["unsupported_claim"]
    assert "alpha_spending" in found[0][1]


def test_one_sided_tests_spend_on_one_side():
    one_sided = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse designs.group_sequential\n"
        "let m0 = two_arm_continuous(n_control=50, n_treatment=50)\n"
        "let m1 = two_arm_continuous(n_control=100, n_treatment=100)\n"
        "let a = t_test_one_sided(design=fixed(model=m0), "
        "null=mean_difference_at_most(model=m0, value=0), alpha={first})\n"
        "let b = t_test_one_sided(design=fixed(model=m1), "
        "null=mean_difference_at_most(model=m1, value=0), alpha=24/1000)\n"
        'let trial = group_sequential(looks=[a, b], alpha=1/40, spending="obrien_fleming")\n'
    )
    # One-sided O'Brien-Fleming at half the information: 0.001525 at the first look.
    assert compile_source(Source(one_sided.format(first="15/10000"))).status == "elaborated"
    found = diagnostics(one_sided.format(first="16/10000"))
    assert [code for code, _ in found] == ["sequential_boundary"]
    assert "a alpha=61/40000" in found[0][1]


def test_the_example_is_cited_and_its_power_simulated(tmp_path):
    report = check_source(
        Source(EXAMPLE.read_text(), "examples/group_sequential.stat"),
        project=tmp_path,
        output=tmp_path / "run",
    )
    overall, simulated = (r["report"] for r in report["requests"])
    assert overall["status"] == "cited"
    assert overall["method"]["key"] == "group_sequential"
    assert any("canonical joint" in a["text"] for a in overall["assumptions"])
    looks = simulated["calculation"]["looks"]
    assert [look["alpha"]["fraction"] for look in looks] == ["3/1000", "6/125"]
    assert simulated["decision"] == "target_met"


@pytest.mark.parametrize(
    ("limits", "found"),
    [
        # A larger limit lets a look spend more than the function gives it.
        (["1/200", "48999543/1000000000"], "premise does not hold"),
        # Pocock's boundaries under O'Brien-Fleming spending.
        (None, "premise does not hold"),
        # A limit not rounded to the boundary's 1e-9.
        (["1/3", "48999543/1000000000"], "premise does not hold"),
    ],
)
def test_the_checker_checks_recorded_limits_from_the_definition(limits, found):
    """The checker does not reuse the code that computed the boundaries: it integrates the
    chance of crossing each look itself, so altered limits fail."""
    compiled = compile_source(Source(program([(50, "3/1000"), (100, "6/125")])))
    record = next(d for d in compiled.derivations if d.name == "trial").to_dict()
    step = next(s for s in record["steps"] if s["rule"] == "spending-boundaries")
    assert check_derivation(record) == []
    if limits is None:
        information = boundaries.information([(50, 50), (100, 100)])
        pocock = boundaries.levels(information, 0.05, 2, "pocock")
        limits = [str(boundaries.floor_level(level, 9)) for level in pocock]
    step["facts"]["limits"] = limits
    problems = check_derivation(record)
    assert any(found in problem for problem in problems), problems
