"""Searches over the sizes of a design's looks: every increasing choice of sizes on a grid,
exact for Fisher's test and simulated for t-tests, ranked by a minimax or optimal criterion."""

import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim import look_search
from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.looks_planning import fisher_looks
from statclaim.methods import boundaries

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples/look_sizes.stat"
FIXTURE = json.loads((ROOT / "tests/fixtures/look_sizes_r.json").read_text())
HEAD = """use models.two_arm_binomial
use sampling
use tests.fisher
use designs.group_sequential
use planning
let halfway = two_arm_binomial(n_control=20, n_treatment={interim_t})
let complete = two_arm_binomial(n_control=40, n_treatment={final_t})
let interim = fisher(design=fixed(model=halfway), null=equal_proportions(model=halfway),
    alpha={early})
let final = fisher(design=fixed(model=complete), null=equal_proportions(model=complete),
    alpha={late})
let trial = {design}
let target = power_target(at=binomial_rates(p_control=1/5, p_treatment=7/10), minimum=4/5,
    maximum_typeI=1/20)
"""
SPLIT = "alpha_spending(looks=[interim, final], alpha=1/20)"
POCOCK = 'group_sequential(looks=[interim, final], alpha=1/20, spending="pocock")'


def study(
    search: str, design: str = SPLIT, early="1/100", late="1/25", interim_t=20, final_t=40
) -> str:
    head = HEAD.format(design=design, early=early, late=late, interim_t=interim_t, final_t=final_t)
    return head + search + "\n"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


def calculation(text, tmp_path) -> list[dict]:
    report = check_source(Source(text), project=tmp_path, output=tmp_path / "run")
    return [request["report"] for request in report["requests"]]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def test_the_grid_lists_every_increasing_choice_of_sizes():
    assert look_search.grid(10, 50, 10) == [10, 20, 30, 40, 50]
    assert look_search.count(2, 10, 50, 10) == 10
    assert look_search.count(3, 10, 50, 10) == 10
    assert look_search.count(3, 10, 20, 10) == 0


def test_candidates_keep_the_allocation_and_take_their_own_boundaries():
    compiled = compile_source(Source(study("", POCOCK, "1/50", "1/50", 40, 80)))
    design = next(b.value for b in compiled.program.bindings if b.name == "trial")
    assert look_search.allocation(design) == 2
    listed = look_search.candidates(design, 10, 40, 10, 2)
    assert len(listed) == 6
    for looks in listed:
        assert [t for _, t, _ in looks] == [2 * c for c, _, _ in looks]
        sizes = [(c, t) for c, t, _ in looks]
        expected = boundaries.limits(sizes, Fraction(1, 20), 2, "pocock")
        assert all(
            abs(level - limit) <= Fraction(1, 10**8)
            for (*_, level), limit in zip(looks, expected, strict=True)
        )


def test_the_minimax_and_optimal_designs_are_the_best_feasible_candidates(tmp_path):
    search = (
        "let minimax = calculate(sample_size(candidates=look_sizes(design=trial, min_per_arm=10, "
        'max_per_arm=60, step=5, criterion="minimax"), target=target))\n'
        "let optimal = calculate(sample_size(candidates=look_sizes(design=trial, min_per_arm=10, "
        'max_per_arm=60, step=5, criterion="optimal"), target=target))'
    )
    minimax, optimal = calculation(study(search), tmp_path)
    # Brute force: every candidate's exact power and expected total.
    found = []
    for c1 in range(10, 61, 5):
        for c2 in range(c1 + 5, 61, 5):
            looks = [
                (c1, c1, Fraction(1, 100), "two_sided"),
                (c2, c2, Fraction(1, 25), "two_sided"),
            ]
            stopped = fisher_looks(looks, 0.2, 0.7)
            if sum(stopped) >= 0.8:
                found.append((c2, look_search.expected_total(looks, stopped), c1))
    smallest = min(final for final, _, _ in found)
    for report, best in (
        (minimax, min((f, e, c) for f, e, c in found if f == smallest)),
        (optimal, min(found, key=lambda item: (item[1], item[0], item[2]))),
    ):
        looks = report["calculation"]["looks"]
        assert [look["n_control"] for look in looks] == [best[2], best[0]]
        assert report["calculation"]["feasible"] >= 1
        assert report["decision"] == "target_met"
    assert minimax["calculation"]["candidates_evaluated"] < optimal["calculation"]["candidates"]
    assert optimal["calculation"]["candidates_evaluated"] == optimal["calculation"]["candidates"]


def test_the_search_agrees_with_an_independent_search_in_r(tmp_path):
    """R values from replication/comparison/look_sizes_r.R; R is not needed here."""
    levels = [Fraction(level) for level in FIXTURE["levels"]]
    control, treatment = (
        float(Fraction(FIXTURE["p_control"])),
        float(Fraction(FIXTURE["p_treatment"])),
    )
    for candidate in FIXTURE["candidates"]:
        n1, n2 = candidate["looks"]
        looks = [(n1, n1, levels[0], "two_sided"), (n2, n2, levels[1], "two_sided")]
        assert fisher_looks(looks, control, treatment) == pytest.approx(
            candidate["stopped"], abs=1e-12
        )
    grid = FIXTURE["grid"]
    search = "\n".join(
        f"let {criterion} = calculate(sample_size(candidates=look_sizes(design=trial, "
        f"min_per_arm={grid[0]}, max_per_arm={grid[-1]}, step={grid[1] - grid[0]}, "
        f'criterion="{criterion}"), target=target))'
        for criterion in ("minimax", "optimal")
    )
    text = study(search).replace(
        "p_control=1/5, p_treatment=7/10", "p_control=3/10, p_treatment=7/10"
    )
    for report, criterion in zip(calculation(text, tmp_path), ("minimax", "optimal"), strict=True):
        looks = report["calculation"]["looks"]
        assert [look["n_control"] for look in looks] == FIXTURE[criterion]


def test_a_search_with_no_feasible_candidate_says_so(tmp_path):
    search = (
        "let sizes = calculate(sample_size(candidates=look_sizes(design=trial, min_per_arm=5, "
        'max_per_arm=15, step=5, criterion="minimax"), target=target))'
    )
    (report,) = calculation(study(search), tmp_path)
    assert report["decision"] == "no_feasible_candidate"
    assert report["calculation"]["feasible"] == 0


def test_a_search_is_refused_where_it_does_not_apply():
    def search(arguments: str, claim: str = "sample_size") -> str:
        return (
            f"let sizes = calculate({claim}(candidates=look_sizes(design=trial, {arguments}), "
            "target=target))"
        )

    good = 'min_per_arm=10, max_per_arm=60, step=10, criterion="minimax"'
    assert diagnostics(study(search(good))) == []
    for arguments, code in (
        ('min_per_arm=10, max_per_arm=60, step=10, criterion="smallest"', "domain"),
        ('min_per_arm=10, max_per_arm=15, step=10, criterion="minimax"', "domain"),
        ('min_per_arm=1, max_per_arm=300, step=1, criterion="minimax"', "domain"),
        ('min_per_arm=10, max_per_arm=400, step=50, criterion="minimax"', "domain"),
    ):
        assert [c for c, _ in diagnostics(study(search(arguments)))] == [code], arguments
    # The ranking is a calculation: no smallest-size claim.
    found = diagnostics(study(search(good, "smallest_sample_size")))
    assert [c for c, _ in found] == ["unsupported_claim"]
    # A final look in a 3:2 allocation has no whole number of treatment per control to keep.
    uneven = study(search(good), interim_t=30, final_t=60)
    assert [c for c, _ in diagnostics(uneven)] == ["domain"]


def test_a_bound_search_is_checked_independently():
    text = study(
        "let looks = look_sizes(design=trial, min_per_arm=10, max_per_arm=60, step=10, "
        'criterion="optimal")\nlet claim = sample_size(candidates=looks, target=target)\n'
        "let sizes = calculate(claim)"
    )
    compiled = compile_source(Source(text))
    names = {d.name for d in compiled.derivations}
    assert "claim" in names
    for derivation in compiled.derivations:
        assert check_derivation(derivation.to_dict()) == [], derivation.name
    claim = next(d for d in compiled.derivations if d.name == "claim").to_dict()
    altered = claim | {"steps": [dict(step) for step in claim["steps"]]}
    for step in altered["steps"]:
        if step["rule"] == "look-candidates":
            step["facts"] = {**step["facts"], "candidates": 99}
    assert check_derivation(altered) != []


def test_the_example_searches_t_test_looks_by_simulation(tmp_path):
    reports = calculation(EXAMPLE.read_text(), tmp_path)
    searched = reports[-1]
    assert searched["decision"] == "target_met"
    looks = searched["calculation"]["looks"]
    assert looks[0]["n_control"] < looks[1]["n_control"]
    assert Fraction(searched["calculation"]["power_lower"]["fraction"]) >= Fraction(4, 5)
    assert searched["calculation"]["screened"] <= searched["calculation"]["candidates"]
