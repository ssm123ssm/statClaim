"""Power by simulation: the engine against R, the simulate(...) operation, and its results.

Reference values come from R 4.6.1: qt, pt, binom.test, power.t.test(strict = TRUE) for
Student's test, and 200,000 raw-data replicates of t.test(var.equal = FALSE) for Welch's.
"""

import math
from pathlib import Path

import pytest

from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.simulation import (
    Stream,
    clopper_pearson,
    estimate,
    t_quantile,
    t_tail,
    two_means_trial,
)

ROOT = Path(__file__).resolve().parents[1]

HEADER = """use models.two_arm_continuous
use models.two_arm_binomial
use sampling
use tests.t
use tests.fisher
use tests.logistic
use planning

let measured = two_arm_continuous(n_control=40, n_treatment=40)
let pain = t_test(design=fixed(model=measured), null=equal_means(model=measured), alpha=1/20)
let target = power_target(at=mean_difference(value=5, sd=10), minimum=4/5, maximum_typeI=1/20)
let sizes = equal_arm_sizes(analysis=pain, min_per_arm=50, max_per_arm=90)
"""


def within(found: float, expected: float, runs: int, sds: float = 4.0) -> bool:
    return abs(found - expected) <= sds * math.sqrt(expected * (1 - expected) / runs)


def run(text: str, tmp_path, name: str = "sim.stat") -> dict:
    return check_source(Source(HEADER + text, name), project=ROOT, output=tmp_path / "run")


# The engine -------------------------------------------------------------------------


def test_t_distribution_matches_r():
    quantiles = [t_quantile(0.975, df) for df in (1, 5, 38, 7.3, 200)]
    expected = [12.70620474, 2.570581836, 2.024394164, 2.345066737, 1.971896224]
    assert quantiles == pytest.approx(expected, abs=1e-8)
    assert 1 - t_tail(2.1, 5) == pytest.approx(0.9551233751, abs=1e-9)
    assert t_tail(-0.4, 12.5) == pytest.approx(0.3479539421, abs=1e-9)


def test_intervals_match_binom_test():
    assert clopper_pearson(8000, 10000) == pytest.approx((0.7920233, 0.8078016), abs=1e-7)
    assert clopper_pearson(0, 1000) == pytest.approx((0.0, 0.003682084), abs=1e-8)
    assert clopper_pearson(1000, 1000) == pytest.approx((0.9963179, 1.0), abs=1e-7)


def test_a_seed_and_label_always_give_the_same_draws():
    first, again, other = Stream(7, "search", 50, 50), Stream(7, "search", 50, 50), Stream(7, "x")
    draws = [first.uniform() for _ in range(5)]
    assert draws == [again.uniform() for _ in range(5)]
    assert draws != [other.uniform() for _ in range(5)]
    # Pinned, so a change in Python's generator or in the seeding is noticed.
    assert Stream(1, "pinned").uniform() == 0.7804278223102618


@pytest.mark.parametrize(
    ("n", "side", "alpha", "exact"),
    [
        (20, "both", 0.05, 0.3379390289),
        (64, "both", 0.05, 0.8014595579),
        (10, "higher", 0.025, 0.1838375296),
    ],
)
def test_student_power_agrees_with_power_t_test(n, side, alpha, exact):
    trial = two_means_trial(5, 10, n, n, 0, alpha, side, welch=False)
    found = estimate(trial, 200_000, Stream(2026, "student", n, side))
    assert within(found.rate, exact, found.runs)


def test_welch_power_agrees_with_raw_data_in_r():
    trial = two_means_trial(5, 10, 12, 20, 0, 0.05, "both", welch=True)
    found = estimate(trial, 200_000, Stream(2026, "welch"))
    # R: 51954 of 200,000 rejected; both estimates carry Monte Carlo error.
    assert abs(found.rate - 51954 / 200_000) <= 4 * math.sqrt(2 * 0.26 * 0.74 / 200_000)


def test_type_one_error_at_the_null_boundary_is_alpha():
    for welch in (False, True):
        trial = two_means_trial(-3, 10, 30, 30, -3, 0.025, "higher", welch=welch)
        assert within(estimate(trial, 200_000, Stream(5, welch)).rate, 0.025, 200_000)
    lower = two_means_trial(2, 10, 25, 25, 2, 0.025, "lower", welch=False)
    assert within(estimate(lower, 200_000, Stream(6)).rate, 0.025, 200_000)


# The operation ----------------------------------------------------------------------


def test_simulate_records_its_seed_and_runs():
    text = HEADER + "let estimate = simulate(meets(analysis=pain, target=target), seed=11)\n"
    compiled = compile_source(Source(text, "sim.stat"))
    assert compiled.status == "elaborated"
    (request,) = compiled.program.to_dict()["requests"]
    assert request["operation"] == "simulate"
    assert request["settings"] == {"seed": 11, "runs": 10_000}


@pytest.mark.parametrize(
    ("line", "code"),
    [
        ("simulate(typeI(pain), seed=1)", "type"),
        ("simulate(meets(analysis=pain, target=target), seed=1, runs=10)", "domain"),
        ("simulate(meets(analysis=pain, target=target), seed=-1)", "domain"),
        (
            "simulate(smallest_sample_size(candidates=equal_arm_sizes(analysis=pain, "
            "min_per_arm=2, max_per_arm=5000), target=target), seed=1, runs=200000)",
            "domain",
        ),
    ],
)
def test_simulate_refuses_what_it_cannot_do(line, code):
    compiled = compile_source(Source(HEADER + f"let x = {line}\n", "sim.stat"))
    assert compiled.status == "invalid"
    assert [d.code for d in compiled.diagnostics if d.severity == "error"] == [code]


def test_exact_and_unmodelled_tests_are_not_simulated():
    exact = """let study = two_arm_binomial(n_control=30, n_treatment=30)
let fisher_test = fisher(design=fixed(model=study), null=equal_proportions(model=study), alpha=1/20)
let rates = power_target(at=binomial_rates(p_control=1/10, p_treatment=1/2), minimum=4/5, \
maximum_typeI=1/20)
let x = simulate(meets(analysis=fisher_test, target=rates), seed=1)
"""
    compiled = compile_source(Source(HEADER + exact, "sim.stat"))
    errors = [d for d in compiled.diagnostics if d.severity == "error"]
    assert [d.code for d in errors] == ["unsupported_claim"]
    assert "exact power" in errors[0].message
    logistic = exact.replace("fisher(", "logistic_regression(")
    compiled = compile_source(Source(HEADER + logistic, "sim.stat"))
    assert [d.code for d in compiled.diagnostics if d.severity == "error"] == [
        "no_simulation_model"
    ]


# Running ----------------------------------------------------------------------------


def test_a_simulated_search_finds_a_size_and_confirms_it(tmp_path):
    report = run(
        "let sizing = simulate(smallest_sample_size(candidates=sizes, target=target), seed=3)\n"
        "let n = sizing.calculation.n_control\n"
        "let lower = sizing.calculation.power_lower\n",
        tmp_path,
    )
    (request,) = report["requests"]
    assert (report["status"], request["status"]) == ("simulated", "simulated")
    details = request["report"]
    calculation = details["calculation"]
    assert details["decision"] == "target_met"
    # power.t.test gives 63.77 per arm; requiring the interval above 4/5 adds a few.
    assert 64 <= calculation["n_control"] <= 70
    assert calculation["stream"] == "confirm" and calculation["confirmations"] >= 1
    assert float(calculation["power_lower"]["decimal_approximation"]) >= 0.8
    assert len(calculation["curve"]) == calculation["candidates_evaluated"]
    assert report["values"]["n"] == calculation["n_control"]
    assert report["values"]["lower"] == calculation["power_lower"]["fraction"]
    assert "an estimate, not evidence" in render_report(report, Source(HEADER, "sim.stat"))
    assert not report["certificate_issued"]


def test_the_same_seed_gives_the_same_result(tmp_path):
    text = "let estimate = simulate(meets(analysis=pain, target=target), seed=9, runs=2000)\n"
    first = run(text, tmp_path / "a")["requests"][0]["report"]["calculation"]
    second = run(text, tmp_path / "b")["requests"][0]["report"]["calculation"]
    assert first == second
    other = run(text.replace("seed=9", "seed=10"), tmp_path / "c")
    assert other["requests"][0]["report"]["calculation"]["power"] != first["power"]


def test_an_interval_that_includes_the_target_is_undecided(tmp_path):
    # At 64 per arm the exact power is 0.8015; 1,000 runs cannot tell it from 0.8.
    text = (
        "let close = two_arm_continuous(n_control=64, n_treatment=64)\n"
        "let near = t_test(design=fixed(model=close), null=equal_means(model=close), "
        "alpha=1/20)\n"
        "let estimate = simulate(meets(analysis=near, target=target), seed=4, runs=1000)\n"
    )
    details = run(text, tmp_path)["requests"][0]["report"]
    assert details["decision"] == "undecided"
    assert details["calculation"]["power_settled"] is False


def test_a_range_without_enough_power_finds_nothing(tmp_path):
    text = (
        "let small = equal_arm_sizes(analysis=pain, min_per_arm=10, max_per_arm=20)\n"
        "let sizing = simulate(smallest_sample_size(candidates=small, target=target), seed=1, "
        "runs=2000)\n"
    )
    details = run(text, tmp_path)["requests"][0]["report"]
    assert details["decision"] == "no_feasible_candidate"
    assert details["calculation"]["candidates_evaluated"] == 11


def test_simulations_do_not_weaken_proofs_in_the_file_status(tmp_path):
    text = (
        "let study = two_arm_binomial(n_control=30, n_treatment=30)\n"
        "let fisher_test = fisher(design=fixed(model=study), "
        "null=equal_proportions(model=study), alpha=1/20)\n"
        "let estimate = simulate(meets(analysis=pain, target=target), seed=2, runs=1000)\n"
    )
    report = run(text, tmp_path)
    assert report["status"] == "simulated"
    statuses = {r["operation"]: r["status"] for r in report["requests"]}
    assert statuses == {"simulate": "simulated"}


def test_welch_and_lower_is_better_are_simulated(tmp_path):
    text = (
        'let lower_better = two_arm_continuous(n_control=60, n_treatment=60, better="lower")\n'
        "let welch = welch_test_one_sided(design=fixed(model=lower_better), "
        "null=mean_difference_at_least(model=lower_better, value=2), alpha=1/40)\n"
        "let goal = power_target(at=mean_difference(value=-3, sd=10), minimum=4/5, "
        "maximum_typeI=1/40)\n"
        "let estimate = simulate(meets(analysis=welch, target=goal), seed=8, runs=4000)\n"
    )
    details = run(text, tmp_path)["requests"][0]["report"]
    calculation = details["calculation"]
    assert details["simulation"]["key"] == "normal_two_means_welch"
    assert calculation["scenario"].startswith("normal outcomes with standard deviation 10")
    assert within(float(calculation["typeI"]["decimal_approximation"]), 0.025, 4000)
