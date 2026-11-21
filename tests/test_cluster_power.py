"""Power of the t-test on cluster summaries: the noncentral t with the design effect."""

import copy
import json
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim.derivation_checker import check_derivation
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source
from statclaim.methods import METHODS
from statclaim.methods.power import cluster_means, cluster_proportions
from statclaim.methods.t_distribution import noncentral_t_cdf, t_cdf, t_quantile

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/cluster_power_r.json").read_text())

TRIAL = (
    "use models.two_arm_continuous\nuse models.two_arm_binomial\nuse sampling\n"
    "use tests.cluster\nuse tests.t\nuse planning\n"
    "let clinics = cluster_assignment(clusters_control=6, clusters_treatment=6, "
    "n_control=120, n_treatment=120)\n"
    "let practice = two_arm(assignment=clinics, outcome=continuous_outcome())\n"
    "let summaries = cluster_t_test(design=fixed(model=practice), "
    "null=equal_means(model=practice), alpha=1/20)\n"
    "let villages = two_arm(assignment=clinics, outcome=binary_outcome())\n"
    "let responders = cluster_proportion_t_test(design=fixed(model=villages), "
    "null=equal_proportions(model=villages), alpha=1/20)\n"
)
MEANS = "mean_difference(value=5, sd=10, icc=1/20)"
RATES = "binomial_rates(p_control=3/10, p_treatment=1/2, icc=1/50)"
NO_ICC = "mean_difference(value=5, sd=10)"
ICC_ONE = "mean_difference(value=5, sd=10, icc=1)"


def target(point=MEANS, minimum="4/5"):
    return f"power_target(at={point}, minimum={minimum}, maximum_typeI=1/20)"


def run(text, tmp_path):
    return check_source(Source(text, "clusters.stat"), project=ROOT, output=tmp_path / "run")


def compiled(text):
    return compile_source(Source(text))


def diagnostics(text):
    return [(d.code, d.message) for d in compiled(text).diagnostics]


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def _value(text):
    return float(Fraction(text))


@pytest.mark.parametrize("case", FIXTURE["means"], ids=lambda c: f"{c['k_c']}x{c['m']}")
def test_cluster_means_agree_with_r(case):
    """R values from replication/comparison/cluster_power_r.R; R is not needed here."""
    point = {
        "value": _value(case["delta"]),
        "sd": _value(case["sd"]),
        "icc": _value(case["icc"]),
        "size_control": case["m"],
        "size_treatment": case["m"],
    }
    power = cluster_means(point, case["k_c"], case["k_t"], 0, _value(case["alpha"]), "both").power
    assert power == pytest.approx(case["noncentral_t"], abs=1e-10)
    if "power_t_test" in case:
        assert power == pytest.approx(case["power_t_test"], abs=1e-10)


@pytest.mark.parametrize("case", FIXTURE["proportions"], ids=lambda c: f"{c['k_c']}x{c['m']}")
def test_cluster_proportions_agree_with_r(case):
    point = {
        "p_control": _value(case["p_c"]),
        "p_treatment": _value(case["p_t"]),
        "icc": _value(case["icc"]),
        "size_control": case["m"],
        "size_treatment": case["m"],
    }
    alpha = _value(case["alpha"])
    power = cluster_proportions(point, case["k_c"], case["k_t"], 0, alpha, "both").power
    assert power == pytest.approx(case["noncentral_t"], abs=1e-10)
    if "power_t_test" in case:
        assert power == pytest.approx(case["power_t_test"], abs=1e-10)


def _search_text(case):
    if case["kind"] == "means":
        point = f"mean_difference(value={case['delta']}, sd={case['sd']}, icc={case['icc']})"
        analysis = "summaries"
    else:
        point = (
            f"binomial_rates(p_control={case['p_c']}, p_treatment={case['p_t']}, icc={case['icc']})"
        )
        analysis = "responders"
    if case["vary"] == "clusters":
        space = (
            f"cluster_counts(analysis={analysis}, cluster_size={case['m']}, min_per_arm=4, "
            "max_per_arm=200)"
        )
    else:
        space = f"cluster_sizes(analysis={analysis}, min_size=1, max_size=500)"
    goal = f"power_target(at={point}, minimum={case['power']}, maximum_typeI={case['alpha']})"
    return (
        TRIAL + f"let sizing = calculate(smallest_sample_size(candidates={space}, target={goal}))\n"
    )


@pytest.mark.parametrize("case", FIXTURE["searches"], ids=lambda c: f"{c['kind']}-{c['vary']}")
def test_searches_find_the_size_r_finds(case, tmp_path):
    report = run(_search_text(case), tmp_path)
    calculation = report["requests"][0]["report"]["calculation"]
    if case["vary"] == "clusters":
        assert calculation["clusters_control"] == case["clusters_per_arm"]
        # The normal approximation never asks for more clusters than the noncentral t.
        assert case["crtsize"] <= case["clusters_per_arm"]
    else:
        assert calculation["cluster_size_control"]["fraction"] == str(case["cluster_size"])
    assert float(calculation["power"]["decimal_approximation"]) == pytest.approx(
        case["power_at"], abs=1e-6
    )


def test_the_t_distribution_matches_known_values():
    assert t_quantile(0.975, 10) == pytest.approx(2.228138851986273, abs=1e-12)
    assert t_cdf(0, 7) == 0.5
    assert noncentral_t_cdf(0, 5, 0) == pytest.approx(0.5)
    # With no noncentrality it is the central t; and the two tails sum to one.
    assert noncentral_t_cdf(1.3, 9, 0) == pytest.approx(t_cdf(1.3, 9), abs=1e-14)
    assert noncentral_t_cdf(-1.3, 9, 0.7) + noncentral_t_cdf(1.3, 9, -0.7) == pytest.approx(1)
    # A large noncentrality does not underflow.
    assert noncentral_t_cdf(2, 20, 60) == pytest.approx(0, abs=1e-12)
    assert noncentral_t_cdf(70, 20, 60) > 0.5


def test_both_cluster_tests_have_a_formula_at_their_outcomes_point():
    assert METHODS["cluster_t_test"].power.point == "mean_difference"
    assert METHODS["cluster_proportion_t_test"].power.point == "binomial_rates"
    for key in ("cluster_t_test", "cluster_proportion_t_test"):
        assert "noncentral t" in METHODS[key].power.approximation


def test_declared_clusters_give_power_with_the_design_effect(tmp_path):
    text = (
        TRIAL
        + f"let power = calculate(meets(analysis=summaries, target={target()}))\n"
        + "let effect = power.calculation.design_effect\n"
        + "let clinics_each = power.calculation.clusters_control\n"
    )
    report = run(text, tmp_path)
    assert report["status"] == "calculated" and not report["certificate_issued"]
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["clusters_control"] == 6 and calculation["n_control"] == 120
    assert calculation["design_effect"]["fraction"] == "39/20"
    assert calculation["degrees_of_freedom"] == 10
    assert calculation["approximation"] == "noncentral t at the planning values, not a bound"
    assert report["requests"][0]["report"]["decision"] == "target_not_met"
    assert report["values"]["effect"] == "39/20" and report["values"]["clinics_each"] == 6


def test_unequal_cluster_sizes_use_each_arms_mean(tmp_path):
    text = TRIAL.replace("n_treatment=120", "n_treatment=125") + (
        f"let power = calculate(meets(analysis=summaries, target={target()}))\n"
    )
    calculation = run(text, tmp_path)["requests"][0]["report"]["calculation"]
    assert calculation["cluster_size_treatment"]["fraction"] == "125/6"
    assert "design_effect" not in calculation  # it differs between the arms


def test_proportions_are_planned_with_icc(tmp_path):
    text = TRIAL + f"let power = calculate(meets(analysis=responders, target={target(RATES)}))\n"
    calculation = run(text, tmp_path)["requests"][0]["report"]["calculation"]
    assert float(calculation["power"]["decimal_approximation"]) == pytest.approx(
        FIXTURE["proportions"][0]["noncentral_t"], abs=1e-6
    )


def test_a_size_search_reports_the_ceiling_when_no_size_is_enough(tmp_path):
    point = "mean_difference(value=3, sd=10, icc=1/10)"
    text = TRIAL + (
        "let sizes = cluster_sizes(analysis=summaries, min_size=2, max_size=300)\n"
        f"let sizing = calculate(sample_size(candidates=sizes, target={target(point)}))\n"
        "let ceiling = sizing.calculation.power_ceiling\n"
    )
    report = run(text, tmp_path)
    details = report["requests"][0]["report"]
    assert details["decision"] == "no_feasible_candidate"
    ceiling = float(details["calculation"]["power_ceiling"]["decimal_approximation"])
    # As clusters grow, a cluster mean's variance falls to sd^2 icc.
    se = (100 * (1 / 10) * (2 / 6)) ** 0.5
    expected = cluster_means(
        {"value": 3, "sd": 10, "icc": 0.1, "size_control": 1e15, "size_treatment": 1e15},
        6,
        6,
        0,
        0.05,
        "both",
    )
    assert ceiling == pytest.approx(expected.power, abs=1e-6)
    assert expected.standard_error == pytest.approx(se)
    assert ceiling < 0.8


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = meets(analysis=summaries, target={target(NO_ICC)})",
            "planning_point",
            "icc=...",
        ),
        (
            "let p = meets(analysis=responders, "
            f"target={target('binomial_rates(p_control=3/10, p_treatment=1/2)')})",
            "planning_point",
            "icc=...",
        ),
        (
            "let s = equal_arm_sizes(analysis=summaries, min_per_arm=4, max_per_arm=40)",
            "unsupported_claim",
            "cluster_counts",
        ),
        (
            "let s = cluster_counts(analysis=summaries, cluster_size=20, min_per_arm=3, "
            "max_per_arm=40)",
            "domain",
            "at least 4 clusters",
        ),
        (
            "let s = cluster_counts(analysis=summaries, cluster_size=20, min_per_arm=4, "
            "max_per_arm=1001)",
            "domain",
            "limited to 1,000",
        ),
        (
            "let s = cluster_sizes(analysis=summaries, min_size=0, max_size=40)",
            "domain",
            "positive",
        ),
        (
            f"let v = verify(meets(analysis=summaries, target={target()}))",
            "unsupported_claim",
            "approximate calculation",
        ),
        (
            f"let p = meets(analysis=summaries, target={target(ICC_ONE)})",
            "domain",
            "icc must lie in [0, 1)",
        ),
    ],
)
def test_refusals_explain_what_a_cluster_plan_needs(line, code, words):
    found = diagnostics(TRIAL + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_icc_is_refused_for_participant_level_tests():
    text = (
        "use models.two_arm_continuous\nuse sampling\nuse tests.t\nuse planning\n"
        "let study = two_arm_continuous(n_control=50, n_treatment=50)\n"
        "let test = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
        f"let p = meets(analysis=test, target={target()})\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "leave icc out" in found[0][1]
    space = "cluster_counts(analysis=test, cluster_size=20, min_per_arm=4, max_per_arm=40)"
    found = diagnostics(text.replace(f"meets(analysis=test, target={target()})", space))
    assert found[0][0] == "unsupported_claim" and "equal_arm_sizes" in found[0][1]


def test_fishers_planning_point_refuses_icc():
    text = (
        "use models.two_arm_binomial\nuse sampling\nuse tests.fisher\nuse planning\n"
        "let study = two_arm_binomial(n_control=50, n_treatment=50)\n"
        "let test = fisher(design=fixed(model=study), "
        "null=equal_proportions(model=study), alpha=1/20)\n"
        f"let p = meets(analysis=test, target={target(RATES)})\n"
    )
    found = diagnostics(text)
    assert found[0][0] == "planning_point" and "leave icc out" in found[0][1]


def _derivation(text, name):
    return next(d for d in compiled(text).derivations if d.name == name).to_dict()


SEARCHES = {
    "counts": "cluster_counts(analysis=summaries, cluster_size=20, min_per_arm=4, max_per_arm=60)",
    "sizes": "cluster_sizes(analysis=summaries, min_size=2, max_size=500)",
}


@pytest.mark.parametrize("space", list(SEARCHES))
def test_cluster_searches_have_checked_derivations(space):
    text = (
        TRIAL
        + f"let search = smallest_sample_size(candidates={SEARCHES[space]}, target={target()})\n"
    )
    derivation = _derivation(text, "search")
    assert check_derivation(derivation) == []
    bounds = next(s for s in derivation["steps"] if s["rule"] == "search-range")["facts"]
    widened = copy.deepcopy(derivation)
    step = next(s for s in widened["steps"] if s["rule"] == "search-range")
    key = "max_clusters_per_arm" if space == "counts" else "max_cluster_size"
    assert key in bounds["search"]
    step["facts"]["search"][key] = 10**6
    assert check_derivation(widened)


def test_the_checker_requires_icc_for_a_cluster_point():
    derivation = _derivation(
        TRIAL + f"let claim = meets(analysis=summaries, target={target()})\n", "claim"
    )
    assert check_derivation(derivation) == []
    for change in ({"icc": "1"}, {"icc": None}):
        altered = copy.deepcopy(derivation)
        step = next(s for s in altered["steps"] if s["rule"] == "power-formula")
        if change["icc"] is None:
            del step["facts"]["point"]["icc"]
        else:
            step["facts"]["point"]["icc"] = change["icc"]
        assert check_derivation(altered)


def test_the_example_and_lesson_plan_cluster_trials(tmp_path):
    for path in ("examples/cluster_trial.stat", "examples/tutorial/31_cluster_power.stat"):
        program = compiled((ROOT / path).read_text())
        assert not program.diagnostics, path
        assert all(check_derivation(d.to_dict()) == [] for d in program.derivations), path
