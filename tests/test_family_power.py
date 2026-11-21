"""Power of a family of tests by simulation: each endpoint, any, all, and the familywise
error under the global null beside the proved or cited bound."""

import copy
import json
import math
import subprocess
from fractions import Fraction
from pathlib import Path

import pytest

from statclaim import simulation as engine
from statclaim.derivation_checker import check_derivation
from statclaim.fisher import fisher_exact
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = json.loads((ROOT / "tests/fixtures/family_power_r.json").read_text())
LESSON = ROOT / "examples/tutorial/43_family_power.stat"
HEAD = (
    "use models.two_arm_binomial\nuse models.two_arm_continuous\nuse sampling\n"
    "use tests.fisher\nuse tests.t\nuse tests.survival\nuse models.two_arm_survival\n"
    "use multiplicity.bonferroni\nuse multiplicity.fixed_sequence\nuse multiplicity.graphical\n"
    "use planning\n"
    "let study = two_arm_continuous(n_control=100, n_treatment=100)\n"
    "let first = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
    "let second = t_test(design=fixed(model=study), null=equal_means(model=study), alpha=1/20)\n"
    "let ordered = fixed_sequence(analyses=[first, second], alpha=1/20)\n"
    "let graph = graphical(analyses=[first, second], alpha=1/20, weights=[1/2, 1/2], "
    "transitions=[[0, 1], [1, 0]])\n"
    "let points = endpoint_points(at=[mean_difference(value=4, sd=10), mean_difference(value=3, "
    "sd=10)], correlation=3/10)\n"
)


def _f(text):
    return float(Fraction(text))


def target(rejecting=', rejecting="any"', point="points"):
    return f"power_target(at={point}, minimum=4/5, maximum_typeI=1/20{rejecting})"


def diagnostics(text):
    return [(d.code, d.message) for d in compile_source(Source(text)).diagnostics]


def _close(ours: float, runs: int, theirs: float, their_runs: int) -> bool:
    """Within four standard errors of two independent Monte Carlo estimates."""
    p = (ours * runs + theirs * their_runs) / (runs + their_runs)
    return abs(ours - theirs) <= 4 * math.sqrt(p * (1 - p) * (1 / runs + 1 / their_runs)) + 1e-9


@pytest.fixture(autouse=True)
def no_backend(monkeypatch):
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: pytest.fail("backend invoked"))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: pytest.fail("backend invoked"))


def _endpoints(case, at_null):
    found = []
    for item in case["endpoints"]:
        member = {
            "sizes": (item["n_control"], item["n_treatment"]),
            "side": "both",
            "level": Fraction(item["alpha"]),
        }
        if item["test"] == "fisher":
            control = _f(item["p_control"])
            treatment = control if at_null else _f(item["p_treatment"])
            found.append({**member, "test": "fisher", "rates": (control, treatment)})
        else:
            difference = 0.0 if at_null else _f(item["difference"])
            found.append(
                {
                    **member,
                    "test": "student",
                    "difference": difference,
                    "sd": _f(item["sd"]),
                    "null_value": 0.0,
                }
            )
    return found


@pytest.mark.parametrize(
    "case", FIXTURE["cases"], ids=lambda c: f"{c['procedure']}-{c['correlation']}"
)
def test_rejection_rates_agree_with_a_raw_data_simulation_in_r(case):
    """R values from replication/comparison/family_power_r.R; R is not needed here."""
    graph = None
    if case["procedure"] == "graphical":
        weights = tuple(Fraction(w) for w in case["weights"])
        transitions = tuple(tuple(Fraction(g) for g in row) for row in case["transitions"])
        graph = (weights, transitions)
    runs = 10000
    for at_null, theirs in ((False, case["power"]), (True, case["null"])):
        trial = engine.family_trial(
            _endpoints(case, at_null),
            _f(case["correlation"]),
            case["procedure"],
            Fraction(case["alpha"]),
            graph,
        )
        found = engine.estimate_family(
            trial, len(case["endpoints"]), runs, engine.Stream(7, "r", at_null)
        )
        each = theirs["each"] if isinstance(theirs["each"], list) else [theirs["each"]]
        for ours, rate in zip(found.each, each, strict=True):
            assert _close(ours / runs, runs, rate, case["runs"]), (found, theirs)
        assert _close(found.any / runs, runs, theirs["any"], case["runs"])
        assert _close(found.all / runs, runs, theirs["all"], case["runs"])


def test_fisher_p_values_are_the_exact_test():
    for control, treatment, alternative in (
        (12, 25, "two_sided"),
        (5, 18, "greater"),
        (30, 30, "two_sided"),
    ):
        exact = fisher_exact(
            n_control=50,
            n_treatment=50,
            control_successes=control,
            treatment_successes=treatment,
            alternative=alternative,
        )
        assert engine.fisher_p_value(50, 50, control, treatment, alternative) == exact.p_value


def test_the_graphical_procedure_passes_level_along_the_graph():
    half, full = Fraction(1, 2), Fraction(1)
    graph = ((half, half), ((0, full), (full, 0)))
    alpha = Fraction(1, 20)
    # The first is rejected at 1/40; its level passes on, so the second is tested at 1/20.
    assert engine.graphical_rejections([0.01, 0.04], alpha, *graph) == [True, True]
    assert engine.graphical_rejections([0.03, 0.04], alpha, *graph) == [False, False]


def test_the_lesson_reports_any_and_all(tmp_path):
    text = LESSON.read_text()
    report = check_source(Source(text, LESSON.name), project=ROOT, output=tmp_path / "run")
    either, both = (r["report"]["calculation"] for r in report["requests"])
    assert [item["name"] for item in either["endpoints"]] == ["response", "symptoms"]
    assert either["rejecting"] == "any" and both["rejecting"] == "all"
    assert _f(either["power_any"]["rate"]["fraction"]) > 0.9
    assert _f(both["power_all"]["rate"]["fraction"]) < 0.7
    assert [r["report"]["decision"] for r in report["requests"]] == ["target_met", "target_not_met"]
    # Proved and cited for any dependence: reported below the bound, not judged.
    assert _f(either["typeI_upper"]["fraction"]) < 0.05 and not either["typeI_judged"]
    program = compile_source(Source(text))
    assert not program.diagnostics
    assert all(check_derivation(d.to_dict()) == [] for d in program.derivations)


@pytest.mark.parametrize("family", ["ordered", "graph"])
def test_sequences_and_graphs_are_simulated_and_checked(family, tmp_path):
    text = HEAD + (
        f"let claim = meets(analysis={family}, target={target()})\n"
        "let found = simulate(claim, seed=1, runs=2000)\n"
    )
    report = check_source(Source(text, "family.stat"), project=ROOT, output=tmp_path / "run")
    calculation = report["requests"][0]["report"]["calculation"]
    assert calculation["procedure"] == ("fixed_sequence" if family == "ordered" else "graphical")
    derivation = next(d for d in compile_source(Source(text)).derivations if d.name == "claim")
    assert check_derivation(derivation.to_dict()) == []


@pytest.mark.parametrize(
    ("line", "code", "words"),
    [
        (
            f"let p = meets(analysis=ordered, target={target(rejecting='')})",
            "planning_point",
            "any endpoint or all",
        ),
        (
            "let p = meets(analysis=ordered, target=power_target(at=mean_difference(value=4, "
            'sd=10), minimum=4/5, maximum_typeI=1/20, rejecting="any"))',
            "planning_point",
            "endpoint_points",
        ),
        (
            f"let p = meets(analysis=first, target={target()})",
            "planning_point",
            "rejecting is for a family",
        ),
        (
            f"let p = calculate(meets(analysis=ordered, target={target()}))",
            "unsupported_claim",
            "simulate",
        ),
        (
            "let other = two_arm_continuous(n_control=80, n_treatment=80)\n"
            "let third = t_test(design=fixed(model=other), null=equal_means(model=other), "
            "alpha=1/40)\n"
            "let half = t_test(design=fixed(model=study), null=equal_means(model=study), "
            "alpha=1/40)\n"
            "let mixed = bonferroni(analyses=[half, third], alpha=1/20)\n"
            f"let p = meets(analysis=mixed, target={target()})",
            "planning_point",
            "same arm sizes",
        ),
        (
            "let survival = two_arm_survival(n_control=100, n_treatment=100)\n"
            "let lr = log_rank(design=fixed(model=survival), null=equal_survival(model=survival), "
            "alpha=1/40)\n"
            "let half = t_test(design=fixed(model=study), null=equal_means(model=study), "
            "alpha=1/40)\n"
            "let mixed = bonferroni(analyses=[half, lr], alpha=1/20)\n"
            f"let p = meets(analysis=mixed, target={target()})",
            "unsupported_claim",
            "not simulated yet",
        ),
        (
            'let p = power_target(at=points, minimum=4/5, maximum_typeI=1/20, rejecting="most")',
            "domain",
            '"any" or "all"',
        ),
    ],
)
def test_refusals_explain_family_power(line, code, words):
    found = diagnostics(HEAD + line + "\n")
    assert found and found[0][0] == code and words in found[0][1], found


def test_the_checker_rejects_altered_points_and_targets():
    text = HEAD + f"let claim = meets(analysis=graph, target={target()})\n"
    derivation = next(
        d for d in compile_source(Source(text)).derivations if d.name == "claim"
    ).to_dict()
    assert check_derivation(derivation) == []
    for change in ("correlation", "rejecting", "count"):
        altered = copy.deepcopy(derivation)
        target_record = altered["subject"]["subject"]["target"]
        if change == "correlation":
            target_record["at"]["correlation"] = "1"
        elif change == "rejecting":
            target_record["rejecting"] = "most"
        else:
            target_record["at"]["endpoints"] = target_record["at"]["endpoints"][:1]
        assert check_derivation(altered), change
