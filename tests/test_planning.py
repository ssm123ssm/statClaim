"""Exact planning calculations, language checks and unexecuted result slots."""

from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path

import pytest

from statproof.catalogue import catalogue
from statproof.design import Design
from statproof.fisher import fisher_exact
from statproof.language_compiler import compile_source
from statproof.language_runner import check_source
from statproof.language_syntax import Source
from statproof.planning import (
    BinomialInterval,
    OneSamplePlan,
    OneSampleResult,
    PowerPlan,
    TwoStagePlan,
    TwoStageRule,
    fisher_rejection_probability,
    interval_payload,
    parse_interval_payload,
    parse_planning_payload,
    parse_policy_payload,
    parse_result_payload,
    planning_payload,
    policy_payload,
    render_planning_proof,
    result_payload,
    search_equal_arms,
    search_one_sample,
    search_two_stage,
)

ROOT = Path(__file__).resolve().parents[1]
ALPHA = Fraction(1, 20)
RATES = (Fraction(1, 10), Fraction(2, 5))
HEADER = """use models.two_arm_binomial
use sampling
use tests.fisher
use planning
let study = two_arm_binomial(n_control=20, n_treatment=20)
let null = equal_proportions(model=study)
"""
FIXED = HEADER + "let analysis = fisher(design=fixed(model=study), null=null, alpha=1/20)\n"


def compiled(text: str):
    return compile_source(Source(text, "test.stat"))


def run(text: str, tmp_path):
    return check_source(Source(text, "test.stat"), project=ROOT, output=tmp_path / "run")


def binomial(n: int, k: int, p: Fraction) -> Fraction:
    return comb(n, k) * p**k * (1 - p) ** (n - k)


def test_power_matches_independent_enumeration():
    # Sum the model's point masses over tables rejected by the reference test.
    for nc, nt in ((3, 4), (7, 5), (9, 9)):
        expected = sum(
            binomial(nc, x, RATES[0]) * binomial(nt, y, RATES[1])
            for x, y in product(range(nc + 1), range(nt + 1))
            if fisher_exact(
                n_control=nc,
                n_treatment=nt,
                control_successes=x,
                treatment_successes=y,
                alpha=ALPHA,
            ).reject_null
        )
        assert fisher_rejection_probability(nc, nt, ALPHA, *RATES) == expected


def test_reference_values_and_search():
    assert float(fisher_rejection_probability(20, 20, ALPHA, *RATES)) == pytest.approx(
        0.4920329563603535, abs=1e-15
    )
    assert float(fisher_rejection_probability(35, 35, ALPHA, *RATES)) == pytest.approx(
        0.7847697628681884, abs=1e-15
    )
    plan, evaluated = search_equal_arms(ALPHA, *RATES, Fraction(4, 5), ALPHA, 2, 40)
    assert (plan.design.n_control, evaluated) == (36, 35)
    assert float(plan.power) == pytest.approx(0.8003902630552112, abs=1e-15)
    exhausted, evaluated = search_equal_arms(ALPHA, *RATES, Fraction(4, 5), ALPHA, 2, 30)
    assert exhausted is None and evaluated == 29


def test_error_under_the_null_respects_alpha():
    for rate in (Fraction(1, 10), Fraction(1, 2), Fraction(9, 10)):
        assert fisher_rejection_probability(12, 9, ALPHA, rate, rate) <= ALPHA


def test_planning_payload_round_trip_and_tampering():
    plan = PowerPlan(Design(36, 36, "fixed", ALPHA), *RATES, Fraction(4, 5), ALPHA)
    payload = planning_payload(plan)
    assert parse_planning_payload(payload) == plan
    payload["target"]["extra"] = "1"
    with pytest.raises(ValueError):
        parse_planning_payload(payload)
    with pytest.raises(ValueError):
        PowerPlan(Design(36, 36, "fixed", ALPHA), RATES[0], RATES[0], Fraction(4, 5), ALPHA)
    with pytest.raises(ValueError):
        render_planning_proof(
            PowerPlan(Design(36, 36, "fixed", ALPHA), *RATES, Fraction(4, 5), Fraction(1, 100)),
            "0" * 64,
        )


def simon(**changes) -> TwoStagePlan:
    fields = {
        "n_first": 13,
        "n_second": 30,
        "rule": TwoStageRule("threshold", 3, 12),
        "null_rate": Fraction(1, 5),
        "alternative_rate": Fraction(2, 5),
        "minimum_power": Fraction(4, 5),
        "maximum_typeI": ALPHA,
    }
    return TwoStagePlan(**{**fields, **changes})


def test_two_stage_matches_direct_enumeration():
    plan = simon()
    for rate in (plan.null_rate, plan.alternative_rate):
        expected = sum(
            binomial(13, x, rate) * binomial(30, y, rate)
            for x, y in product(range(14), range(31))
            if x > 3 and x + y > 12
        )
        assert plan.rejection_probability(rate) == expected
    values = plan.evaluate()
    assert values["typeI_target_met"] and values["power_target_met"]
    assert plan.expected_sample_size(plan.null_rate) < 43
    assert parse_policy_payload(policy_payload(plan)) == plan


def test_posterior_rule_matches_uniform_prior_closed_form():
    # Under Beta(1, 1), P(rate > x | no data) = 1 - x; after one success it is 1 - x^2.
    rule = TwoStageRule("posterior", reference=Fraction(1, 4))
    assert rule.posterior_at_least(Fraction(3, 4), 0, 0)
    assert not rule.posterior_at_least(Fraction(3, 4) + Fraction(1, 1000), 0, 0)
    assert rule.posterior_at_least(Fraction(15, 16), 1, 1)
    assert not rule.posterior_at_least(Fraction(15, 16) + Fraction(1, 1000), 1, 1)


def test_posterior_threshold_does_not_bound_error_by_itself():
    lenient = simon(
        n_first=10,
        n_second=20,
        rule=TwoStageRule(
            "posterior",
            reference=Fraction(1, 5),
            continue_at_least=Fraction(0),
            success_at_least=Fraction(1, 2),
        ),
    )
    assert lenient.rejection_probability(lenient.null_rate) > ALPHA


def test_planning_compiles_without_execution():
    compilation = compiled(
        FIXED + "let target = power_target(at=binomial_rates(p_control=1/10, p_treatment=2/5), "
        "minimum=4/5, maximum_typeI=1/20)\n"
        "let power = calculate(meets(analysis=analysis, target=target)).calculation.power\n"
        "let sizing = sample_size(candidates=equal_arm_sizes(analysis=analysis, "
        "min_per_arm=2, max_per_arm=40), target=target)\n"
        "let outcome = verify(sizing)\n"
    )
    assert compilation.status == "elaborated"
    assert [r.claim.kind for r in compilation.program.requests] == ["meets", "sample_size"]


@pytest.mark.parametrize(
    ("line", "code"),
    [
        ("let t = power_target(at=binomial_rates(p_control=1/10, p_treatment=11/10), "
         "minimum=4/5, maximum_typeI=1/20)", "domain"),
        ("let t = power_target(at=binomial_rates(p_control=1/10, p_treatment=2/5), "
         "minimum=0, maximum_typeI=1/20)", "domain"),
        ("let c = meets(analysis=analysis, target=power_target(at=binomial_rates("
         "p_control=1/5, p_treatment=1/5), minimum=4/5, maximum_typeI=1/20))",
         "alternative_in_null"),
        ("let c = equal_arm_sizes(analysis=analysis, min_per_arm=5, max_per_arm=4)", "domain"),
        ("let c = equal_arm_sizes(analysis=analysis, min_per_arm=0, max_per_arm=4)", "domain"),
        ("let c = verify(typeI(analysis))\nlet d = calculate(typeI(analysis))", "type"),
    ],
)  # fmt: skip
def test_invalid_planning_inputs(line, code):
    compilation = compiled(FIXED + line + "\n")
    assert compilation.status == "invalid"
    assert code in [d.code for d in compilation.diagnostics]


def test_wrong_planning_point_family():
    text = FIXED + (
        "use designs.two_stage\n"
        "let c = meets(analysis=analysis, target=power_target(at=response_rate(value=2/5), "
        "minimum=4/5, maximum_typeI=1/20))\n"
    )
    assert "planning_point" in [d.code for d in compiled(text).diagnostics]


def test_changed_assumptions_block_verification():
    target = (
        "let target = power_target(at=binomial_rates(p_control=1/10, p_treatment=2/5), "
        "minimum=4/5, maximum_typeI={})\n"
    )
    stricter = compiled(
        FIXED + target.format("1/100") + "verify meets(analysis=analysis, target=target)\n"
    )
    assert [d.code for d in stricter.diagnostics] == ["typeI_target_not_established"]
    adaptive = compiled(
        HEADER
        + "let analysis = fisher(design=adaptive(model=study), null=null, alpha=1/20)\n"
        + target.format("1/20")
        + "calculate meets(analysis=analysis, target=target)\n"
    )
    assert [d.code for d in adaptive.diagnostics] == ["sampling_scope"]


def test_calculation_fields_and_unmet_power(tmp_path):
    report = run(
        FIXED + "let target = power_target(at=binomial_rates(p_control=1/10, p_treatment=2/5), "
        "minimum=4/5, maximum_typeI=1/20)\n"
        "let claim = meets(analysis=analysis, target=target)\n"
        "let calculation = calculate(claim)\n"
        "let power = calculation.calculation.power\n"
        "let met = calculation.calculation.power_target_met\n"
        "let verification = verify(claim)\n"
        "let evidence = verification.evidence\n",
        tmp_path,
    )
    values = report["values"]
    assert values["calculation"]["status"] == "calculated"
    assert float(Fraction(values["power"])) == pytest.approx(0.4920329563603535, abs=1e-15)
    assert values["met"] is False
    # Unmet power is decided before Lean is involved, and leaves evidence absent.
    assert values["verification"]["status"] == "unresolved_obligation"
    assert values["evidence"] is None
    assert report["backend_invoked"] is False
    assert "power_target_not_met" in [d["code"] for d in report["diagnostics"]]


def test_exhausted_search_reports_no_candidate(tmp_path):
    report = run(
        FIXED + "let target = power_target(at=binomial_rates(p_control=1/10, p_treatment=2/5), "
        "minimum=4/5, maximum_typeI=1/20)\n"
        "let sizing = sample_size(candidates=equal_arm_sizes(analysis=analysis, "
        "min_per_arm=2, max_per_arm=30), target=target)\n"
        "let recommendation = calculate(sizing)\n"
        "let size = recommendation.calculation.n_control\n"
        "let outcome = verify(sizing)\n",
        tmp_path,
    )
    values = report["values"]
    assert values["recommendation"]["decision"] == "no_feasible_candidate"
    assert values["size"] is None
    assert values["outcome"]["evidence"] is None
    assert "no_feasible_candidate" in [d["code"] for d in report["diagnostics"]]


def test_two_stage_calculation(tmp_path):
    report = run(
        (ROOT / "examples/two_stage.stat").read_text().split("let verification")[0], tmp_path
    )
    details = report["values"]["characteristics"]["calculation"]
    assert details["typeI_target_met"] and details["power_target_met"]
    assert details["maximum_sample_size"] == 43


def test_new_objects_are_catalogued():
    data = catalogue()
    assert {"planning", "designs.two_stage"} <= {module["name"] for module in data["modules"]}
    assert {"PowerTarget", "PlanningDetails", "PolicyDetails"} <= {
        o["name"] for o in data["objects"]
    }


def one_sample(n: int = 25, **changes) -> OneSamplePlan:
    fields = {
        "n": n,
        "null_rate": Fraction(1, 5),
        "alpha": ALPHA,
        "alternative_rate": Fraction(2, 5),
        "minimum_power": Fraction(4, 5),
        "maximum_typeI": ALPHA,
    }
    return OneSamplePlan(**{**fields, **changes})


def null_tail(n: int, critical: int) -> Fraction:
    return sum(binomial(n, k, Fraction(1, 5)) for k in range(critical, n + 1))


def test_one_sample_critical_value_is_the_smallest_valid_one():
    for n in (1, 7, 25, 40):
        plan = one_sample(n)
        assert null_tail(n, plan.critical) <= ALPHA
        assert plan.critical == 0 or null_tail(n, plan.critical - 1) > ALPHA
        assert plan.rejection_probability(plan.null_rate) == null_tail(n, plan.critical)


def test_one_sample_search_and_payload():
    plan, evaluated = search_one_sample(one_sample(), 10, 60)
    assert (plan.n, plan.critical, evaluated) == (35, 12, 26)
    assert parse_policy_payload(policy_payload(plan)) == plan
    tampered = policy_payload(plan)
    tampered["design"]["critical_value"] = 11
    with pytest.raises(ValueError):
        parse_policy_payload(tampered)
    assert search_one_sample(one_sample(), 10, 20)[0] is None
    with pytest.raises(ValueError):
        one_sample(alternative_rate=Fraction(1, 10))


def test_one_sample_language(tmp_path):
    text = (
        (ROOT / "examples/one_sample.stat")
        .read_text()
        .replace("let verification = verify(sizing)\n", "")
    )
    values = run(text, tmp_path)["values"]
    assert values["recommended_n"] == 35 and values["critical_value"] == 12
    below = compiled(
        "use tests.binomial\nuse planning\n"
        "let a = binomial_test(model=one_arm_binomial(n=25), null_rate=1/5, alpha=1/20)\n"
        "let c = meets(analysis=a, target=power_target(at=response_rate(value=1/10), "
        "minimum=4/5, maximum_typeI=1/20))\n"
    )
    assert "alternative_in_null" in [d.code for d in below.diagnostics]


def test_cuts_reproduce_the_reference_rejection_region():
    from statproof.planning import fisher_cuts, fisher_rejection_region

    for nc, nt in ((3, 4), (7, 5), (9, 9)):
        region = fisher_rejection_region(nc, nt, ALPHA)
        cuts, nexts = fisher_cuts(nc, nt, ALPHA)
        assert len(cuts) == len(nexts) == nc + nt + 1
        for x, y in product(range(nc + 1), range(nt + 1)):
            reference = fisher_exact(
                n_control=nc,
                n_treatment=nt,
                control_successes=x,
                treatment_successes=y,
                alpha=ALPHA,
            ).reject_null
            assert region[x][y] == reference


def test_smallest_claim_is_bound_into_the_payload():
    plan, _ = search_equal_arms(ALPHA, *RATES, Fraction(4, 5), ALPHA, 2, 40, True)
    payload = planning_payload(plan)
    assert payload["search"]["claim"] == "smallest_in_range"
    assert parse_planning_payload(payload).minimal
    assert "checked_smaller" in render_planning_proof(plan, "0" * 64)
    sufficient, _ = search_equal_arms(ALPHA, *RATES, Fraction(4, 5), ALPHA, 2, 40)
    assert "checked_smaller" not in render_planning_proof(sufficient, "0" * 64)
    one, _ = search_one_sample(one_sample(), 10, 60, True)
    assert parse_policy_payload(policy_payload(one)).minimal


def test_one_sample_result_matches_direct_tail(tmp_path):
    result = OneSampleResult(35, Fraction(1, 5), ALPHA, 14)
    assert result.p_value == sum(binomial(35, k, Fraction(1, 5)) for k in range(14, 36))
    assert result.critical == 12 and result.reject_null
    assert not OneSampleResult(35, Fraction(1, 5), ALPHA, 11).reject_null
    # The decision agrees with comparing the p-value to alpha at every count.
    for count in range(36):
        observed = OneSampleResult(35, Fraction(1, 5), ALPHA, count)
        assert observed.reject_null == (observed.p_value <= ALPHA)
    payload = result_payload(result)
    assert parse_result_payload(payload) == result
    payload["result"]["reject_null"] = False
    with pytest.raises(ValueError):
        parse_result_payload(payload)
    text = (ROOT / "examples/one_sample_result.stat").read_text().split("let verification")[0]
    values = run(text, tmp_path)["values"]
    assert Fraction(values["p_value"]) == result.p_value
    assert values["calculation"]["decision"] == "reject_null"
    invalid = compiled(
        "use tests.binomial\n"
        "let a = binomial_test(model=one_arm_binomial(n=5), null_rate=1/5, alpha=1/20)\n"
        "let d = responses(analysis=a, count=6)\n"
    )
    assert "domain" in [d.code for d in invalid.diagnostics]


def test_interval_endpoints_bracket_the_exact_limits(tmp_path):
    level, tail = Fraction(19, 20), Fraction(1, 40)
    step = Fraction(1, 10_000)
    for n, x in ((35, 14), (20, 1), (12, 11)):
        interval = BinomialInterval(n, x, level)
        upper_tail = lambda rate: sum(binomial(n, k, rate) for k in range(x, n + 1))  # noqa: E731,B023
        lower_tail = lambda rate: sum(binomial(n, k, rate) for k in range(x + 1))  # noqa: E731,B023
        # Rejected at the endpoint, not rejected one grid step inside it.
        assert upper_tail(interval.lower) <= tail < upper_tail(interval.lower + step)
        assert lower_tail(interval.upper) <= tail < lower_tail(interval.upper - step)
    assert (BinomialInterval(35, 14, level).lower, BinomialInterval(35, 14, level).upper) == (
        Fraction(2387, 10_000),
        Fraction(5789, 10_000),
    )
    assert BinomialInterval(20, 0, level).lower == 0
    assert BinomialInterval(20, 20, level).upper == 1
    payload = interval_payload(BinomialInterval(35, 14, level))
    assert parse_interval_payload(payload) == BinomialInterval(35, 14, level)
    payload["result"]["upper"] = "1/2"
    with pytest.raises(ValueError):
        parse_interval_payload(payload)
    text = (ROOT / "examples/confidence_interval.stat").read_text().split("let verification")[0]
    values = run(text, tmp_path)["values"]
    assert (Fraction(values["lower"]), Fraction(values["upper"])) == (
        Fraction(2387, 10_000),
        Fraction(5789, 10_000),
    )
    invalid = compiled(
        "use tests.binomial\n"
        "let c = confidence_interval(model=one_arm_binomial(n=5), count=2, level=1)\n"
    )
    assert "domain" in [d.code for d in invalid.diagnostics]


def test_unequal_allocation_search():
    plan, evaluated = search_equal_arms(ALPHA, *RATES, Fraction(4, 5), ALPHA, 10, 40, True, 2)
    assert (plan.design.n_control, plan.design.n_treatment, evaluated) == (26, 52, 17)
    # Every smaller candidate was evaluated and falls short.
    for controls in range(10, 26):
        assert fisher_rejection_probability(controls, 2 * controls, ALPHA, *RATES) < Fraction(4, 5)
    payload = planning_payload(plan)
    assert payload["search"]["treatment_per_control"] == 2
    assert parse_planning_payload(payload) == plan
    assert "⟨n, 2 * n," in render_planning_proof(plan, "0" * 64)
    with pytest.raises(ValueError):
        PowerPlan(
            Design(26, 26, "fixed", ALPHA),
            *RATES,
            Fraction(4, 5),
            ALPHA,
            "sample_size",
            (10, 40),
            False,
            2,
        )
    invalid = compiled(
        FIXED + "let c = allocated_arm_sizes(analysis=analysis, min_control=1, max_control=9, "
        "treatment_per_control=0)\n"
    )
    assert "domain" in [d.code for d in invalid.diagnostics]


def test_two_stage_search_reproduces_published_simon_designs(tmp_path):
    arguments = (Fraction(1, 5), Fraction(2, 5), Fraction(4, 5), ALPHA, 45)
    optimal, _ = search_two_stage(*arguments, "optimal")
    minimax, _ = search_two_stage(*arguments, "minimax")

    def shape(plan):
        rule = plan.rule
        return (rule.continue_above, plan.n_first, rule.reject_above, plan.n_first + plan.n_second)

    assert shape(optimal) == (3, 13, 12, 43)
    assert shape(minimax) == (4, 18, 10, 33)
    assert optimal.expected_sample_size(Fraction(1, 5)) < minimax.expected_sample_size(
        Fraction(1, 5)
    )
    other, _ = search_two_stage(
        Fraction(1, 10), Fraction(3, 10), Fraction(9, 10), ALPHA, 40, "optimal"
    )
    assert shape(other) == (2, 18, 6, 35)
    assert search_two_stage(*arguments[:4], 20, "optimal")[0] is None
    text = (ROOT / "examples/two_stage_search.stat").read_text().split("# Lean checks")[0]
    values = run(text, tmp_path)["values"]
    assert (values["stage1"], values["stage2"]) == (13, 30)
    unsupported = compiled(
        "use designs.two_stage\nuse planning\n"
        "let t = power_target(at=response_rate(value=2/5), minimum=4/5, maximum_typeI=1/20)\n"
        'let c = two_stage_designs(null_rate=1/5, max_total=45, criterion="optimal")\n'
        "let s = smallest_sample_size(candidates=c, target=t)\n"
    )
    assert "unsupported_claim" in [d.code for d in unsupported.diagnostics]
