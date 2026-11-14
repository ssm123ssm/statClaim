import json
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path

import pytest

from statproof.fisher import ALPHA, fisher_exact, fraction_record


def compute(n_control, n_treatment, control_successes, treatment_successes):
    return fisher_exact(
        n_control=n_control,
        n_treatment=n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
    )


@pytest.mark.parametrize("n_control,n_treatment", list(product(range(1, 9), repeat=2)))
def test_all_small_tables_against_direct_combinatorics_and_conditional_bound(
    n_control, n_treatment
):
    # Independent direct combination products check the neighboring-weight
    # recurrence. Each possible table for these arm sizes is visited exactly once.
    for total in range(n_control + n_treatment + 1):
        lower, upper = max(0, total - n_treatment), min(n_control, total)
        masses = {
            k: Fraction(
                comb(n_control, k) * comb(n_treatment, total - k),
                comb(n_control + n_treatment, total),
            )
            for k in range(lower, upper + 1)
        }
        assert sum(masses.values()) == 1
        rejected_mass = Fraction(0)
        for observed, mass in masses.items():
            expected = sum((p for p in masses.values() if p <= mass), Fraction(0))
            result = compute(n_control, n_treatment, observed, total - observed)
            assert result.observed_table_probability == mass
            assert result.p_value == expected
            assert 0 < result.p_value <= 1
            assert (result.support_min, result.support_max) == (lower, upper)
            if result.reject_null:
                rejected_mass += mass
        # Exhaustive exact evidence for these finite examples, not a proof for
        # all designs or for the binomial conditioning argument.
        assert rejected_mass <= ALPHA


@pytest.mark.parametrize(
    "nc,nt,xc,xt,expected",
    [
        (4, 4, 3, 1, Fraction(17, 35)),
        (10, 14, 1, 11, Fraction(41, 14858)),
        (2, 2, 0, 2, Fraction(1, 3)),
        (1, 1, 0, 1, Fraction(1)),
        (10, 15, 0, 0, Fraction(1)),
        (10, 15, 10, 15, Fraction(1)),
        (100, 100, 50, 50, Fraction(1)),
    ],
)
def test_exact_examples_and_degenerate_margins(nc, nt, xc, xt, expected):
    assert compute(nc, nt, xc, xt).p_value == expected


@pytest.mark.parametrize("nc,nt,xc,xt", [(10, 14, 1, 11), (4, 9, 0, 3), (12, 7, 8, 2)])
def test_row_and_outcome_swaps_preserve_two_sided_value(nc, nt, xc, xt):
    p_value = compute(nc, nt, xc, xt).p_value
    assert compute(nt, nc, xt, xc).p_value == p_value
    assert compute(nc, nt, nc - xc, nt - xt).p_value == p_value


def test_ties_are_included_exactly():
    # Equal-probability opposite tails both contribute, not just one tail.
    result = compute(4, 4, 0, 4)
    assert result.p_value == 2 * result.observed_table_probability == Fraction(1, 35)


def test_rejection_includes_the_exact_threshold():
    result = compute(1, 19, 0, 19)
    assert result.p_value == ALPHA
    assert result.reject_null


def test_extreme_tail_is_exact_even_below_float_range():
    result = compute(1000, 1000, 0, 1000)
    assert result.p_value == Fraction(2, comb(2000, 1000))
    assert result.p_value > 0
    assert result.reject_null
    assert fraction_record(result.p_value)["decimal_approximation"] != "0"


@pytest.mark.parametrize(
    "field,value",
    [
        ("n_control", 0),
        ("n_treatment", -1),
        ("n_control", True),
        ("n_treatment", 1.5),
        ("control_successes", -1),
        ("treatment_successes", 11),
        ("control_successes", True),
        ("treatment_successes", 0.5),
        ("control_successes", "2"),
    ],
)
def test_invalid_api_inputs(field, value):
    arguments = dict(n_control=10, n_treatment=10, control_successes=1, treatment_successes=2)
    arguments[field] = value
    with pytest.raises(ValueError):
        fisher_exact(**arguments)


def test_stored_r_reference_values():
    fixture = json.loads((Path(__file__).parent / "fixtures/fisher_r.json").read_text())
    for case in fixture["cases"]:
        result = fisher_exact(**case["inputs"])
        assert float(result.p_value) == pytest.approx(case["p_value"], rel=1e-10, abs=0)
