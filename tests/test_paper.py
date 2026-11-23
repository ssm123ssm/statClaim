"""The programs the StatClaim article shows give the numbers it reports.

The article links each program in examples/paper/ by name (?open=paper/<file> in the web
studio), so these files must keep their names. replication/examples.py checks their statuses,
with Lean for the proofs.
"""

from pathlib import Path

import pytest

from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "examples/paper"
# Links printed in the article. Renaming one of these files breaks a published link.
LINKED = (
    "composed_model",
    "fisher_adaptive",
    "fisher_design",
    "fisher_observed",
    "fisher_sample_size",
    "response_rate_precision",
    "simon_design",
    "simon_search",
    "t_test_simulation",
)


def run(name, tmp_path):
    path = PAPER / f"{name}.stat"
    return check_source(
        Source(path.read_text(), str(path)),
        project=ROOT,
        output=tmp_path / name,
        operations=("calculate", "simulate"),
    )


def calculation(report, name):
    request_id = report["values"][name]["request_id"]
    return report["requests"][request_id - 1]["report"]["calculation"]


def test_every_linked_program_is_there():
    assert sorted(path.stem for path in PAPER.glob("*.stat")) == sorted(LINKED)


def test_unspecified_stopping_leaves_the_guarantee_open():
    path = PAPER / "fisher_adaptive.stat"
    compiled = compile_source(Source(path.read_text(), str(path)))
    assert [d.code for d in compiled.diagnostics] == ["sampling_scope"]
    assert "not evidence of inflated error" in compiled.diagnostics[0].message


@pytest.mark.parametrize(
    ("name", "status"),
    [
        ("fisher_sample_size", "calculated"),
        ("simon_search", "calculated"),
        ("response_rate_precision", "calculated"),
        ("t_test_simulation", "simulated"),
    ],
)
def test_calculations_run_without_lean(name, status, tmp_path):
    report = run(name, tmp_path)
    assert report["status"] in (status, "unresolved_obligation")
    assert {r["value"]["status"] for r in report["requests"]} <= {
        "calculated",
        "simulated",
        "not_executed",
    }


def test_the_smallest_fisher_size_is_36_per_arm(tmp_path):
    report = run("fisher_sample_size", tmp_path)
    found = calculation(report, "recommendation")
    assert (found["n_control"], found["n_treatment"]) == (36, 36)


def test_the_searches_find_simons_optimal_and_minimax_designs(tmp_path):
    report = run("simon_search", tmp_path)
    for name, design, expected_size in (
        ("optimal", (9, 15, 0, 2), 14.546),
        ("minimax", (13, 7, 0, 2), 16.407),
    ):
        found = calculation(report, name)
        keys = ("n_stage1", "n_stage2", "continue_above", "reject_above")
        assert tuple(found[key] for key in keys) == design
        expected = found["expected_sample_size_null"]
        assert round(expected["numerator"] / expected["denominator"], 3) == expected_size
