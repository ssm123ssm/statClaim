"""The published evaluation matches what the software does today."""

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load():
    spec = importlib.util.spec_from_file_location("evaluate", ROOT / "replication/evaluate.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_every_scenario_behaves_as_stated_and_results_are_current():
    evaluate = load()
    rows = evaluate.run()
    assert [row["key"] for row in rows if not row["as_expected"]] == []
    assert len({row["key"] for row in rows}) == len(rows) >= 30
    assert (ROOT / "replication/results.md").read_text() == evaluate.render(rows), (
        "Rerun 'uv run python replication/evaluate.py'."
    )
    # The limits are reported, not hidden.
    outcomes = {row["outcome"] for row in rows}
    assert {"rejected", "unresolved", "calculated", "surfaced", "invisible"} == outcomes


def simon():
    import sys

    sys.path.insert(0, str(ROOT / "replication"))
    import simon as module

    return module


def test_simon_data_and_published_results_agree_with_the_software():
    import json

    module = simon()
    designs = module.DATA["designs"]
    assert len(designs) == 102 and sum(d["table"] == 1 for d in designs) == 48
    recorded = json.loads((ROOT / "replication/simon_results.json").read_text())
    assert len(recorded) == 102 and all(row["meets_targets"] for row in recorded)
    assert all(row["search_finds_same_design"] for row in recorded)
    assert sum(not row["table_values_match"] for row in recorded) == 4
    # Recompute a spread of designs; the full run is too slow for this suite.
    for index in (0, 23, 47, 71, 101):
        fresh = module.calculate(designs[index])
        for key in ("typeI", "power", "meets_targets", "expected_size", "table_values_match"):
            assert fresh[key] == recorded[index][key], (index, key)
    proofs = json.loads((ROOT / "replication/simon_proofs.json").read_text())
    assert len(proofs) == 102
    assert all(item["status"] == "verified" and item["certificate_id"] for item in proofs.values())


def replication_module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / f"replication/{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_power_cross_check_is_current_and_within_tolerance():
    power = replication_module("power")
    rows = power.run()
    assert rows and all(row["within_tolerance"] for row in rows)
    assert (ROOT / "replication/power_results.md").read_text() == power.render(rows), (
        "Rerun 'uv run python replication/power.py'."
    )


def test_every_replication_step_names_a_script_and_its_pinned_outputs():
    run = replication_module("run")
    for step in run.STEPS:
        assert (ROOT / "replication" / step.script).is_file(), step
        assert all((ROOT / "replication" / name).is_file() for name in step.outputs), step
    # A Python-only replication never needs Lean; the Lean steps are separate.
    assert any(step.lean for step in run.STEPS)
    assert {step.script for step in run.STEPS if not step.lean} >= {
        "evaluate.py",
        "simon.py",
        "power.py",
    }


def test_worked_designs_without_lean_have_their_recorded_statuses(capsys, monkeypatch):
    examples = replication_module("examples")
    monkeypatch.setattr("sys.argv", ["examples.py"])
    assert examples.main() == 0
    assert "DIFFERS" not in capsys.readouterr().out


def test_comparison_designs_compile_as_recorded():
    """The StatClaim side of the R cross-checks stays valid."""
    from statclaim.language_compiler import compile_source
    from statclaim.language_syntax import Source

    for name in ("graph.stat", "sequential.stat", "two_arm_power.stat"):
        path = ROOT / "replication/comparison" / name
        assert compile_source(Source(path.read_text(), str(path))).status == "elaborated", name


def test_copd_case_study_is_current_without_lean():
    copd = replication_module("copd")
    for name, text in copd.outputs(lean=False).items():
        assert (ROOT / "replication/copd" / name).read_text() == text, (
            f"Rerun 'uv run python replication/copd.py' ({name})."
        )
    assert "Program status: calculated" in copd.outputs(lean=False)["power_check.txt"]
