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
