"""Run StatClaim on the comparison designs and write statclaim_side.txt.

uv run python replication/comparison/statclaim_side.py

Needs the Lean setup (make setup) for the two-look design; the rest needs Python only.
The invalid graphs are graph.stat with one change each, so each differs from the valid
file in exactly the way the matching graphicalMCP case does.
"""

import tempfile
from pathlib import Path

from statclaim import __version__
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
GRAPH = (HERE / "graph.stat").read_text()
CASES = [
    ("graph.stat", GRAPH),
    (
        "graph.stat, a row of transitions summing to 1.3",
        GRAPH.replace("[0, 1, 0],", "[0, 7/10, 6/10],"),
    ),
    ("graph.stat, weights summing to 1.1", GRAPH.replace("[1/2, 1/2, 0]", "[3/5, 1/2, 0]")),
    (
        "graph.stat, a test passing level to itself",
        GRAPH.replace("[0, 1, 0],", "[1/5, 4/5, 0],"),
    ),
    (
        "graph.stat, one test declared at half the level",
        GRAPH.replace("value=0), alpha=1/40)", "value=0), alpha=1/80)"),
    ),
    ("sequential.stat", (HERE / "sequential.stat").read_text()),
    ("two_arm_power.stat", (HERE / "two_arm_power.stat").read_text()),
]


def main() -> int:
    lines = [f"StatClaim {__version__} on the comparison designs.", ""]
    with tempfile.TemporaryDirectory() as directory:
        for index, (name, text) in enumerate(CASES):
            source = Source(text, name.split(",")[0])
            report = check_source(source, project=ROOT, output=Path(directory) / f"case-{index}")
            rendered = render_report(report, source).splitlines()
            # Run folders and certificate paths differ on every machine.
            kept = [
                line
                for line in rendered
                if not line.startswith(("Source snapshot", "  Certificate:"))
            ]
            lines += [f"== {name}", *kept, ""]
    (HERE / "statclaim_side.txt").write_text("\n".join(lines))
    print("Wrote replication/comparison/statclaim_side.txt")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
