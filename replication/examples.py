"""Run the worked designs and compare each status with the one recorded here.

uv run python replication/examples.py          # the designs that need no Lean
uv run python replication/examples.py --lean   # the designs that need Lean

A status that differs, for the file or for any request, fails the run.
"""

import sys
import tempfile
from pathlib import Path

from statclaim.language_runner import check_source
from statclaim.language_syntax import Source

ROOT = Path(__file__).resolve().parents[1]

# (file, needs Lean, file status, status of each request in order)
EXAMPLES = (
    ("examples/tutorial/12_continuous_outcome.stat", False, "cited", ("cited", "cited")),
    ("examples/cited_power.stat", False, "calculated", ("calculated",) * 4),
    (
        "examples/confirmatory_trial.stat",
        True,
        "cited",
        ("conditional", "conditional", "verified"),
    ),
    ("examples/mixed_endpoints.stat", True, "cited", ("conditional", "verified")),
    ("examples/tutorial/11_bayesian_rule.stat", True, "verified", ("calculated", "verified")),
    ("examples/randomisation.stat", True, "verified", ("verified", "verified")),
    ("examples/cluster_trial.stat", True, "cited", ("cited", "verified")),
    ("examples/stratified_randomisation.stat", True, "verified", ("verified", "verified")),
    ("examples/randomisation_family.stat", True, "conditional", ("conditional", "verified")),
    ("examples/analysis_population.stat", True, "verified", ("verified", "verified")),
)


def main() -> int:
    lean = "--lean" in sys.argv
    failed = []
    with tempfile.TemporaryDirectory() as directory:
        for index, (name, needs_lean, status, requests) in enumerate(EXAMPLES):
            if needs_lean != lean:
                continue
            path = ROOT / name
            report = check_source(
                Source(path.read_text(), str(path)),
                project=ROOT,
                output=Path(directory) / f"example-{index}",
            )
            found = tuple(request["value"]["status"] for request in report["requests"])
            ok = report["status"] == status and found == requests
            print(f"{'ok' if ok else 'DIFFERS'}: {name}: {report['status']} {list(found)}")
            if not ok:
                failed.append(name)
    if failed:
        print(f"Statuses differ from those recorded: {', '.join(failed)}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
