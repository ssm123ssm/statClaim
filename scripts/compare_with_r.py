"""Compare all small tables and selected larger tables with R's fisher.test.

Run with `uv run --locked python scripts/compare_with_r.py` (requires Rscript).
Use --write-fixtures to regenerate the compact, offline reference fixture.
"""

import argparse
import csv
import io
import json
import math
import shutil
import subprocess
from pathlib import Path

from statproof.fisher import fisher_exact

R_CODE = """
args <- commandArgs(trailingOnly = TRUE)
cases <- read.csv(args[1])
values <- apply(cases, 1, function(z) {
  tab <- matrix(c(z[3], z[1] - z[3], z[4], z[2] - z[4]), nrow=2, byrow=TRUE)
  fisher.test(tab, alternative="two.sided", conf.int=FALSE)$p.value
})
options(digits=17)
write.table(data.frame(cases, p_value=values), stdout(), sep=",", row.names=FALSE)
"""

SELECTED_CASES = [
    (4, 4, 3, 1),
    (10, 14, 1, 11),
    (17, 13, 2, 10),
    (1, 19, 0, 19),
    (100, 100, 10, 25),
    (100, 100, 50, 50),
    (100, 100, 0, 100),
    (500, 600, 15, 35),
    (50, 1000, 0, 30),
    (100, 150, 100, 150),
]
FIELDS = ["n_control", "n_treatment", "control_successes", "treatment_successes"]


def main() -> None:
    import tempfile

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-fixtures", action="store_true")
    options = parser.parse_args()
    if not shutil.which("Rscript"):
        raise SystemExit("Rscript is required for the optional external reference comparison.")
    small = [
        (nc, nt, xc, xt)
        for nc in range(1, 9)
        for nt in range(1, 9)
        for xc in range(nc + 1)
        for xt in range(nt + 1)
    ]
    cases = list(dict.fromkeys([*small, *SELECTED_CASES]))
    with tempfile.TemporaryDirectory() as directory:
        case_path = Path(directory) / "cases.csv"
        with case_path.open("w", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerow(FIELDS)
            writer.writerows(cases)
        completed = subprocess.run(
            ["Rscript", "--vanilla", "-e", R_CODE, str(case_path)],
            text=True,
            capture_output=True,
            check=True,
            timeout=120,
        )
    selected = []
    rows = list(csv.DictReader(io.StringIO(completed.stdout)))
    if len(rows) != len(cases):
        raise SystemExit("R returned an unexpected number of comparisons.")
    for row in rows:
        inputs = {name: int(row[name]) for name in FIELDS}
        expected = float(row["p_value"])
        observed = float(fisher_exact(**inputs).p_value)
        if not math.isclose(observed, expected, rel_tol=1e-10, abs_tol=0):
            raise SystemExit(f"Reference mismatch for {inputs}: Python={observed}, R={expected}")
        if tuple(inputs.values()) in SELECTED_CASES:
            selected.append({"inputs": inputs, "p_value": expected})
    print(f"Matched R fisher.test on {len(rows)} tables (relative tolerance 1e-10).")
    if options.write_fixtures:
        version = subprocess.run(
            ["Rscript", "--version"],
            text=True,
            capture_output=True,
            check=True,
            timeout=10,
        )
        fixture = {
            "reference": "stats::fisher.test(alternative='two.sided', conf.int=FALSE)",
            "r_version": (version.stdout + version.stderr).strip(),
            "regenerate": "uv run --locked python scripts/compare_with_r.py --write-fixtures",
            "cases": selected,
        }
        target = Path(__file__).resolve().parents[1] / "tests/fixtures/fisher_r.json"
        target.parent.mkdir(exist_ok=True)
        target.write_text(json.dumps(fixture, indent=2) + "\n")
        print(f"Wrote {len(selected)} reference fixtures.")


if __name__ == "__main__":
    main()
