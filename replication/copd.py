"""Re-check the case study: the analysis plan of a confirmatory COPD trial (NCT03162055).

uv run python replication/copd.py                 # rewrite the outputs that need no Lean
uv run python replication/copd.py --check         # fail if they are out of date
uv run python replication/copd.py --lean          # rewrite the full checks, which need Lean
uv run python replication/copd.py --lean --check  # fail if they are out of date

The plan's encodings and outputs are in copd/. Without Lean, the study reports and
the power statements are compared. With Lean, so is every claim of each encoding.
"""

import sys
import tempfile
from pathlib import Path

from statclaim.contract_reports import report_markdown, study_report
from statclaim.language_compiler import compile_source
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FOLDER = HERE / "copd"
# The two encodings of the plan: as its methods are named (cited), and by name only.
ENCODINGS = ("design_cited", "design_declared")


def source(name: str) -> Source:
    path = FOLDER / f"{name}.stat"
    return Source(path.read_text(), f"replication/copd/{name}.stat")


def checked(name: str) -> str:
    """The rendered check, without run folders and certificate paths, which differ by machine."""
    with tempfile.TemporaryDirectory() as directory:
        report = check_source(source(name), project=ROOT, output=Path(directory) / name)
    lines = render_report(report, source(name)).splitlines()
    kept = [line for line in lines if not line.startswith(("Source snapshot", "  Certificate:"))]
    return "\n".join(kept) + "\n"


def reported(name: str) -> str:
    text = report_markdown(study_report(compile_source(source(name)), source(name).path))
    return text if text.endswith("\n") else text + "\n"


def outputs(lean: bool) -> dict[str, str]:
    if lean:
        return {f"{name}_check.txt": checked(name) for name in ENCODINGS}
    return {
        **{f"{name}_report.md": reported(name) for name in ENCODINGS},
        "power_check.txt": checked("power"),
    }


def main() -> int:
    expected = outputs(lean="--lean" in sys.argv)
    if "--check" in sys.argv:
        stale = [name for name, text in expected.items() if (FOLDER / name).read_text() != text]
        print(f"Out of date: {', '.join(stale)}." if stale else "The case study is current.")
        return 1 if stale else 0
    for name, text in expected.items():
        (FOLDER / name).write_text(text)
    print(f"Wrote {', '.join(expected)} to replication/copd/.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
