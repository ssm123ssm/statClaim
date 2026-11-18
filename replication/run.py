"""Replicate the published results from a clean checkout. Each step checks a pinned output.

uv run python replication/run.py           # Python only; make replicate
uv run python replication/run.py --lean    # also re-prove in Lean; make replicate-lean
uv run python replication/run.py --update  # regenerate the pinned outputs; make replicate-update

Every step runs even if an earlier one fails. The run fails if any step does.
"""

import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Step:
    title: str
    script: str
    arguments: tuple[str, ...] = ()
    # The pinned outputs it compares against, and rewrites with --update. Empty for a
    # step whose expected results are written in the script itself.
    outputs: tuple[str, ...] = ()
    lean: bool = False


# To add a case study, add one Step whose script supports --check.
STEPS = (
    Step("Error-injection evaluation", "evaluate.py", outputs=("results.md", "results.json")),
    Step(
        "Simon (1989): exact values and optimality",
        "simon.py",
        outputs=("simon_results.md", "simon_results.json"),
    ),
    Step("Power for cited tests against base R", "power.py", outputs=("power_results.md",)),
    Step("Worked designs without Lean", "examples.py"),
    Step("Simon (1989): every design proved again in Lean", "simon.py", ("--fresh",), lean=True),
    Step("Worked designs with Lean", "examples.py", ("--lean",), lean=True),
)


def command(step: Step, update: bool) -> list[str]:
    mode = () if update else ("--check",) if step.outputs else ()
    return [sys.executable, str(HERE / step.script), *step.arguments, *mode]


def main() -> int:
    update, lean = "--update" in sys.argv, "--lean" in sys.argv
    if update and lean:
        print("--update regenerates the Python outputs only; run --lean separately.")
        return 2
    steps = [s for s in STEPS if (s.outputs if update else lean or not s.lean)]
    failed, start = [], time.monotonic()
    for step in steps:
        print(f"== {step.title}", flush=True)
        began = time.monotonic()
        code = subprocess.run(command(step, update), cwd=HERE.parent).returncode
        elapsed = time.monotonic() - began
        print(f"== {'ok' if code == 0 else 'FAILED'} in {elapsed:.0f} s\n", flush=True)
        if code:
            failed.append(step.title)
    print(f"Total {time.monotonic() - start:.0f} s.")
    if failed:
        print(f"Failed: {'; '.join(failed)}")
        return 1
    print("Every step matches its pinned results." if not update else "Outputs regenerated.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
