"""Ask Lean about every program Python refuses: test 3 of docs/proposals/lean-translation.md.

uv run python scripts/check_lean_rejections.py            # ask Lean, compare with EXPECTED
uv run python scripts/check_lean_rejections.py --no-lean  # translate only

The programs are the error-injection scenarios in replication/scenarios.py that Python
rejects or leaves unresolved, and every corpus program the compiler rejects or leaves with
an open requirement on a `verify` claim. Each is elaborated with its contract checks
deferred and translated with every claim stated (`lean_translation/rejection.py`). All go
in one Lean file, one namespace each, and Lean's outcome for each must be the one
EXPECTED below. Lean accepting a program Python refuses is allowed only where EXPECTED
says why.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "replication"))
sys.path.insert(0, str(ROOT / "scripts"))

from check_lean_translation import corpus, label  # noqa: E402
from scenarios import SCENARIOS  # noqa: E402

from statclaim.language_compiler import compile_source, requirements  # noqa: E402
from statclaim.language_syntax import Source  # noqa: E402
from statclaim.lean_translation.rejection import OUTCOMES, Asked, ask, outcome  # noqa: E402

# Why Lean accepts a program Python refuses: Python's rule asks more than the claims.
DUPLICATE = (
    "The union bound holds with a test listed twice; Python's rule keeps one question from "
    "being reported as two."
)
EXPECTED: dict[str, tuple[str, str]] = {
    # Scenarios Python rejects.
    "scenario/ni_null_superiority_test": ("contract", ""),
    "scenario/equality_null_one_sided_test": ("contract", ""),
    "scenario/nonzero_difference_fisher": ("contract", ""),
    "scenario/null_from_another_study": ("ill_typed", ""),
    "scenario/binary_test_continuous_outcome": ("untyped", ""),
    "scenario/survival_test_continuous_outcome": ("untyped", ""),
    "scenario/looks_out_of_order": ("contract", ""),
    "scenario/looks_change_the_test": ("contract", ""),
    "scenario/result_feeds_design": ("untyped", ""),
    "scenario/duplicate_endpoint": ("accepted", DUPLICATE),
    "scenario/sequence_with_split_levels": ("contract", ""),
    "scenario/familywise_claim_on_looks": ("untyped", ""),
    "scenario/same_outcome_declared_twice": ("accepted", DUPLICATE),
    "scenario/graph_shares_exceed_whole": ("contract", ""),
    "scenario/graph_recycles_to_itself": ("contract", ""),
    "scenario/planning_point_in_null": (
        "accepted",
        "The point is used by a calculation, which states nothing in Lean.",
    ),
    "scenario/level_of_zero": ("contract", ""),
    "scenario/one_participant_per_arm": ("contract", ""),
    "scenario/more_events_than_participants": (
        "accepted",
        "Observed counts enter Lean only with the result claim that reads them; none is made.",
    ),
    "scenario/risk_margin_logistic": ("contract", ""),
    "scenario/lower_is_better_wrong_way": (
        "accepted",
        "The guarantee holds for the null as stated; which direction is better is the "
        "reader's question, which Lean's models do not record.",
    ),
    "scenario/repeated_measures_declared": ("contract", ""),
    "scenario/cluster_randomised_declared": ("contract", ""),
    "scenario/cluster_summaries_on_participants": ("untyped", ""),
    "scenario/per_protocol_population": ("untyped", ""),
    # Scenarios Python leaves with an open requirement.
    "scenario/optional_stopping_exact": ("refuted", ""),
    "scenario/optional_stopping_cited": ("refuted", ""),
    "scenario/looks_at_full_level": ("unproved", ""),
    "scenario/ten_endpoints_at_five_percent": ("unproved", ""),
    "scenario/target_stricter_than_level": ("unproved", ""),
    # Corpus programs.
    "examples/adaptive.stat": ("refuted", ""),
    "examples/hypothesis_inequality.stat": ("contract", ""),
    "examples/hypothesis_mismatch.stat": ("contract", ""),
    "examples/overallocated.stat": ("unproved", ""),
    "examples/paper/fisher_adaptive.stat": ("refuted", ""),
    "examples/tutorial/03_optional_stopping.stat": ("refuted", ""),
    "examples/tutorial/03_wrong_null.stat": ("contract", ""),
    "examples/tutorial/06_changed_levels.stat": ("unproved", ""),
}


def refused_programs() -> dict[str, str]:
    """Every program Python rejects or leaves with an open requirement, by label."""
    found = {
        f"scenario/{s.key}": s.source for s in SCENARIOS if s.expected in ("rejected", "unresolved")
    }
    for path in corpus():
        text = path.read_text(encoding="utf-8")
        compilation = compile_source(Source(text, str(path)))
        program = compilation.program
        if compilation.status == "invalid" or any(
            requirements(program, request)
            for request in program.requests
            if request.operation == "verify"
        ):
            found[label(path)] = text
    return found


def namespace(key: str) -> str:
    return "StatClaimRefused." + ".".join(f"«{part}»" for part in key.split("/"))


def asked_all() -> dict[str, Asked]:
    return {key: ask(Source(text, f"{key}.stat"), key) for key, text in refused_programs().items()}


def run_lean(asked: dict[str, Asked]) -> dict[str, list[int]]:
    """Ask Lean about every typed program at once: the lines of each translation where
    Lean reports an error."""
    lines = ["import StatClaim", ""]
    starts: list[tuple[int, str]] = []
    for key, item in asked.items():
        if not item.lean:
            continue
        lines += [f"namespace {namespace(key)}", ""]
        starts.append((len(lines) + 1, key))
        lines += item.lean.splitlines()
        lines += ["", f"end {namespace(key)}", ""]
    errors: dict[str, list[int]] = {key: [] for _, key in starts}
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Refused.lean"
        path.write_text("\n".join(lines) + "\n")
        run = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True
        )
    for line in (run.stdout + run.stderr).splitlines():
        found = re.match(rf"{re.escape(str(path))}:(\d+):\d+: error", line)
        if not found:
            continue
        number = int(found.group(1))
        start, key = max((s for s in starts if s[0] <= number), default=(0, ""))
        if key:
            errors[key].append(number - start + 1)
        else:
            raise SystemExit(f"Lean failed outside the programs:\n{run.stdout}{run.stderr}")
    return errors


def main() -> int:
    asked = asked_all()
    missing = sorted(set(asked) - set(EXPECTED))
    stale = sorted(set(EXPECTED) - set(asked))
    problems = [f"{key}: no expected outcome; add it to EXPECTED" for key in missing]
    problems += [f"{key}: Python no longer refuses it; remove it from EXPECTED" for key in stale]
    for key, (expected, reason) in EXPECTED.items():
        if expected not in OUTCOMES:
            problems.append(f"{key}: unknown outcome {expected}")
        if (expected == "accepted") != bool(reason):
            problems.append(f"{key}: give a reason exactly when Lean accepts the program")
    typed = sum(bool(item.lean) for item in asked.values())
    print(f"Asked {len(asked)} programs Python refuses; {typed} translate.")
    if "--no-lean" in sys.argv:
        for key, item in asked.items():
            if (item.denotation is None) != (EXPECTED.get(key, ("",))[0] == "untyped"):
                problems.append(f"{key}: typed program expected only when the outcome needs Lean")
    else:
        errors = run_lean(asked)
        tally: dict[str, int] = {}
        for key, item in asked.items():
            found = outcome(item, errors.get(key, []))
            tally[found] = tally.get(found, 0) + 1
            expected = EXPECTED.get(key, ("?", ""))[0]
            print(f"  {found:<10} {key}: Python {', '.join(item.refused)}")
            if found != expected:
                problems.append(f"{key}: Lean's outcome is {found}, expected {expected}")
        print("Outcomes: " + ", ".join(f"{name} {tally.get(name, 0)}" for name in OUTCOMES))
    if problems:
        print(f"{len(problems)} problems:")
        print("\n".join(problems))
        return 1
    print("Lean refuses, or the table says why it accepts, every program Python refuses.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
