"""Translate every .stat program in the corpus to Lean, and check the result with Lean.

uv run python scripts/check_lean_translation.py            # translate, then check with Lean
uv run python scripts/check_lean_translation.py --no-lean  # translate only
uv run python scripts/check_lean_translation.py --update   # rewrite the pinned translations

Part 3 of docs/proposals/lean-translation.md. The corpus is every example, lesson and
article program in examples/ and every replication study in replication/*/. All programs
go in one Lean file, one namespace each, so Mathlib is imported once. A program the
compiler rejects is not translated; its rejection is checked separately.

Lean also lists the premises each claim's proof uses. The grade they give must equal the
grade the translator expects and the status Python reports for the claim (`best_status`).
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

from statclaim.language_compiler import compile_source
from statclaim.language_inspection import best_status
from statclaim.language_syntax import Source
from statclaim.language_values import STATUS_GRADES
from statclaim.lean_translation.grades import grade
from statclaim.lean_translation.program import Translation, translate

ROOT = Path(__file__).resolve().parents[1]
PINNED_DIRECTORY = ROOT / "tests/fixtures/lean_translation"
# Translations reviewed as diffs: an exact test, cited tests of both scopes, a declared
# test, a design whose stopping rule leaves its claim unresolved, a cited test of
# association in a survey, a family of a proved and a cited test, a fixed sequence and
# a design with two looks.
PINNED = (
    "examples/paper/fisher_design.stat",
    "examples/t_test.stat",
    "examples/declared_test.stat",
    "examples/paper/fisher_adaptive.stat",
    "examples/complex_survey.stat",
    "examples/mixed_endpoints.stat",
    "examples/trial_models.stat",
    "replication/comparison/sequential.stat",
)


def corpus() -> list[Path]:
    return sorted([*(ROOT / "examples").rglob("*.stat"), *(ROOT / "replication").glob("*/*.stat")])


def namespace(path: Path) -> str:
    parts = path.relative_to(ROOT).with_suffix("").parts
    return "StatClaimProgram." + ".".join(f"«{part}»" for part in parts)


def label(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def compiled(path: Path):
    """The compiled program, or None when the compiler rejects it."""
    result = compile_source(Source(path.read_text(encoding="utf-8"), str(path)))
    return None if result.status == "invalid" else result.program


def translation(path: Path) -> Translation | None:
    """The program's translation, or None when the compiler rejects it."""
    program = compiled(path)
    return None if program is None else translate(program, label(path))


def python_grade(path: Path, request_id: int) -> str:
    """The grade Python's best status for the claim corresponds to."""
    program = compiled(path)
    assert program is not None
    return STATUS_GRADES[best_status(program.requests[request_id - 1].claim)]


def grade_problems(results: dict[str, tuple[Path, Translation]], output: str) -> list[str]:
    """Claims whose grade from Lean's dependencies differs from what is expected."""
    used: dict[tuple[str, str], list[str]] = {}
    for line in output.splitlines():
        found = re.search(r"STATCLAIM_PREMISES (\S+) (\S+): (.*)$", line)
        if found:
            premises = [name for name in found.group(3).strip().split(",") if name]
            used[(found.group(1), found.group(2))] = premises
    problems = []
    for name, (path, result) in results.items():
        for claim, expected in result.claims.items():
            if (name, claim) not in used:
                problems.append(f"{name} {claim}: Lean listed no premises")
                continue
            from_lean = grade(result.owns[claim], used[(name, claim)])
            from_python = python_grade(path, result.requests[claim])
            if not from_lean == expected == from_python:
                problems.append(
                    f"{name} {claim}: Lean's premises give {from_lean}, the translator "
                    f"expects {expected}, Python reports {from_python}"
                )
    return problems


def block(path: Path, result: Translation) -> str:
    name = namespace(path)
    return f"namespace {name}\n\n{result.lean}\nend {name}\n"


def pinned(path: str) -> Path:
    return PINNED_DIRECTORY / (Path(path).with_suffix("").as_posix().replace("/", "__") + ".lean")


def main() -> int:
    blocks, claims, skipped, rejected = [], 0, 0, 0
    results: dict[str, tuple[Path, Translation]] = {}
    for path in corpus():
        result = translation(path)
        if result is None:
            rejected += 1
            continue
        results[label(path)] = (path, result)
        blocks.append(block(path, result))
        claims += len(result.claims)
        skipped += len(result.skipped)
    print(
        f"Translated {len(blocks)} programs with {claims} claims; {skipped} declarations or "
        f"claims not translated yet; {rejected} programs the compiler rejects."
    )
    if "--update" in sys.argv:
        PINNED_DIRECTORY.mkdir(parents=True, exist_ok=True)
        for path in PINNED:
            result = translation(ROOT / path)
            assert result is not None, path
            pinned(path).write_text(result.lean)
        print(f"Wrote {len(PINNED)} pinned translations to {PINNED_DIRECTORY.relative_to(ROOT)}")
    if "--no-lean" in sys.argv:
        return 0
    with tempfile.TemporaryDirectory() as directory:
        corpus_file = Path(directory) / "Corpus.lean"
        corpus_file.write_text("import StatClaim\n\n" + "\n".join(blocks))
        run = subprocess.run(
            ["lake", "env", "lean", str(corpus_file)], cwd=ROOT, capture_output=True, text=True
        )
    if run.returncode != 0:
        lines = (run.stdout + run.stderr).splitlines()
        errors = [line for line in lines if re.search(r":\d+:\d+: error", line)]
        print(f"Lean rejected the translated corpus ({len(errors)} errors):")
        print("\n".join(lines[:60]))
        return 1
    print("Lean accepted every translated program.")
    problems = grade_problems(results, run.stdout + run.stderr)
    if problems:
        print(f"{len(problems)} claims have grades that disagree:")
        print("\n".join(problems))
        return 1
    print(f"Every claim's grade from Lean's dependencies agrees with Python ({claims} claims).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
