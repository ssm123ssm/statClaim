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

Each exact test's claim must imply the statement its certificate template checks for
`verify` today (test 5 of the proposal): the template's body is placed beside the program,
and an `example` derives the template's theorem from the program's claim.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

from statclaim.language import ComposedFamilyIR
from statclaim.language_compiler import compile_source
from statclaim.language_inspection import best_status
from statclaim.language_syntax import Source
from statclaim.language_values import STATUS_GRADES
from statclaim.lean_translation.denote import Claim, denote
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.exact import ExactAnalysis
from statclaim.lean_translation.grades import grade
from statclaim.lean_translation.program import Translation, translate
from statclaim.lean_translation.prove import DEEP, projection, template, template_body

ROOT = Path(__file__).resolve().parents[1]
PINNED_DIRECTORY = ROOT / "tests/fixtures/lean_translation"
# Translations reviewed as diffs: an exact test, cited tests of both scopes, a declared
# test, a design whose stopping rule leaves its claim unresolved, a cited test of
# association in a survey, a family of a proved and a cited test, a fixed sequence, a
# design with two looks, a graphical procedure, the COPD hierarchy, which nests a graph
# in a sequence, exact tests (one-sided Fisher, association with fixed groups,
# randomisation), a result for observed counts and an interval.
PINNED = (
    "examples/paper/fisher_design.stat",
    "examples/t_test.stat",
    "examples/declared_test.stat",
    "examples/paper/fisher_adaptive.stat",
    "examples/complex_survey.stat",
    "examples/mixed_endpoints.stat",
    "examples/trial_models.stat",
    "replication/comparison/sequential.stat",
    "examples/recycling.stat",
    "replication/copd/design_cited.stat",
    "examples/one_sided.stat",
    "examples/case_control.stat",
    "examples/randomisation.stat",
    "examples/fisher_result.stat",
    "examples/difference_interval.stat",
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


def python_catches_up(path: Path, request_id: int) -> bool:
    """A combination whose members are all proved: Lean proves it outright, and Python will
    report it as proved once verify issues certificates from translated programs
    (milestone 6). Until then Python reports it as conditional, which never overstates."""
    program = compiled(path)
    assert program is not None
    return isinstance(program.requests[request_id - 1].claim.subject, ComposedFamilyIR)


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
            catching_up = (from_lean, from_python) == ("proved", "conditional") and (
                python_catches_up(path, result.requests[claim])
            )
            if not (from_lean == expected and (from_python == from_lean or catching_up)):
                problems.append(
                    f"{name} {claim}: Lean's premises give {from_lean}, the translator "
                    f"expects {expected}, Python reports {from_python}"
                )
    return problems


def equivalence(claim: Claim) -> str:
    """An `example` deriving the template's theorem from the program's claim."""
    space, name = f"template_{claim.name}", lean(claim.name)
    if claim.result is not None:
        # Each part of a result is the theorem of the same name in its template.
        parts = claim.result.parts
        text = template(claim.result.kind, claim.result.source)
        examples = [
            f"{DEEP}\nexample (i : Instance) (premises : Premises i) :\n"
            f"    type_of% @{space}.checked_{part} :=\n"
            f"  ({name} i premises){projection(index, len(parts))}\n"
            for index, (part, _) in enumerate(parts)
        ]
        return "\n".join(
            [f"namespace {space}", "", template_body(text), "", f"end {space}", "", *examples]
        )
    analysis = claim.analysis
    assert isinstance(analysis, ExactAnalysis)
    level = analysis.level
    if analysis.kind == "margin":
        proof = [
            f"  have claim := {name} i premises",
            f"  have same : {space}.declaredAnalysis = {lean(analysis.name)} := by",
            f"    unfold {space}.declaredAnalysis {lean(analysis.name)}",
            "    congr 1",
            "    all_goals norm_num",
            "  rw [same]",
            "  intro parameter null",
            "  refine le_trans (claim parameter null) ?_",
            f"  norm_num [{level}]",
        ]
    elif analysis.kind == "groups":
        names = analysis.names
        proof = [
            "  intro p",
            f"  have claim := {name} i premises (p, p) rfl",
            # The sampling law of a fixed design is the model's law.
            "  change ((StatClaim.Modules.TwoArmBinomial.model "
            f"{names['groups']}).law (p, p)).real",
            f"    (StatClaim.Modules.Fisher.procedure {names['groups']} {level}).rejectionEvent ≤ _"
            " at claim",
            f"  rw [StatClaim.Modules.TwoArmBinomial.law_under_null {names['groups']} (p, p) rfl,",
            f"    StatClaim.Modules.Fisher.rejectionEvent_eq {names['groups']} {level}] at claim",
            "  exact claim",
        ]
    elif analysis.kind == "randomisation":
        proof = [
            "  intro _ _ _ statistic outcomes sharp",
            f"  exact {name} i premises statistic outcomes sharp",
        ]
    else:
        proof = [f"  exact {name} i premises"]
    return "\n".join(
        [
            f"namespace {space}",
            "",
            template_body(template(analysis.kind, analysis.test)),
            "",
            f"end {space}",
            "",
            "example (i : Instance) (premises : Premises i) :",
            f"    type_of% @{space}.checked_typeI := by",
            *proof,
            "",
        ]
    )


def equivalences(path: Path) -> list[str]:
    """One for each exact test's claim in the program."""
    program = compiled(path)
    assert program is not None
    claims = denote(program).claims
    return [
        equivalence(claim)
        for claim in claims
        if isinstance(claim.analysis, ExactAnalysis) or claim.result is not None
    ]


def block(path: Path, result: Translation, extra: list[str] = []) -> str:  # noqa: B006
    name = namespace(path)
    tail = "".join(f"{text}\n" for text in extra)
    return f"namespace {name}\n\n{result.lean}\n{tail}end {name}\n"


def pinned(path: str) -> Path:
    return PINNED_DIRECTORY / (Path(path).with_suffix("").as_posix().replace("/", "__") + ".lean")


def main() -> int:
    blocks, claims, skipped, rejected, templates = [], 0, 0, 0, 0
    results: dict[str, tuple[Path, Translation]] = {}
    for path in corpus():
        result = translation(path)
        if result is None:
            rejected += 1
            continue
        results[label(path)] = (path, result)
        extra = equivalences(path)
        templates += len(extra)
        blocks.append(block(path, result, extra))
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
    print(
        f"Lean accepted every translated program, and each of the {templates} exact tests' "
        "claims implies the statement its template checks."
    )
    problems = grade_problems(results, run.stdout + run.stderr)
    if problems:
        print(f"{len(problems)} claims have grades that disagree:")
        print("\n".join(problems))
        return 1
    print(f"Every claim's grade from Lean's dependencies agrees with Python ({claims} claims).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
