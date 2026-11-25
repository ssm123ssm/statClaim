"""Check the corpus and frozen translator statements against the Lean semantics."""

import collections
import json
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
from statclaim.lean_translation import data
from statclaim.lean_translation.material import material

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests/fixtures/lean_semantics"
OPTIONS = (
    "import StatClaim\n\nset_option linter.unusedVariables false\n"
    "set_option linter.unusedSimpArgs false\nset_option maxRecDepth 100000\n"
    "set_option maxHeartbeats 20000000\n\n"
)


def label(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def corpus() -> list[Path]:
    """Tracked example and replication programs."""
    found = sorted([*(ROOT / "examples").rglob("*.stat"), *(ROOT / "replication").glob("*/*.stat")])
    listed = subprocess.run(
        ["git", "ls-files", "examples", "replication"], cwd=ROOT, capture_output=True, text=True
    )
    if listed.returncode != 0:
        return found
    tracked = set(listed.stdout.splitlines())
    return [path for path in found if label(path) in tracked]


def covered() -> tuple[dict, collections.Counter]:
    """The canonical and encoded corpus programs, plus counts of compiler rejections."""
    found, outside = {}, collections.Counter()
    for path in corpus():
        source = Source(path.read_text(), label(path))
        compilation = compile_source(source)
        if compilation.status == "invalid":
            outside["The compiler rejects it."] += 1
            continue
        program = compilation.program.to_dict()
        outputs, _ = material(compilation.program, ROOT)
        found[label(path)] = (path, program, data.program_data(program, reported=outputs))
    return found, outside


def fixtures() -> dict[str, tuple[str, str]]:
    sources = json.loads((FIXTURES / "sources.json").read_text())
    _, *sections = re.split(
        r"^-- program: (.+)\n", (FIXTURES / "Agreement.lean").read_text(), flags=re.M
    )
    statements = dict(zip(sections[::2], sections[1::2], strict=True))
    if len(statements) * 2 != len(sections) or statements.keys() != sources.keys():
        raise ValueError("Frozen statements must have exactly one pinned program each.")
    return {name: (source, statements[name]) for name, source in sources.items()}


def block(name: str, source: str, agreement: str, namespace: str):
    compiled = compile_source(Source(source, name))
    if compiled.status == "invalid":
        raise ValueError(f"{name}: a checked program no longer compiles.")
    program = compiled.program.to_dict()
    outputs, hints = material(compiled.program, ROOT)
    definition = data.program_data(program, reported=outputs)
    text = (
        f"namespace {namespace}\n\n{definition}\n{data.claims(program, hints, outputs)}\n"
        f"{data.report(name)}\n{agreement}\nend {namespace}\n"
    )
    return text, compiled.program, outputs


def grade_problems(name: str, compiled, reported: list, output: str) -> list[str]:
    grades = data.printed_grades(output, name)
    requests = [r for r in compiled.requests if r.operation == "verify"]
    if grades is None or len(grades) != len(requests):
        return [f"Lean printed the wrong number of grades for {name}."]
    problems = []
    canonical = data.verify_claims(compiled.to_dict())
    for index, (request, grade) in enumerate(zip(requests, grades, strict=True)):
        if not data.ready(canonical[index], reported, index):
            continue
        expected = STATUS_GRADES[best_status(request.claim)]
        if grade != expected and not (
            (grade, expected) == ("proved", "conditional")
            and isinstance(request.claim.subject, ComposedFamilyIR)
        ):
            problems.append(f"{name} request {request.request_id}: Lean {grade}, Python {expected}")
    return problems


def checks(found: dict, frozen: dict):
    for name in sorted(found.keys() | frozen.keys()):
        current = found[name][0].read_text() if name in found else None
        pin, statement = frozen.get(name, (None, ""))
        if current is not None:
            yield name, current, statement if current == pin else ""
        if pin is not None and current != pin:
            yield f"frozen/{name}", pin, statement


def main() -> int:
    found, outside = covered()
    frozen = fixtures()
    print(f"The semantics covers {len(found)} corpus programs; the others:")
    for reason, number in outside.most_common():
        print(f"  {number:3}  {reason}")
    if "--no-lean" in sys.argv:
        return 0
    # Run the same checks in batches so a large exact search releases its Lean heap
    # before the next batch starts.
    checks_to_run = list(checks(found, frozen))
    proved = 0
    agreements = sum(
        line.count("program.claimAt")
        for _, text in frozen.values()
        for line in text.splitlines()
        if "Old.Claims i ↔" in line
    )
    with tempfile.TemporaryDirectory() as directory:
        file = Path(directory) / "Semantics.lean"
        for start in range(0, len(checks_to_run), 12):
            inputs = checks_to_run[start : start + 12]
            built = [block(*entry, f"Corpus{i}") for i, entry in enumerate(inputs)]
            file.write_text(OPTIONS + "\n".join(text for text, _, _ in built))
            run = subprocess.run(
                ["lake", "env", "lean", str(file)], cwd=ROOT, capture_output=True, text=True
            )
            output = run.stdout + run.stderr
            if run.returncode:
                print(f"Lean failed for the batch starting at {inputs[0][0]}.")
                print("\n".join(line for line in output.splitlines() if "STATCLAIM_" not in line))
                return 1
            problems = []
            for (name, _, _), (_, compiled, reported) in zip(inputs, built, strict=True):
                program = compiled.to_dict()
                if problem := data.binding_problem(output, name, program, reported=reported):
                    problems.append(problem)
                problems.extend(grade_problems(name, compiled, reported, output))
                if not name.startswith("frozen/"):
                    proved += sum(
                        data.ready(claim, reported, i)
                        for i, claim in enumerate(data.verify_claims(program))
                    )
            if problems:
                print("\n".join(problems))
                return 1
            print(f"Checked {start + len(inputs)}/{len(checks_to_run)} programs.", flush=True)
    print(f"Lean proved {proved} live corpus claims and checked {agreements} frozen statements.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
