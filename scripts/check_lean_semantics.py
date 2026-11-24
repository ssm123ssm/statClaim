"""Check the semantics on the corpus (docs/proposals/lean-semantics.md).

uv run python scripts/check_lean_semantics.py            # write the data, then check in Lean
uv run python scripts/check_lean_semantics.py --no-lean  # write the data only

For every corpus program the semantics covers, Python writes the program as Lean data,
and one Lean build checks each program's contracts by `decide +kernel`, proves each claim
that has a sampling law by the soundness theorem, and prints the data's canonical form
and each claim's grade. The canonical form must equal the canonical program's `verify`
claims, and each grade must be Python's. The same build accepts, by definition, that
each claim today's translation states is the semantics' claim, and that its premises give
the premises the semantic claim assumes. Every other program is listed with the reason
the semantics does not cover it yet.
"""

import collections
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from check_lean_translation import (  # noqa: E402
    compiled,
    corpus,
    namespace,
    python_catches_up,
    python_grade,
)

from statclaim.language_compiler import compile_source  # noqa: E402
from statclaim.lean_translation import data  # noqa: E402
from statclaim.lean_translation.certificate import Source  # noqa: E402
from statclaim.lean_translation.data import (  # noqa: E402
    Outside,
    binding_problem,
    claims,
    printed_grades,
    program_data,
    ready,
    report,
    verify_claims,
)
from statclaim.lean_translation.denote import Denotation, denote  # noqa: E402
from statclaim.lean_translation.emit import name as lean  # noqa: E402


def label(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def covered() -> tuple[dict[str, tuple[Path, dict, str]], collections.Counter]:
    """The programs the semantics covers, with their canonical form and data, and why the
    others are not covered."""
    found, outside = {}, collections.Counter()
    for path in corpus():
        compilation = compile_source(Source(path.read_text(), label(path)))
        if compilation.status == "invalid":
            outside["The compiler rejects it."] += 1
            continue
        program = compilation.program.to_dict()
        try:
            found[label(path)] = (path, program, program_data(program))
        except Outside as reason:
            outside[str(reason)] += 1
    return found, outside


SEMANTICS = "StatClaim.Semantics"


def adapter(denotation: Denotation) -> str:
    """Today's abstract parts, read off the semantics' instance."""
    lines = [f"abbrev Instance := {SEMANTICS}.Instance"]
    for part in denotation.abstracts:
        source = denotation.sources[part.name]
        field = lean(part.name)
        if source[0] in ("model", "study"):
            law = (
                f"(i.laws {data.model(source[1])})"
                if source[0] == "model"
                else f"(i.studies {data.study(source[1])})"
            )
            lines += [
                f"def Instance.{part.parameter} (i : Instance) : Type := {law}.Parameter",
                f"def Instance.{part.outcome} (i : Instance) : Type := {law}.Outcome",
                f"instance (i : Instance) : MeasurableSpace (Instance.{part.outcome} i) :=",
                f"  {law}.space",
                f"def Instance.{field} (i : Instance) := {law}.model",
            ]
        elif source[0] == "test" and "study" in source[2]:
            lines.append(
                f"def Instance.{field} (i : Instance) :=\n"
                f"  i.studyTest {data.string(source[1])} {data.study(source[2])}"
            )
        elif source[0] == "test":
            lines.append(
                f"def Instance.{field} (i : Instance) :=\n"
                f"  i.test {data.string(source[1])} {data.model(source[2])}"
            )
        elif source[0] == "slack":
            lines.append(
                f"def Instance.{field} (i : Instance) : ℝ := i.slack {data.string(source[1])}"
            )
        else:
            views = [f"({SEMANTICS}.Model.view i.laws {data.model(m)})" for m in source[2]]
            binders = " ".join(
                f"(v{k} : StatClaim.Interface.MemberView Θ Ω {v}.Parameter {v}.Outcome)"
                for k, v in enumerate(views)
            )
            given = ", ".join([f"v{k}" for k in range(len(views))] + ["PUnit.unit"])
            count, listed = len(views), ", ".join(views)
            lines.append(
                f"def Instance.{field} (i : Instance) (Θ Ω : Type) [MeasurableSpace Ω]\n"
                f"    (σ : StatClaim.Interface.JointStudy Θ Ω) {binders} :\n"
                f"    Fin {count} → Set Ω :=\n"
                f"  i.graph {data.string(source[1])} [{listed}] {count} Θ Ω σ ({given})"
            )
    return "\n".join(lines) + "\n"


def statements(denotation: Denotation) -> str:
    """Today's translation without its proofs: its definitions, premises and claims, over
    the semantics' instance."""
    out = [adapter(denotation)]
    out += [f"{definition}\n" for definition in denotation.defs]
    out.append("structure Premises (i : Instance) : Prop where")
    out += [f"  {lean(p.name)} : {p.statement}" for p in denotation.premises]
    conjuncts = [claim.statement for claim in denotation.claims] or ["True"]
    wrapped = [f"({c})" if len(conjuncts) > 1 else c for c in conjuncts]
    out += ["", "def Claims (i : Instance) : Prop :=", "  " + " ∧\n  ".join(wrapped)]
    return "\n".join(out) + "\n"


def agreement(path: Path, program: dict) -> str:
    """Lean must accept that each claim the translation states is the semantics' claim,
    by definition, and that its premises give the premises each semantic claim assumes."""
    denotation = denote(compiled(path))
    requests = [r for r in program["requests"] if r["operation"] == "verify"]
    index = {request["request_id"]: k for k, request in enumerate(requests)}
    fields = {denotation.sources[p.name]: lean(p.name) for p in denotation.premises}
    lines = [f"namespace Old\n\n{statements(denotation)}\nend Old\n"]
    if denotation.claims:
        stated = " ∧ ".join(f"program.claimAt {index[c.request_id]} i" for c in denotation.claims)
        lines.append(f"example (i : {SEMANTICS}.Instance) : Old.Claims i ↔ {stated} := Iff.rfl")
    for c in denotation.claims:
        r = index[c.request_id]
        claim = requests[r]["claim"]
        given = [
            f"h.{fields[key]}" for key in data.premise_keys(claim["subject_name"], claim["subject"])
        ]
        proof = f"⟨{', '.join([*given, 'trivial'])}⟩" if given else "trivial"
        lines.append(
            f"example (i : {SEMANTICS}.Instance) (h : Old.Premises i) :\n"
            f"    {SEMANTICS}.Premise.AllHold i (program.premisesAt {r}) := {proof}"
        )
    return "\n".join(lines) + "\n"


def block(path: Path, name: str, program: dict, data: str) -> str:
    return (
        f"namespace {namespace(path)}\n\n{data}\n{claims(program)}\n"
        f"{report(name)}\n{agreement(path, program)}\nend {namespace(path)}\n"
    )


def grade_problems(name: str, path: Path, program: dict, output: str) -> list[str]:
    """Claims whose grade in Lean is not Python's. A combination whose members are all
    proved is proved in Lean; Python reports it as conditional until it takes its evidence
    from the semantics."""
    grades = printed_grades(output, name)
    if grades is None:
        return [f"Lean printed no grades for {name}."]
    problems = []
    requests = [r for r in program["requests"] if r["operation"] == "verify"]
    for request, grade in zip(requests, grades, strict=True):
        if not ready(request["claim"]):
            continue
        expected = python_grade(path, request["request_id"])
        catching_up = (grade, expected) == ("proved", "conditional") and python_catches_up(
            path, request["request_id"]
        )
        if grade != expected and not catching_up:
            problems.append(
                f"{name} request {request['request_id']}: Lean {grade}, Python {expected}"
            )
    return problems


def main() -> int:
    found, outside = covered()
    print(f"The semantics covers {len(found)} corpus programs; the others:")
    for reason, number in outside.most_common():
        print(f"  {number:3}  {reason}")
    if "--no-lean" in sys.argv:
        return 0
    text = "import StatClaim\n\nset_option linter.unusedVariables false\n\n" + "\n".join(
        block(path, name, program, data) for name, (path, program, data) in found.items()
    )
    with tempfile.TemporaryDirectory() as directory:
        file = Path(directory) / "Semantics.lean"
        file.write_text(text)
        run = subprocess.run(
            ["lake", "env", "lean", str(file)], cwd=ROOT, capture_output=True, text=True
        )
    output = run.stdout + run.stderr
    if run.returncode != 0:
        errors = [line for line in output.splitlines() if re.search(r":\d+:\d+: error", line)]
        print(f"Lean refused the data or its contracts ({len(errors)} errors):")
        print("\n".join(output.splitlines()[:60]))
        return 1
    problems = [
        problem
        for name, (_, program, _) in found.items()
        if (problem := binding_problem(output, name, program)) is not None
    ]
    for name, (path, program, _) in found.items():
        problems += grade_problems(name, path, program, output)
    if problems:
        print("\n".join(problems))
        return 1
    stated = [ready(claim) for _, program, _ in found.values() for claim in verify_claims(program)]
    agreed = sum(len(denote(compiled(path)).claims) for path, _, _ in found.values())
    print(
        f"Lean's contracts hold for all {len(found)}, and each one's data encodes to its "
        f"canonical program. The soundness theorem proves {sum(stated)} claims, each with "
        f"Python's grade; {len(stated) - sum(stated)} are not ready (no sampling law, or "
        f"levels over budget) and stay unproved, as in Python. Each of the {agreed} claims "
        "today's translation states is the "
        "semantics' claim, by definition, and its premises give the semantic claim's."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
