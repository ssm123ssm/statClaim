"""Check Phase 2's one-sided Fisher spike for kernel and output binding checks."""

import copy
import subprocess
import tempfile
from pathlib import Path

from check_lean_semantics import ROOT, fixtures, grade_problems

from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source
from statclaim.lean_translation import data
from statclaim.lean_translation.certificate import AUDIT
from statclaim.lean_translation.material import material

EXAMPLE = "examples/one_sided.stat"
OPTIONS = "set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\n"


def spike() -> tuple[dict, list[dict | None], dict[int, str]]:
    path = ROOT / EXAMPLE
    compiled = compile_source(Source(path.read_text(), EXAMPLE))
    assert compiled.status != "invalid"
    outputs, hints = material(compiled.program, ROOT)
    return compiled.program.to_dict(), outputs, hints


def proof(program: dict, reported: list[dict | None], hints: dict[int, str]) -> str:
    audit = AUDIT.format(
        names=", ".join(f"``{name}" for name in ["contracts", *(f"claim_{r}" for r in hints)]),
        input_sha256="0" * 64,
    )
    return "\n".join(
        [
            "import StatClaim\nimport Lean.Util.CollectAxioms\n",
            data.program_data(program, reported=reported),
            data.claims(program, hints, reported),
            data.report(EXAMPLE),
            audit,
        ]
    )


def refusals(program: dict, reported: list[dict | None], hints: dict[int, str]) -> str:
    type_i = next(
        r for r, claim in enumerate(data.verify_claims(program)) if claim["kind"] == "typeI"
    )
    result = next(
        r for r, claim in enumerate(data.verify_claims(program)) if claim["kind"] == "result"
    )
    assert reported[result] is not None
    checks = [
        f"example : program.checkAt {type_i} [] = false := by decide +kernel",
        "",
    ]
    wrong_p_value = "1" if reported[result]["p_value"] == "0" else "0"
    for index, change in enumerate(
        (
            {"p_value": wrong_p_value},
            {"reject_null": not reported[result]["reject_null"]},
        )
    ):
        wrong = copy.deepcopy(reported)
        wrong[result].update(change)
        checks += [
            f"namespace WrongOutput{index}",
            data.program_data(program, reported=wrong),
            f"example : program.checkAt {result} {hints[result]} = false := by decide +kernel",
            f"end WrongOutput{index}",
        ]
    wrong_null = copy.deepcopy(program)
    data.verify_claims(wrong_null)[type_i]["subject"]["null"]["value"] = "-1/20"
    checks += [
        "namespace WrongNull",
        data.program_data(wrong_null, reported=reported),
        "example : ¬ program.Contracts := by decide +kernel",
        "end WrongNull",
    ]
    return "\n".join(checks)


def main() -> int:
    program, reported, hints = spike()
    text = "\n".join(
        [
            proof(program, reported, hints),
            OPTIONS,
            "set_option linter.unusedVariables false",
            fixtures()[EXAMPLE][1],
            refusals(program, reported, hints),
        ]
    )
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "ExactSpike.lean"
        path.write_text(text)
        run = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True
        )
    output = run.stdout + run.stderr
    if run.returncode:
        print(output)
        return 1
    problem = data.binding_problem(output, EXAMPLE, program, reported=reported)
    problems = ([problem] if problem else []) + grade_problems(
        EXAMPLE,
        compile_source(Source((ROOT / EXAMPLE).read_text(), EXAMPLE)).program,
        reported,
        output,
    )
    wrong_report = copy.deepcopy(reported)
    for reply in wrong_report:
        if reply is not None and "reject_null" in reply:
            reply["reject_null"] = not reply["reject_null"]
    if not data.binding_problem(output, EXAMPLE, program, reported=wrong_report):
        problems.append("The binding check accepted a different reported decision.")
    if problems:
        print("\n".join(problems))
        return 1
    print(
        "Lean proved all three spike claims, agreed with the frozen translator statements, "
        "and rejected bad hints and results."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
