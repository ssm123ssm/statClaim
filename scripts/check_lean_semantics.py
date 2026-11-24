"""Check the semantics' data on the corpus (docs/proposals/lean-semantics.md, milestone 1).

uv run python scripts/check_lean_semantics.py            # write the data, then check in Lean
uv run python scripts/check_lean_semantics.py --no-lean  # write the data only

For every corpus program the semantics covers, Python writes the program as Lean data,
and one Lean build checks each program's contracts by `decide +kernel` and prints the
data's canonical form, which must equal the canonical program's `verify` claims. Every
other program is listed with the reason the semantics does not cover it yet.
"""

import collections
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from check_lean_translation import corpus, namespace  # noqa: E402

from statclaim.language_compiler import compile_source  # noqa: E402
from statclaim.lean_translation.certificate import Source  # noqa: E402
from statclaim.lean_translation.data import (  # noqa: E402
    Outside,
    binding_problem,
    program_data,
    report,
)


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


def block(path: Path, name: str, data: str) -> str:
    return (
        f"namespace {namespace(path)}\n\n{data}\n"
        "theorem contracts : program.Contracts := by decide +kernel\n\n"
        f"{report(name)}\nend {namespace(path)}\n"
    )


def main() -> int:
    found, outside = covered()
    print(f"The semantics covers {len(found)} corpus programs; the others:")
    for reason, number in outside.most_common():
        print(f"  {number:3}  {reason}")
    if "--no-lean" in sys.argv:
        return 0
    text = "import StatClaim\n\n" + "\n".join(
        block(path, name, data) for name, (path, _, data) in found.items()
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
    if problems:
        print("\n".join(problems))
        return 1
    print(
        f"Lean's contracts hold for all {len(found)}, and each one's data encodes to its "
        "canonical program."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
