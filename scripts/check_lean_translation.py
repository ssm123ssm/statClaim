"""Translate every .stat program in the corpus to Lean, and check the result with Lean.

uv run python scripts/check_lean_translation.py            # translate, then check with Lean
uv run python scripts/check_lean_translation.py --no-lean  # translate only
uv run python scripts/check_lean_translation.py --update   # rewrite the pinned translations

Part 3 of docs/proposals/lean-translation.md. The corpus is every example, lesson and
article program in examples/ and every replication study in replication/*/. All programs
go in one Lean file, one namespace each, so Mathlib is imported once. A program the
compiler rejects is not translated; its rejection is checked separately.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source
from statclaim.lean_translation.program import Translation, translate

ROOT = Path(__file__).resolve().parents[1]
PINNED_DIRECTORY = ROOT / "tests/fixtures/lean_translation"
# Translations reviewed as diffs: an exact test, cited tests of both scopes, a declared
# test, and a design whose stopping rule leaves its claim unresolved.
PINNED = (
    "examples/paper/fisher_design.stat",
    "examples/t_test.stat",
    "examples/declared_test.stat",
    "examples/paper/fisher_adaptive.stat",
)


def corpus() -> list[Path]:
    return sorted([*(ROOT / "examples").rglob("*.stat"), *(ROOT / "replication").glob("*/*.stat")])


def namespace(path: Path) -> str:
    parts = path.relative_to(ROOT).with_suffix("").parts
    return "StatClaimProgram." + ".".join(f"«{part}»" for part in parts)


def translation(path: Path) -> Translation | None:
    """The program's translation, or None when the compiler rejects it."""
    compiled = compile_source(Source(path.read_text(encoding="utf-8"), str(path)))
    if compiled.status == "invalid" or compiled.program is None:
        return None
    return translate(compiled.program)


def block(path: Path, result: Translation) -> str:
    name = namespace(path)
    return f"namespace {name}\n\n{result.lean}\nend {name}\n"


def pinned(path: str) -> Path:
    return PINNED_DIRECTORY / (Path(path).with_suffix("").as_posix().replace("/", "__") + ".lean")


def main() -> int:
    blocks, claims, skipped, rejected = [], 0, 0, 0
    for path in corpus():
        result = translation(path)
        if result is None:
            rejected += 1
            continue
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
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
