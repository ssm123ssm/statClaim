"""Write docs/trusted-lean.md: which Lean a reviewer must read, and how much of it.

uv run python scripts/check_trusted_lean.py          # rewrite the page
uv run python scripts/check_trusted_lean.py --check  # fail if it is out of date

Lean checks every proof, so proofs need no review. The definitions that say what a
certificate proves do: the semantics' claims, premises, grades and contracts, the
encoding, the generated registry, and the objects and procedures they are stated in.
Each file has a role here; the semantics' files also state it in their headers. The page
lists the line counts of every trusted file, so the check fails, and a review sees it,
whenever the trusted Lean changes.
"""

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "docs/trusted-lean.md"

ROLES = {
    "all": "Trusted in full",
    "statements": "Definitions trusted; Lean checks the proofs",
    "none": "Not trusted: Lean checks these proofs",
}
# What a header must say for each role, in the files that carry one.
HEADERS = {
    "all": "Trusted",
    "statements": "Trusted: the statement of each checked claim",
    "none": "Not trusted",
}
ROLE = {
    "StatClaim/Semantics/Syntax.lean": "all",
    "StatClaim/Semantics/Meaning.lean": "all",
    "StatClaim/Semantics/Contracts.lean": "all",
    "StatClaim/Semantics/Grades.lean": "all",
    "StatClaim/Semantics/Encode.lean": "all",
    "StatClaim/Generated/Methods.lean": "all",
    "StatClaim/Semantics/Exact.lean": "statements",
    "StatClaim/Semantics/Results.lean": "statements",
    "StatClaim/Semantics/Intervals.lean": "statements",
    "StatClaim/Semantics/Plans.lean": "statements",
    "StatClaim/Semantics/Soundness.lean": "none",
    "StatClaim/Semantics/Theorems.lean": "none",
    "StatClaim/Semantics/Injective.lean": "none",
}
# Files whose headers must state their role.
MARKED = ("StatClaim/Semantics/", "StatClaim/Generated/")

INTRO = """# Trusted Lean

A certificate proves what the Lean definitions say it proves, so a reviewer must read
those definitions. Lean's kernel checks every proof, so proofs need no review. This page
lists every Lean file of the library with what in it is trusted:

- **Trusted in full**: the semantics' syntax, the meaning of every claim, its premises
  and grade, the contracts, the encoding of a program as data, and the generated
  registry of cited methods and procedures.
- **Definitions trusted**: the objects and procedures claims are stated in, and the
  statement of each checked claim; Lean checks the theorems and each check's soundness.
- **Not trusted**: proofs only.

Beyond these files, Lean's kernel, its JSON printer, the toolchain and the StatClaim
parser and elaborator are trusted; see [certificates](certificates.md).

`scripts/check_trusted_lean.py` writes this page, and `make lean-check` fails when it is
out of date: a change to a trusted file changes its line count here, so it shows in
review. Run `uv run python scripts/check_trusted_lean.py` after a reviewed change.
"""


def role(path: str) -> str:
    return ROLE.get(path, "statements")


def header(text: str) -> str:
    """The module's first block comment."""
    start = text.find("/-!")
    return text[start : text.find("-/", start)] if start >= 0 else ""


def problems(files: list[Path]) -> list[str]:
    found = []
    for path in files:
        name = path.relative_to(ROOT).as_posix()
        if not name.startswith(MARKED):
            continue
        said = header(path.read_text())
        kind = role(name)
        wrong = [other for other in ("statements", "none") if other != kind]
        if HEADERS[kind] not in said or any(HEADERS[other] in said for other in wrong):
            found.append(f"{name}: its header must say {HEADERS[kind]!r} and no other role.")
    unknown = sorted(set(ROLE) - {p.relative_to(ROOT).as_posix() for p in files})
    found += [f"{name} is listed but does not exist." for name in unknown]
    return found


def render(files: list[Path]) -> str:
    rows, totals = [], dict.fromkeys(ROLES, 0)
    for path in files:
        name = path.relative_to(ROOT).as_posix()
        kind = role(name)
        lines = len(path.read_text().splitlines())
        totals[kind] += lines
        rows.append(f"| `{name}` | {ROLES[kind]} | {lines if kind != 'none' else ''} |")
    summary = (
        f"Trusted in full: {totals['all']} lines. Definitions trusted, with proofs Lean "
        f"checks: {totals['statements']} lines. Proofs only: {totals['none']} lines."
    )
    table = ["| File | What is trusted | Lines |", "| --- | --- | ---: |", *rows]
    return "\n".join([INTRO, summary, "", *table, ""])


def main() -> int:
    files = sorted((ROOT / "StatClaim").rglob("*.lean"))
    found = problems(files)
    if found:
        print("\n".join(found))
        return 1
    text = render(files)
    if "--check" in sys.argv:
        if not TARGET.is_file() or TARGET.read_text() != text:
            print(f"{TARGET.relative_to(ROOT)} is out of date; run scripts/check_trusted_lean.py")
            return 1
        print(f"{TARGET.relative_to(ROOT)} is current.")
        return 0
    TARGET.write_text(text)
    print(f"Wrote {TARGET.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
