"""Ask Lean about programs Python refuses: test 3 of docs/proposals/lean-translation.md.

Python checks contracts while it elaborates, so a program that fails one has no typed
form and never reaches Lean. Here those checks are deferred instead: each failure is
recorded, the value is built anyway, and the program is translated with every `verify`
claim stated, including those Python leaves with an open requirement. Lean then gives
one of the `OUTCOMES`, read from where its first error falls.

The same program is also written as Lean data (`data.py`) and asked of the semantics
(docs/proposals/lean-semantics.md): whether its contracts hold, and whether each claim
follows by the soundness theorem or, when a design stops by a rule depending on the
data, is false.

Not trusted: a mistake here makes the check pass or fail wrongly, never a certificate.
"""

import re
from dataclasses import dataclass

from statclaim.language import elaborate
from statclaim.language_compiler import requirements
from statclaim.language_syntax import DEFERRED, Diagnostic, Source
from statclaim.lean_translation import data
from statclaim.lean_translation.denote import Denotation, denote
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.program import render

# The statistical contracts and value ranges Python checks while elaborating
# (`reference.py`); syntax, names and types are never deferred.
CONTRACTS = frozenset(
    {
        "domain",
        "model_mismatch",
        "hypothesis_mismatch",
        "alternative_in_null",
        "direction_mismatch",
        "complex_sample",
        "matched_design",
        "not_estimable",
        "observational_design",
        "unit_mismatch",
        "undeclared_randomisation",
        "population_mismatch",
        "never_rejects",
        "planning_point",
        "rule_mismatch",
        "sampling_contract",
        "family_size",
        "duplicate_analysis",
        "outcome_conflict",
        "sequential_question",
        "sequence_level",
        "graph_definition",
        "sequential_order",
    }
)

OUTCOMES = {
    "contract": "Lean decides one of the program's contract facts false.",
    "ill_typed": "Lean rejects a definition or premise of the program as ill-typed.",
    "unproved": "Lean fails to prove the claim, while every contract fact holds.",
    "refuted": "Lean proves that the design supplies no sampling law, so the claim cannot "
    "be stated, or under the semantics is false.",
    "accepted": "Lean accepts the program: Python's rule asks more than any claim Lean states.",
    "untyped": "No typed program: a type error, or values Python's objects refuse to hold "
    "even with the contract checks deferred. Nothing reaches Lean.",
}
# The semantics' outcomes add one: a program it does not cover yet (phase 2).
SEMANTIC_OUTCOMES = {
    **OUTCOMES,
    "uncovered": "The semantics does not cover the program yet, so it has no Lean data.",
}

DECLARATION = re.compile(
    r"^(?:(?:noncomputable|private|protected)\s+)*(theorem|def|structure|abbrev|instance)\s+(\S+)"
)


@dataclass
class Asked:
    """A program Python refuses, or leaves with open requirements, as Lean is asked it."""

    label: str
    deferred: list[Diagnostic]  # contract checks Python failed, deferred
    errors: list[Diagnostic]  # other errors, which leave no typed program
    open: list[Diagnostic]  # requirements Python leaves open on verify claims
    denotation: Denotation | None = None
    lean: str = ""  # the translation, empty when there is no typed program
    # Why a value could not be built past a deferred check, when it could not.
    unbuilt: str = ""
    program: dict | None = None  # the canonical program, when there is a typed one
    semantic: str = ""  # its Lean data and what Lean is asked of it, when it is covered
    uncovered: str = ""  # why the semantics does not cover it yet

    @property
    def refused(self) -> list[str]:
        """The codes of what Python refuses."""
        codes = [d.code for d in (*self.errors, *self.deferred, *self.open)]
        return [*codes, "unbuilt"] if self.unbuilt else codes


def ask(source: Source, label: str) -> Asked:
    """Elaborate with contracts deferred, then translate with every claim stated, and write
    the program as Lean data when the semantics covers it."""
    deferred: list[Diagnostic] = []
    token = DEFERRED.set((CONTRACTS, deferred))
    try:
        program, diagnostics = elaborate(source)
    except (ValueError, TypeError, AttributeError) as refused:
        # Building a value went on past a deferred check and found it could not.
        return Asked(label, deferred, [], [], unbuilt=f"{type(refused).__name__}: {refused}")
    finally:
        DEFERRED.reset(token)
    errors = [d for d in diagnostics if d.severity == "error"]
    if errors:
        return Asked(label, deferred, errors, [])
    opened = [
        diagnostic
        for request in program.requests
        if request.operation == "verify"
        for diagnostic in requirements(program, request)
    ]
    canonical = program.to_dict()
    asked = Asked(label, deferred, [], opened, program=canonical)
    try:
        asked.semantic = questions(canonical, label)
    except data.Outside as reason:
        asked.uncovered = str(reason)
    try:
        asked.denotation = denote(program, ask=True)
        asked.lean = render(asked.denotation, label)
    except ValueError as refused:
        # A module's own object refuses the values, so no Lean statement is formed.
        asked.unbuilt = f"ValueError: {refused}"
    return asked


def questions(program: dict, label: str) -> str:
    """The program as Lean data, with what Lean is asked of it: that its contracts hold;
    each claim, by the soundness theorem, or its refutation when a design stops by a rule
    depending on the data; and the data's canonical form."""
    lines = [
        data.program_data(program),
        "theorem contracts : program.Contracts := by decide +kernel",
    ]
    for index, claim in enumerate(data.verify_claims(program)):
        if data.fixed(claim["subject"]):
            lines.append(
                f"theorem claim_{index} : program.Claim {index} :=\n"
                f"  {data.SEMANTICS}.Program.sound program contracts {index} (by decide +kernel)"
            )
        else:
            lines.append(
                f"theorem refuted_{index} : ¬ program.Claim {index} :=\n"
                f"  {data.SEMANTICS}.Program.refuted program {index} (by decide +kernel)"
            )
    return "\n\n".join([*lines, data.report(label)])


def owners(text: str) -> list[tuple[str, str]]:
    """For each line of a translation, its namespace and the declaration it belongs to."""
    spaces: list[str] = []
    current = ""
    found = []
    for line in text.splitlines():
        if line.startswith("namespace "):
            spaces.append(line.split()[1])
            current = ""
        elif line.startswith("end ") and spaces and line.split()[1] == spaces[-1]:
            spaces.pop()
            current = ""
        elif line.startswith(("run_cmd", "open ")):
            current = "run_cmd" if line.startswith("run_cmd") else current
        else:
            match = DECLARATION.match(line)
            if match:
                current = match.group(2)
        found.append((".".join(spaces), current))
    return found


def outcome(asked: Asked, errors: list[int]) -> str:
    """Lean's outcome for a program, from the lines of its translation where Lean reported
    errors (counted from 1)."""
    denotation = asked.denotation
    if denotation is None:
        return "untyped"
    if not errors:
        return "refuted" if denotation.refuted else "accepted"
    space, declaration = owners(asked.lean)[min(errors) - 1]
    if declaration in {lean(c.name) for c in denotation.contracts if c.name}:
        return "contract"
    claims = {lean(c.name) for c in denotation.claims}
    if declaration in claims or any(space.startswith(f"{claim}_") for claim in claims):
        return "unproved"
    return "ill_typed"


def semantic_outcome(asked: Asked, errors: list[int]) -> str:
    """The semantics' outcome for a program, from the lines of its Lean data and questions
    where Lean reported errors (counted from 1)."""
    if not asked.semantic:
        return "uncovered" if asked.uncovered else "untyped"
    if not errors:
        return "refuted" if "\ntheorem refuted_" in asked.semantic else "accepted"
    _, declaration = owners(asked.semantic)[min(errors) - 1]
    if declaration == "contracts":
        return "contract"
    if declaration.startswith(("claim_", "refuted_")):
        return "unproved"
    return "ill_typed"
