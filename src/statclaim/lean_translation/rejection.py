"""Ask Lean about programs Python refuses: test 3 of docs/proposals/lean-translation.md.

Python checks contracts while it elaborates, so a program that fails one has no typed
form and never reaches Lean. Here those checks are deferred instead: each failure is
recorded, the value is built anyway, and the program is translated with every `verify`
claim stated, including those Python leaves with an open requirement. Lean then gives
one of the `OUTCOMES`, read from where its first error falls.

Not trusted: a mistake here makes the check pass or fail wrongly, never a certificate.
"""

import re
from dataclasses import dataclass

from statclaim.language import elaborate
from statclaim.language_compiler import requirements
from statclaim.language_syntax import DEFERRED, Diagnostic, Source
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
    "refuted": "Lean proves that the design supplies no sampling law, so no claim is stated.",
    "accepted": "Lean accepts the program: Python's rule asks more than any claim Lean states.",
    "untyped": "No typed program: a type error, or values Python's objects refuse to hold "
    "even with the contract checks deferred. Nothing reaches Lean.",
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

    @property
    def refused(self) -> list[str]:
        """The codes of what Python refuses."""
        codes = [d.code for d in (*self.errors, *self.deferred, *self.open)]
        return [*codes, "unbuilt"] if self.unbuilt else codes


def ask(source: Source, label: str) -> Asked:
    """Elaborate with contracts deferred, then translate with every claim stated."""
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
    try:
        denotation = denote(program, ask=True)
        text = render(denotation, label)
    except ValueError as refused:
        # A module's own object refuses the values, so no Lean statement is formed.
        return Asked(label, deferred, [], opened, unbuilt=f"ValueError: {refused}")
    return Asked(label, deferred, [], opened, denotation, text)


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
