"""Translate a compiled program into a Lean file. See docs/proposals/lean-translation.md.

`denote.py` decides what the file states, `prove.py` how each statement is proved, and
`grades.py` how each claim's grade follows from the premises its proof uses. This module
puts them together. The file ends in a `ProgramTheorem`: for every instance of the
program's abstract parts, the premises imply the claims, and some instance meets the
premises. Anything not translated is listed in `skipped` with the reason.
"""

import re
from dataclasses import dataclass, field

from statclaim.language import ProgramIR
from statclaim.lean_translation import prove
from statclaim.lean_translation.denote import INTERFACE, Denotation, denote
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.grades import collector


@dataclass
class Translation:
    lean: str
    claims: dict[str, str] = field(default_factory=dict)  # claim → the grade expected
    owns: dict[str, str | None] = field(default_factory=dict)  # claim → its own premise
    requests: dict[str, int] = field(default_factory=dict)  # claim → its request id
    skipped: dict[str, str] = field(default_factory=dict)  # binding or request → reason


def render(denotation: Denotation, label: str) -> str:
    out = ["set_option linter.unusedVariables false", ""]
    out += [
        "/-- The program's abstract parts: laws Lean does not fix, and the tests seen",
        "from outside. -/",
        "structure Instance where",
    ]
    out += [f"  {line}" for line in denotation.fields]
    out += [*denotation.instances, ""]
    for definition in denotation.defs:
        out += [definition, ""]
    if denotation.contracts:
        out += ["-- Contract facts the Python compiler checks, decided by Lean.", ""]
    for fact in denotation.contracts:
        if fact.check == "comment":
            out += [f"-- {fact.facts[0]}", ""]
            continue
        out += [
            f"theorem {lean(fact.name)} :\n    " + " ∧\n    ".join(fact.facts) + " :=",
            f"  {prove.contract(fact)}",
            "",
        ]
    out += [
        "/-- The premises the claims rest on: cited and declared guarantees. -/",
        "structure Premises (i : Instance) : Prop where",
    ]
    out += [f"  {lean(p.name)} : {p.statement}" for p in denotation.premises]
    out.append("")
    for claim in denotation.claims:
        proof = prove.claim(claim)
        head = f"theorem {lean(claim.name)} (i : Instance) (premises : Premises i) :"
        if proof.startswith("by\n"):
            out += [head, f"    {claim.statement} := by", proof.removeprefix("by\n"), ""]
        else:
            out += [head, f"    {claim.statement} :=", f"  {proof}", ""]
    conjuncts = [claim.statement for claim in denotation.claims] or ["True"]
    wrapped = [f"({c})" if len(conjuncts) > 1 else c for c in conjuncts]
    out += [
        "/-- What the program claims. -/",
        "def Claims (i : Instance) : Prop :=",
        "  " + " ∧\n  ".join(wrapped),
        "",
    ]
    out.append("/-- One instance meeting every premise, so the claims are not vacuous. -/")
    values = prove.witness(denotation.abstracts)
    if values:
        out.append("noncomputable def witness : Instance where")
        out += [f"  {value}" for value in values]
    else:
        out.append("noncomputable def witness : Instance := ⟨⟩")
    out.append("")
    proofs = [f"{lean(claim.name)} i premises" for claim in denotation.claims]
    if len(proofs) == 1:
        implies = proofs[0]
    else:
        implies = f"⟨{', '.join(proofs)}⟩" if proofs else "trivial"
    met = ", ".join(prove.premise(p) for p in denotation.premises)
    out += [
        f"theorem program : {INTERFACE}.ProgramTheorem Premises Claims where",
        f"  implies := fun i premises => {implies}",
        f"  satisfiable := ⟨witness, ⟨{met}⟩⟩",
        "",
    ]
    out.append(collector(label, [claim.name for claim in denotation.claims]))
    return "\n".join(out).rstrip() + "\n"


def translate(program: ProgramIR, label: str = "program") -> Translation:
    """The Lean text of a compiled program, its claims and what it leaves out.

    `label` names the program in the lines Lean prints about each claim's premises.
    """
    denotation = denote(program)
    safe_label = re.sub(r"[^A-Za-z0-9_./-]", "_", label)
    return Translation(
        render(denotation, safe_label),
        {claim.name: claim.grade for claim in denotation.claims},
        {claim.name: claim.own for claim in denotation.claims},
        {claim.name: claim.request_id for claim in denotation.claims},
        dict(denotation.skipped),
    )
