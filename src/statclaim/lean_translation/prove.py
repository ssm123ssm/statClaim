"""How a translated program's statements are proved. Untrusted: Lean's kernel checks every
proof, so a mistake here fails the build and cannot make a wrong statement pass.

Contract facts are decided by `decide` or `norm_num`. A single claim is proved directly,
from its premise or its module's theorem. A family is proved by naming its composition
rule and the members' levels, as the program states them; the `statclaim` tactic then
discharges what remains: each member's bound, the arithmetic on levels and the case
split over members.
"""

from statclaim.lean_translation.denote import (
    BINOMIAL,
    FISHER,
    INTERFACE,
    Abstract,
    Analysis,
    Claim,
    Contract,
    Premise,
    subscript,
)
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.emit import rational, real


def contract(fact: Contract) -> str:
    if fact.check == "decide":
        return "by decide"
    if fact.check == "norm_num":
        return f"by norm_num [{fact.unfold}]" if fact.unfold else "by norm_num"
    if fact.check == "fisher_null":
        if fact.predicate == "equal_proportions":
            return "fun parameter => Iff.rfl"
        return f"fun parameter => {BINOMIAL}.proportionDifference_zero_iff parameter"
    if fact.check == "fisher_requires":
        return f"⟨{fact.compatible}⟩"
    raise ValueError(f"No proof for a {fact.check} contract.")


def premise(_: Premise) -> str:
    """The witness meets every level premise with a test that never rejects."""
    return f"{INTERFACE}.neverRejects_meets_level _ _ _ _ (by norm_num)"


def witness(abstracts: list[Abstract]) -> list[str]:
    values = []
    for part in abstracts:
        if part.kind == "model":
            values += [
                f"{part.parameter} := Unit",
                f"{part.outcome} := Unit",
                f"{lean(part.name)} := {INTERFACE}.{part.structure}.trivial",
            ]
        elif part.kind == "test":
            values.append(f"{part.name} := {INTERFACE}.TestInterface.neverRejects _")
        else:
            values.append(f"{part.name} := 0")
    return values


def member_bound(member: Analysis) -> tuple[str, str]:
    """A member's own bound under its model's law: its type and its proof."""
    law, null, reject = member.model.law(), member.null_ref(), member.reject()
    if member.kind == "fisher":
        assert member.design.compatible is not None
        compatible = member.design.compatible.ref()
        bound = real(member.alpha)
        proof = (
            f"{INTERFACE}.model_bound {compatible}\n"
            f"      ({FISHER}.typeI_statement {lean(member.model.sizes)} {member.design.ref()} "
            f"{compatible} {lean(member.level)})"
        )
    else:
        bound = f"({real(member.alpha)} + i.{lean(member.slack)})"
        proof = f"premises.{lean(member.premise)}.2"
    return f"∀ parameter, {null} parameter → ({law} parameter).real {reject} ≤ {bound}", proof


def measurable(member: Analysis) -> str:
    if member.kind == "fisher":
        return f"{lean(member.name)}.procedure.rejection_measurable"
    return f"i.{lean(member.test)}.measurable"


def claim(statement: Claim) -> str:
    analysis = statement.analysis
    if statement.kind == "typeI":
        assert analysis is not None and analysis.design.compatible is not None
        compatible = analysis.design.compatible.ref()
        if analysis.kind == "fisher":
            return (
                f"{FISHER}.typeI_statement {lean(analysis.model.sizes)} {analysis.design.ref()} "
                f"{compatible} {lean(analysis.level)}"
            )
        given = f"premises.{lean(analysis.premise)}"
        if analysis.scope == "finite_sample":
            return f"{INTERFACE}.typeI_of_finite_premise {compatible} rfl {given}"
        return f"{INTERFACE}.typeI_of_premise {compatible} {given}"
    members = statement.members
    marks = [subscript(k) for k in range(len(members))]
    lines = [
        "by",
        f"  intro Θ Ω _ σ {' '.join(f'v{m}' for m in marks)} {' '.join(f'm{m}' for m in marks)}",
    ]
    for mark, member in zip(marks, members, strict=True):
        bound, proof = member_bound(member)
        lines += [
            f"  have o{mark} : {bound} :=",
            f"    {proof}",
            f"  have b{mark} := v{mark}.bound m{mark} {measurable(member)} o{mark}",
        ]
        if member.kind != "fisher":
            lines.append(
                f"  have s{mark} : 0 ≤ i.{lean(member.slack)} :=\n"
                f"    {INTERFACE}.Scope.permits_nonnegative premises.{lean(member.premise)}.1"
            )
    if statement.rule == "sequence":
        rule = f"{INTERFACE}.sequence_of_members σ _ _ {rational(statement.alpha)}"
    else:
        levels = ", ".join(rational(member.alpha) for member in members)
        rule = f"{INTERFACE}.familywise_of_members σ _ _ ![{levels}]"
    lines += [f"  apply {rule}", "  all_goals statclaim"]
    return "\n".join(lines)
