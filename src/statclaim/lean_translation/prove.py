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
    Combination,
    Contract,
    Graph,
    Part,
    Premise,
    combination_claim,
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


def premise(given: Premise) -> str:
    """How the witness meets a premise: a test or a procedure that never rejects."""
    if given.kind == "graph":
        marks = [subscript(k) for k in range(given.members)]
        views = " ".join(f"v{m}" for m in marks)
        marginals = " ".join(f"m{m}" for m in marks)
        return (
            f"⟨{INTERFACE}.Scope.permits_zero _, by\n"
            f"      intro Θ Ω _ σ {views} {marginals}\n"
            f"      exact {INTERFACE}.familywise_of_nothing σ.law _ (by norm_num [witness])⟩"
        )
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
        elif part.kind == "procedure":
            values.append(f"{part.name} := fun {' '.join(['_'] * part.arity)} => ∅")
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


def bounded_leaves(combination: Combination) -> list[Part]:
    """The single tests whose own bounds a proof needs: those not inside a graph, whose
    guarantee covers its members."""
    found = []
    for part in combination.parts:
        if part.leaf is not None and combination.rule != "graph":
            found.append(part)
        elif part.combination is not None:
            found += bounded_leaves(part.combination)
    return found


def graphs_within(combination: Combination) -> list[Graph]:
    """The graphs that are members somewhere inside a combination."""
    found = []
    for part in combination.parts:
        if part.combination is not None:
            if part.combination.graph is not None:
                found.append(part.combination.graph)
            found += graphs_within(part.combination)
    return found


def prove_combination(combination: Combination, lines: list[str], counter: list[int]) -> str:
    """Lines proving a combination's claim about σ; returns the hypothesis holding it."""
    index = counter[0]
    counter[0] += 1
    name = f"c{subscript(index)}"
    if combination.graph is not None:
        views = " ".join(f"v{subscript(part.view)}" for part in combination.parts)
        marginals = " ".join(f"m{subscript(part.view)}" for part in combination.parts)
        lines += [
            f"  have {name} : {combination_claim(combination)} :=",
            f"    premises.{lean(combination.graph.premise)}.2 Θ Ω σ {views} {marginals}",
        ]
        return name
    for part in combination.parts:
        if part.combination is None:
            continue
        inner = prove_combination(part.combination, lines, counter)
        if part.kind == "looks":
            lemma = f"{INTERFACE}.looks_member {inner}"
        elif part.combination.rule == "sequence":
            lemma = f"{INTERFACE}.sequence_member σ {inner}"
        else:
            lemma = f"{INTERFACE}.family_member σ {inner}"
        lines.append(f"  have n{subscript(counter[0])} := {lemma}")
        counter[0] += 1
    if combination.rule == "sequence":
        rule = f"{INTERFACE}.sequence_of_members σ _ _ {rational(combination.alpha)}"
    else:
        levels = ", ".join(rational(part.level) for part in combination.parts)
        rule = f"{INTERFACE}.familywise_of_members σ _ _ ![{levels}]"
    lines += [
        f"  have {name} : {combination_claim(combination)} := by",
        f"    apply {rule}",
        "    all_goals statclaim",
    ]
    return name


def claim(statement: Claim) -> str:
    analysis = statement.analysis
    if statement.kind == "typeI" and statement.combination is None:
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
    combination = statement.combination
    assert combination is not None
    marks = [subscript(k) for k in range(len(statement.leaves))]
    lines = [
        "by",
        f"  intro Θ Ω _ σ {' '.join(f'v{m}' for m in marks)} {' '.join(f'm{m}' for m in marks)}",
    ]
    for part in bounded_leaves(combination):
        member, mark = part.leaf, subscript(part.view)
        assert member is not None
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
    for index, graph in enumerate(graphs_within(combination)):
        lines.append(
            f"  have g{subscript(index)} : 0 ≤ i.{lean(graph.slack)} :=\n"
            f"    {INTERFACE}.Scope.permits_nonnegative premises.{lean(graph.premise)}.1"
        )
    final = prove_combination(combination, lines, [0])
    lines.append(f"  exact {final}")
    return "\n".join(lines)
