"""Independent checker for contract derivations.

The checker receives a serialized derivation and trusts none of it. It reads
the facts from the serialized subject, re-evaluates every premise with its own
code, and confirms the derivation's structure: the rules exist, each step's
facts and conclusion are the ones the subject implies, the final step rests on
the required earlier steps, and the open obligations are exactly the obligation
rules that fail.

It shares the rule statements with `derivations` (they are data), and nothing
else: it does not call the contract code or the functions that build derivations.
A rule name or a success flag alone never passes.
"""

from fractions import Fraction

from statproof.derivations import (
    ANALYSIS_ASSUMPTIONS,
    FAMILY_ASSUMPTIONS,
    NOT_ESTABLISHED,
    RULES,
)

SUPPORTED_NULLS = {"tests.fisher/fisher": ["equal_proportions"]}
SUPPORTED_JOINT_LAWS = ["binomial_marginals"]
FAMILY_LIMITS = (2, 20)


def _sizes(model: dict) -> dict:
    return {"n_control": model["n_control"], "n_treatment": model["n_treatment"]}


def _statement(null: dict) -> str:
    if null["predicate"] == "equal_proportions":
        return "p_treatment = p_control"
    operator = "=" if null["predicate"] == "proportion_difference" else "<="
    return f"p_treatment - p_control {operator} {null['value']}"


def _analysis_expectations(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    """(rule, facts, premise holds) for the three premises of the analysis contract."""
    design, null = analysis["design"], analysis["null"]
    supported = SUPPORTED_NULLS["tests.fisher/fisher"]
    alpha = Fraction(analysis["alpha"])
    return [
        (
            "same-model",
            {
                "subject": name,
                "design_model": _sizes(design["model"]),
                "null_model": _sizes(null["model"]),
            },
            _sizes(design["model"]) == _sizes(null["model"]),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": _statement(null),
                "supported": supported,
            },
            null["predicate"] in supported,
        ),
        ("level-range", {"subject": name, "alpha": analysis["alpha"]}, 0 <= alpha <= 1),
    ]


def _sampling_expectation(name: str, analysis: dict) -> tuple[str, dict, bool]:
    stopping = analysis["design"]["stopping"]
    return ("fixed-sampling", {"subject": name, "stopping": stopping}, stopping == "fixed")


def _expected(derivation: dict) -> tuple[list[tuple], list[tuple], tuple[str, ...]]:
    """What the subject implies: required steps, obligation rules, assumptions.

    A required step is (rule, facts, holds, rules or step groups it must use).
    """
    name, subject, contract = derivation["name"], derivation["subject"], derivation["contract"]
    if contract == "tests.fisher/fisher":
        premises = _analysis_expectations(name, subject)
        steps = [(rule, facts, holds, ()) for rule, facts, holds in premises]
        steps.append(("analysis-contract", {"subject": name}, True, tuple(range(3))))
        return steps, [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract == "multiplicity.bonferroni/bonferroni":
        members = [(item["name"], item["analysis"]) for item in subject["analyses"]]
        names = [member for member, _ in members]
        steps, finals = [], []
        for member, analysis in members:
            start = len(steps)
            for rule, facts, holds in _analysis_expectations(member, analysis):
                steps.append((rule, facts, holds, ()))
            steps.append(
                ("analysis-contract", {"subject": member}, True, tuple(range(start, start + 3)))
            )
            finals.append(len(steps) - 1)
        low, high = FAMILY_LIMITS
        base = len(steps)
        steps += [
            (
                "distinct-members",
                {"subject": name, "members": names},
                len(set(names)) == len(names),
                (),
            ),
            ("family-size", {"subject": name, "count": len(names)}, low <= len(names) <= high, ()),
            (
                "joint-law",
                {"subject": name, "joint_law": subject["joint_law"]},
                subject["joint_law"] in SUPPORTED_JOINT_LAWS,
                (),
            ),
        ]
        steps.append(
            (
                "family-contract",
                {"subject": name, "members": names},
                True,
                (*finals, base, base + 1, base + 2),
            )
        )
        allocated = sum((Fraction(analysis["alpha"]) for _, analysis in members), Fraction())
        obligations = [
            (
                "allocation",
                {"subject": name, "allocated": str(allocated), "alpha": subject["alpha"]},
                allocated <= Fraction(subject["alpha"]),
            )
        ]
        obligations += [_sampling_expectation(member, analysis) for member, analysis in members]
        return steps, obligations, FAMILY_ASSUMPTIONS
    raise ValueError(f"unknown contract {contract!r}")


def check_derivation(derivation: dict) -> list[str]:
    """Return the problems found; an empty list means the derivation is valid."""
    problems: list[str] = []
    try:
        if derivation.get("scope") != "compatibility":
            problems.append("A derivation must be scoped to compatibility.")
        if derivation.get("not_established") != NOT_ESTABLISHED:
            problems.append("The statement of what is not established is missing or altered.")
        required, obligation_rules, assumptions = _expected(derivation)
        steps = derivation["steps"]
        for index, step in enumerate(steps):
            rule = RULES.get(step.get("rule"))
            if rule is None:
                problems.append(f"Step {index + 1} names an unknown rule.")
            elif step.get("premise") != rule.premise:
                problems.append(f"Step {index + 1} misstates the premise of {step['rule']}.")
            if any(not isinstance(use, int) or not 0 <= use < index for use in step["uses"]):
                problems.append(f"Step {index + 1} uses a step that does not precede it.")
        # The required steps must appear, in order, as the leading steps.
        for index, (rule, facts, holds, uses) in enumerate(required):
            label = f"Step {index + 1} ({rule})"
            if index >= len(steps):
                problems.append(f"{label} is missing.")
                continue
            step = steps[index]
            if step["rule"] != rule:
                problems.append(f"{label}: found rule {step['rule']!r} instead.")
                continue
            if step["facts"] != facts:
                problems.append(f"{label}: the recorded facts do not match the declaration.")
            if not holds:
                problems.append(f"{label}: the premise does not hold for the declaration.")
            if step["conclusion"] != RULES[rule].conclusion.format(**facts):
                problems.append(f"{label}: the conclusion is not the rule's conclusion.")
            if tuple(step["uses"]) != uses:
                problems.append(f"{label}: it does not rest on the required earlier steps.")
        if required and len(steps) >= len(required):
            final = RULES[required[-1][0]].conclusion.format(**required[-1][1])
            if derivation["conclusion"] != final:
                problems.append("The stated conclusion is not the conclusion of the contract rule.")
        # Obligation rules: a step when the premise holds, an open obligation when not.
        extra = steps[len(required) :]
        expected_steps = [(rule, facts) for rule, facts, holds in obligation_rules if holds]
        expected_open = [(rule, facts) for rule, facts, holds in obligation_rules if not holds]
        if [(step["rule"], step["facts"]) for step in extra] != expected_steps:
            problems.append("The steps for obligation rules do not match the declaration.")
        for step in extra:
            rule = RULES.get(step["rule"])
            if rule and step["conclusion"] != rule.conclusion.format(**step["facts"]):
                problems.append(f"The conclusion recorded for {step['rule']} is altered.")
        recorded = [(item["rule"], item["facts"]) for item in derivation["obligations"]]
        if recorded != expected_open:
            problems.append("The unresolved obligations do not match the declaration.")
        for item in derivation["obligations"]:
            rule = RULES.get(item["rule"])
            if rule is None or rule.obligation is None:
                problems.append("An obligation names a rule that cannot leave an obligation.")
            elif item["code"] != rule.code or item["statement"] != rule.obligation.format(
                **item["facts"]
            ):
                problems.append(f"The obligation recorded for {item['rule']} is altered.")
        if tuple(derivation["assumptions"]) != assumptions:
            problems.append("The required assumptions do not match the contract.")
    except (KeyError, TypeError, ValueError, IndexError, ZeroDivisionError) as error:
        problems.append(f"Malformed derivation: {error}")
    return problems
