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

from statclaim.derivations import (
    ANALYSIS_ASSUMPTIONS,
    CITED_NOT_ESTABLISHED,
    COMPOSED_NOT_ESTABLISHED,
    CONTRACT_IDS,
    FAMILY_ASSUMPTIONS,
    NOT_ESTABLISHED,
    ONE_SAMPLE_ASSUMPTIONS,
    PLANNING_POINT_ASSUMPTION,
    RULES,
    TWO_STAGE_ASSUMPTIONS,
)
from statclaim.methods import METHODS, NULL_FORMS, OUTCOMES
from statclaim.methods.assumptions import (
    FIXED_SIZES,
    PRESPECIFIED_FAMILY,
    PRESPECIFIED_LOOKS,
    PRESPECIFIED_ORDER,
    SINGLE_ANALYSIS,
)
from statclaim.methods.core import Guarantee

SUPPORTED_NULLS = {
    "two_sided": ["equal_proportions"],
    # The one-sided test fixes the margin at zero.
    "greater": ["proportion_difference_at_most"],
    # The difference test takes any margin strictly between -1 and 1.
    "margin": ["proportion_difference_at_most"],
}
SUPPORTED_JOINT_LAWS = ["binomial_marginals"]
FAMILY_LIMITS = (2, 20)
ONE_ARM_LIMIT, PER_ARM_LIMIT, STAGE_LIMIT, SEARCH_LIMIT, RATIO_LIMIT = 1000, 500, 200, 120, 10
CRITERIA = ["optimal", "minimax"]


def _whole(value, minimum: int) -> bool:
    return type(value) is int and value >= minimum


def _probability(text: str) -> bool:
    return 0 <= Fraction(text) <= 1


def _one_sample_expectations(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    n, rate = analysis["model"]["n"], analysis["null_rate"]
    return [
        ("sample-size-range", {"subject": name, "n": n}, _whole(n, 1) and n <= ONE_ARM_LIMIT),
        ("null-rate-interior", {"subject": name, "rate": rate}, 0 < Fraction(rate) < 1),
        (
            "level-range",
            {"subject": name, "alpha": analysis["alpha"]},
            _probability(analysis["alpha"]),
        ),
    ]


def _rule_well_formed(rule: dict) -> bool:
    if rule["kind"] == "threshold":
        return _whole(rule["continue_above"], 0) and _whole(rule["reject_above"], 0)
    if rule["kind"] == "posterior":
        return (
            _whole(rule["prior_a"], 1)
            and _whole(rule["prior_b"], 1)
            and 0 < Fraction(rule["reference"]) < 1
            and _probability(rule["continue_at_least"])
            and _probability(rule["success_at_least"])
        )
    return False


def _two_stage_expectations(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    first, second = analysis["design"]["n_stage1"], analysis["design"]["n_stage2"]
    sizes_ok = all(_whole(size, 1) and size <= STAGE_LIMIT for size in (first, second))
    return [
        ("stage-sizes", {"subject": name, "n_stage1": first, "n_stage2": second}, sizes_ok),
        (
            "null-rate",
            {"subject": name, "rate": analysis["null_rate"]},
            _probability(analysis["null_rate"]),
        ),
        (
            "decision-rule",
            {"subject": name, "rule": analysis["rule"]},
            _rule_well_formed(analysis["rule"]),
        ),
    ]


def _search_valid(search: dict) -> bool:
    if "max_per_arm" in search:
        ratio = (
            1 if search["allocation"] == "equal_arms" else int(search["allocation"].split(":")[1])
        )
        low, high = search["min_per_arm"], search["max_per_arm"]
        return (
            _whole(low, 1)
            and _whole(high, low)
            and 1 <= ratio <= RATIO_LIMIT
            and high * ratio <= PER_ARM_LIMIT
        )
    if "max_n" in search:
        return (
            _whole(search["min_n"], 1)
            and _whole(search["max_n"], search["min_n"])
            and (search["max_n"] <= ONE_ARM_LIMIT)
        )
    return (
        _whole(search["max_total"], 2)
        and search["max_total"] <= SEARCH_LIMIT
        and search["criterion"] in CRITERIA
        and 0 < Fraction(search["null_rate"]) < 1
    )


# The contract rule and assumptions for each kind of analysis, keyed by its test.
BLOCKS = {
    "fisher": ("analysis-contract", ANALYSIS_ASSUMPTIONS),
    "binomial_exact_one_sided": ("one-sample-contract", ONE_SAMPLE_ASSUMPTIONS),
    "two_stage": ("two-stage-contract", TWO_STAGE_ASSUMPTIONS),
}


def _premises(name: str, analysis: dict) -> list[tuple[str, dict, bool]]:
    if analysis["test"] == "fisher":
        return _analysis_expectations(name, analysis)
    if analysis["test"] == "binomial_exact_one_sided":
        return _one_sample_expectations(name, analysis)
    if analysis["test"] == "two_stage":
        return _two_stage_expectations(name, analysis)
    raise ValueError(f"unknown analysis {analysis['test']!r}")


def _block(name: str, analysis: dict, start: int = 0) -> list[tuple]:
    """The premises of an analysis followed by its contract rule."""
    steps = [(rule, facts, holds, ()) for rule, facts, holds in _premises(name, analysis)]
    uses = tuple(range(start, start + len(steps)))
    steps.append((BLOCKS[analysis["test"]][0], {"subject": name}, True, uses))
    return steps


def _planning_expected(derivation: dict) -> tuple[list[tuple], list[tuple], tuple[str, ...]]:
    name, claim = derivation["name"], derivation["subject"]
    if derivation["contract"] != f"planning/{claim['kind']}":
        raise ValueError("the contract does not match the claim")
    subject = claim["subject"]
    search = subject.get("candidates")
    if (search is not None) != (claim["kind"] == "sample_size"):
        raise ValueError("a search accompanies exactly the sample_size claim")
    analysis = subject["analysis"] if search is None else search.get("analysis")
    target, inner = subject["target"], f"{name}.analysis"
    steps, used = [], []
    if analysis is not None:
        steps = _block(inner, analysis)
        used.append(len(steps) - 1)
        assumptions = BLOCKS[analysis["test"]][1]
    else:
        assumptions = TWO_STAGE_ASSUMPTIONS
    two_arm = analysis is not None and analysis["test"] == "fisher"
    point = target["at"]
    kind = "two_arm" if two_arm else "single_arm"
    steps.append(
        (
            "planning-point",
            {"subject": name, "analysis": kind, "point": point},
            ("p_control" in point and "p_treatment" in point) == two_arm
            and ("response_rate" in point) != two_arm,
            (),
        )
    )
    used.append(len(steps) - 1)
    if "p_control" in point:
        facts = {
            "subject": name,
            "p_control": point["p_control"],
            "p_treatment": point["p_treatment"],
            "null": "p_treatment = p_control",
        }
        outside = Fraction(point["p_control"]) != Fraction(point["p_treatment"])
        kind = analysis.get("alternative", "two_sided") if two_arm else "two_sided"
        gap = Fraction(point["p_treatment"]) - Fraction(point["p_control"])
        if kind == "greater":
            facts["null"] = "p_treatment <= p_control"
            outside = gap > 0
        elif kind == "margin":
            facts["null"] = f"p_treatment - p_control <= {analysis['null']['value']}"
            outside = gap > Fraction(analysis["null"]["value"])
    else:
        null_rate = search["null_rate"] if analysis is None else analysis["null_rate"]
        facts = {
            "subject": name,
            "rate": point["response_rate"],
            "null_rate": null_rate,
            "null": f"response rate <= {null_rate}",
        }
        outside = Fraction(point["response_rate"]) > Fraction(null_rate)
    steps.append(("alternative", facts, outside, ()))
    used.append(len(steps) - 1)
    minimum, maximum = target["minimum_power"], target["maximum_typeI"]
    steps.append(
        (
            "target-range",
            {"subject": name, "minimum": minimum, "maximum_typeI": maximum},
            0 < Fraction(minimum) <= 1 and _probability(maximum),
            (),
        )
    )
    used.append(len(steps) - 1)
    if search is not None:
        bounds = {key: value for key, value in search.items() if key != "analysis"}
        steps.append(
            ("search-range", {"subject": name, "search": bounds}, _search_valid(bounds), ())
        )
        used.append(len(steps) - 1)
    steps.append(("planning-contract", {"subject": name}, True, tuple(used)))
    obligations = []
    if two_arm:
        obligations.append(
            (
                "error-budget",
                {"subject": name, "alpha": analysis["alpha"], "maximum_typeI": maximum},
                Fraction(analysis["alpha"]) <= Fraction(maximum),
            )
        )
        obligations.append(_sampling_expectation(inner, analysis))
    return steps, obligations, (*assumptions, PLANNING_POINT_ASSUMPTION)


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
    alternative = analysis.get("alternative", "two_sided")
    supported = SUPPORTED_NULLS[alternative]
    null_ok = null["predicate"] in supported and (
        alternative == "two_sided"
        or (alternative == "greater" and Fraction(null["value"]) == 0)
        or (alternative == "margin" and -1 < Fraction(null["value"]) < 1)
    )
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
            null_ok,
        ),
        ("level-range", {"subject": name, "alpha": analysis["alpha"]}, 0 <= alpha <= 1),
    ]


def _null_statement(null: dict) -> str:
    """The statement of a registered null form, from the registry's data."""
    form = NULL_FORMS[null["predicate"]][1]
    return form.state(Fraction(null["value"]) if form.takes_value else Fraction(0))


def _cited_expected(name: str, subject: dict, contract: str):
    """Steps, obligations, assumptions and guarantee for a cited method's contract.

    The method registry is data, like the rules. The premises are re-evaluated here.
    """
    method = METHODS.get(subject["test"])
    if method is None or contract != f"{method.module}/{method.key}":
        raise ValueError("the contract does not match the declaration")
    design, null = subject["design"], subject["null"]
    sizes, alpha = _sizes(design["model"]), Fraction(subject["alpha"])
    expected_model = OUTCOMES[method.outcome].constructor
    continuous = all(
        model["module"] == expected_model for model in (design["model"], null["model"])
    )
    enough = min(sizes.values()) >= method.min_per_arm and sum(sizes.values()) >= method.min_total
    steps = [
        (
            "same-model",
            {"subject": name, "design_model": sizes, "null_model": _sizes(null["model"])},
            continuous and sizes == _sizes(null["model"]),
            (),
        ),
        (
            "supported-null",
            {
                "subject": name,
                "predicate": null["predicate"],
                "statement": _null_statement(null),
                "supported": [method.null],
            },
            null["predicate"] == method.null,
            (),
        ),
        ("level-interior", {"subject": name, "alpha": subject["alpha"]}, 0 < alpha < 1, ()),
        (
            "enough-data",
            {
                "subject": name,
                **sizes,
                "min_per_arm": method.min_per_arm,
                "min_total": method.min_total,
            },
            enough,
            (),
        ),
        ("cited-contract", {"subject": name}, True, (0, 1, 2, 3)),
    ]
    fixed = _sampling_expectation(name, subject)
    guarantee = None
    if fixed[2]:
        statement = Guarantee(
            "type_I_error",
            method.relation,
            alpha,
            _null_statement(null),
            method.scope,
            method.limit,
        )
        guarantee = {
            **statement.to_dict(),
            "sentence": statement.sentence,
            "grade": "cited",
            "method": method.to_dict(),
            "given": [item.id for item in method.assumptions],
            "references": list(method.references),
        }
    return steps, [fixed], tuple(item.text for item in method.assumptions), guarantee


MEMBER_GRADES = {
    "proved": "provable in Lean; verify the member's own Type I claim",
    "cited": "cited from the literature; not machine-checked",
    "conditional": "holds if each of its own looks' bounds holds; verify its own Type I claim",
}


COMPOSITIONS = {
    # method: (contract, the assumption it adds, member assumptions it replaces,
    #          concluding rule, levels are split, error quantity, what must grow)
    "bonferroni": (
        "multiplicity.bonferroni/bonferroni",
        PRESPECIFIED_FAMILY,
        (),
        "composed-family-contract",
        True,
        "familywise_error",
        "each member's sample size or number of events grows",
    ),
    "alpha_spending": (
        "designs.group_sequential/alpha_spending",
        PRESPECIFIED_LOOKS,
        (FIXED_SIZES.text, SINGLE_ANALYSIS.text),
        "sequential-contract",
        True,
        "type_I_error",
        "the sample size at each look grows",
    ),
    "fixed_sequence": (
        "multiplicity.fixed_sequence/fixed_sequence",
        PRESPECIFIED_ORDER,
        (),
        "fixed-sequence-contract",
        False,
        "familywise_error",
        "each member's sample size or number of events grows",
    ),
}


def _combination(name: str, subject: dict, offset: int = 0, nested: bool = False) -> dict:
    """What a combination's declaration implies, re-derived from the serialized subject.

    Step indices are absolute: `offset` is the number of steps before this block.
    """
    method_name = subject.get("method")
    if method_name not in COMPOSITIONS or subject.get("composition") != "conditional":
        raise ValueError("not a conditional combination")
    contract, own, discharged, rule, splits, quantity, limit = COMPOSITIONS[method_name]
    sequential = method_name == "alpha_spending"
    if nested and not sequential:
        raise ValueError("only a design with looks may be a member")
    members = [(item["name"], item["analysis"]) for item in subject["analyses"]]
    names = [member for member, _ in members]
    steps: list[tuple] = []
    finals, inner_obligations, components = [], [], []
    own_texts, nested_texts, cited_texts = [own.text], [], []
    exact, keys, nulls = True, [], []
    for member, analysis in members:
        start = offset + len(steps)
        if "test" not in analysis:
            if sequential:
                raise ValueError("a look must be a single analysis")
            block = _combination(member, analysis, start, nested=True)
            steps += block["steps"]
            inner_obligations += block["obligations"]
            nested_texts += [
                text for text in (*block["own"], *block["nested"]) if text not in nested_texts
            ]
            cited_texts += [text for text in block["cited"] if text not in cited_texts]
            null, grade, scope = block["null"], "conditional", block["scope"]
            basis = block["contract"]
            keys.append("design")
        elif analysis["test"] in METHODS:
            method = METHODS[analysis["test"]]
            block_steps, fixed, texts, _ = _cited_expected(
                member, analysis, f"{method.module}/{method.key}"
            )
            steps += [(r, f, h, tuple(start + u for u in uses)) for r, f, h, uses in block_steps]
            inner_obligations += fixed
            cited_texts += [
                text for text in texts if text not in cited_texts and text not in discharged
            ]
            null, grade, scope = _null_statement(analysis["null"]), "cited", method.scope
            basis = f"{method.module}/{method.key} version {method.version}"
            keys.append(method.key)
        elif analysis["test"] == "fisher":
            for rule_name, facts, holds in _analysis_expectations(member, analysis):
                steps.append((rule_name, facts, holds, ()))
            steps.append(
                ("analysis-contract", {"subject": member}, True, tuple(range(start, start + 3)))
            )
            inner_obligations.append(_sampling_expectation(member, analysis))
            null, grade, scope = _statement(analysis["null"]), "proved", "finite_sample"
            basis = CONTRACT_IDS[analysis.get("alternative", "two_sided")]
            keys.append(basis.split("/")[1])
        else:
            raise ValueError("a member's analysis cannot be combined")
        finals.append(offset + len(steps) - 1)
        if "test" in analysis:
            nulls.append((analysis["null"]["predicate"], analysis["null"].get("value")))
        exact = exact and scope == "finite_sample"
        components.append(
            {
                "name": member,
                "level": analysis["alpha"],
                "scope": scope,
                "grade": grade,
                "basis": basis,
                "null": null,
            }
        )
        bound = Guarantee(
            "type_I_error", "at_most", Fraction(analysis["alpha"]), null, "finite_sample"
        )
        own_texts.append(f"{member}: {bound.sentence} ({MEMBER_GRADES[grade]})")
    if method_name == "bonferroni" and all(key == "fisher" for key in keys):
        raise ValueError("a family of two-sided Fisher analyses is proved, not conditional")
    low, high = FAMILY_LIMITS
    base = offset + len(steps)
    distinct = len(set(names)) == len(names)
    steps += [
        ("distinct-members", {"subject": name, "members": names}, distinct, ()),
        ("family-size", {"subject": name, "count": len(names)}, low <= len(names) <= high, ()),
    ]
    used = [*finals, base, base + 1]
    alpha = Fraction(subject["alpha"])
    if sequential:
        sizes = [
            [a["design"]["model"]["n_control"], a["design"]["model"]["n_treatment"]]
            for _, a in members
        ]
        modules = {a["design"]["model"]["module"] for _, a in members}
        grows = all(
            later[0] >= earlier[0] and later[1] >= earlier[1] and sum(later) > sum(earlier)
            for earlier, later in zip(sizes, sizes[1:], strict=False)
        )
        steps += [
            (
                "same-question",
                {"subject": name, "test": keys[0], "statement": components[0]["null"]},
                len(set(keys)) == 1 and len(set(nulls)) == 1 and len(modules) == 1,
                (),
            ),
            ("increasing-looks", {"subject": name, "sizes": sizes}, grows, ()),
        ]
        used += [base + 2, base + 3]
    if not splits:
        full = all(Fraction(analysis["alpha"]) == alpha for _, analysis in members)
        steps.append(("full-level", {"subject": name, "alpha": subject["alpha"]}, full, ()))
        used.append(base + 2)
    steps.append((rule, {"subject": name, "members": names}, True, tuple(used)))
    obligations = []
    if splits:
        allocated = sum((Fraction(analysis["alpha"]) for _, analysis in members), Fraction())
        obligations.append(
            (
                "allocation",
                {"subject": name, "allocated": str(allocated), "alpha": subject["alpha"]},
                allocated <= alpha,
            )
        )
    obligations += inner_obligations
    scope = "finite_sample" if exact else "asymptotic"
    null = components[0]["null"] if sequential else "any subset of the member nulls is true"
    statement = Guarantee(quantity, "at_most", alpha, null, scope, limit)
    return {
        "contract": contract,
        "steps": steps,
        "obligations": obligations,
        "own": own_texts,
        "nested": nested_texts,
        "cited": cited_texts,
        "scope": scope,
        "null": components[0]["null"],
        "guarantee": {
            **statement.to_dict(),
            "sentence": statement.sentence,
            "grade": "conditional",
            "members": components,
            "given": [own.id, *(f"member_guarantee:{n}" for n in names)],
        },
    }


def _composed_expected(name: str, subject: dict, contract: str):
    """Steps, obligations, assumptions and guarantee of a combination's contract."""
    block = _combination(name, subject)
    if contract != block["contract"]:
        raise ValueError("the contract does not match the declaration")
    met = all(holds for _, _, holds in block["obligations"])
    return (
        block["steps"],
        block["obligations"],
        (*block["own"], *block["nested"], *block["cited"]),
        block["guarantee"] if met else None,
    )


def _carried(derivation: dict):
    """What a contract that carries a guarantee implies; None for any other contract."""
    subject = derivation.get("subject")
    if not isinstance(subject, dict):
        return None
    if subject.get("test") in METHODS:
        return _cited_expected(derivation["name"], subject, derivation["contract"])
    if subject.get("composition") == "conditional":
        return _composed_expected(derivation["name"], subject, derivation["contract"])
    return None


def _sampling_expectation(name: str, analysis: dict) -> tuple[str, dict, bool]:
    stopping = analysis["design"]["stopping"]
    return ("fixed-sampling", {"subject": name, "stopping": stopping}, stopping == "fixed")


def _expected(derivation: dict) -> tuple[list[tuple], list[tuple], tuple[str, ...]]:
    """What the subject implies: required steps, obligation rules, assumptions.

    A required step is (rule, facts, holds, rules or step groups it must use).
    """
    name, subject, contract = derivation["name"], derivation["subject"], derivation["contract"]
    carried = _carried(derivation)
    if carried is not None:
        return carried[:3]
    if contract in CONTRACT_IDS.values():
        if subject["test"] != "fisher" or contract != CONTRACT_IDS.get(
            subject.get("alternative", "two_sided")
        ):
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [_sampling_expectation(name, subject)], ANALYSIS_ASSUMPTIONS
    if contract in ("tests.binomial/binomial_test", "designs.two_stage/two_stage_test"):
        expected = "binomial_exact_one_sided" if "binomial" in contract else "two_stage"
        if subject["test"] != expected:
            raise ValueError("the contract does not match the declaration")
        return _block(name, subject), [], BLOCKS[expected][1]
    if contract in ("planning/meets", "planning/sample_size"):
        return _planning_expected(derivation)
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
        # A guarantee may be carried only by a contract that supplies one, and then
        # only the guarantee the declaration implies.
        carried = _carried(derivation)
        guarantee = carried[3] if carried else None
        if derivation.get("guarantee") != guarantee:
            problems.append("The recorded guarantee is not the one the declaration implies.")
        scope = "conditional_guarantee" if guarantee else "compatibility"
        if derivation.get("scope") != scope:
            problems.append("The derivation's scope does not match what it establishes.")
        if derivation.get("not_established") != (
            NOT_ESTABLISHED
            if not guarantee
            else COMPOSED_NOT_ESTABLISHED
            if guarantee["grade"] == "conditional"
            else CITED_NOT_ESTABLISHED
        ):
            problems.append("The statement of what is not established is missing or altered.")
        required, obligation_rules, assumptions = _expected(derivation)
        steps = derivation["steps"]
        for index, step in enumerate(steps):
            rule = RULES.get(step.get("rule"))
            if rule is None:
                problems.append(f"Step {index + 1} names an unknown rule.")
            elif step.get("premise") != rule.premise:
                problems.append(f"Step {index + 1} misstates the premise of {step['rule']}.")
            elif step.get("rule_version") != rule.version:
                problems.append(f"Step {index + 1} uses another version of {step['rule']}.")
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
