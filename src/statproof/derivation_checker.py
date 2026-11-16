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
    ONE_SAMPLE_ASSUMPTIONS,
    PLANNING_POINT_ASSUMPTION,
    RULES,
    TWO_STAGE_ASSUMPTIONS,
)

SUPPORTED_NULLS = {"tests.fisher/fisher": ["equal_proportions"]}
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
        if subject["test"] != "fisher":
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
