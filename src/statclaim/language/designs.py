"""Builders for assignments, outcomes, two-arm models and their checks."""

import json
from collections.abc import Callable, Iterator
from dataclasses import replace
from fractions import Fraction

from statclaim.language.core import (
    LocatedValue,
    fail,
)
from statclaim.language.ir import (
    AssignmentIR,
    ComposedFamilyIR,
    FamilyIR,
    OutcomeIR,
    OutcomeNullIR,
    StratumIR,
    TwoArmModelIR,
    two_arm_model,
)
from statclaim.language.normalize import (
    normalize,
)
from statclaim.language_syntax import (
    Span,
)
from statclaim.methods import OUTCOMES, methods_for
from statclaim.methods.assumptions import (
    CONTRADICTED_BY,
    POPULATIONS,
)
from statclaim.randomisation import (
    SCHEMES,
    groups_of,
)


def _declare_randomisation(
    assignment: AssignmentIR, arguments: dict[str, LocatedValue], span: Span
) -> AssignmentIR:
    """Add the declared randomisation scheme, strata and block size, checked to fit."""
    scheme, strata, block = (
        arguments.get(name) for name in ("randomisation", "strata", "block_size")
    )
    named = scheme is not None and scheme.value is not None
    detail = next(
        (item for item in (strata, block) if item is not None and item.value is not None), None
    )
    if not named:
        if detail is not None:
            fail(
                "domain",
                "strata and block_size describe how the assignment was randomised; declare "
                'randomisation="stratified" or "blocked" with them.',
                detail.span,
            )
        return assignment
    if scheme.value not in SCHEMES:
        fail(
            "domain",
            'randomisation must be "complete", "stratified" or "blocked": every split, within '
            "each stratum or block where declared, was equally likely. Minimisation and other "
            "schemes are not supported yet; leave randomisation out for them.",
            scheme.span,
        )
    layers = []
    for item in (strata.value or ()) if strata is not None else ():
        if not isinstance(item.value, StratumIR):
            fail("type", "Each stratum must be stratum(control=..., treatment=...).", item.span)
        layers.append((item.value.control, item.value.treatment))
    size = block.value if block is not None else None
    declared = replace(
        assignment, randomisation=scheme.value, strata=tuple(layers), block_size=size
    )
    try:
        groups_of(*declared.randomised_units[1:], scheme.value, tuple(layers), size)
    except ValueError as error:
        fail("domain", str(error), (detail or scheme).span)
    return declared


def _declare_population(
    assignment: AssignmentIR, arguments: dict[str, LocatedValue]
) -> AssignmentIR:
    """Add who is analysed, when the assignment declares it."""
    population = arguments.get("population")
    if population is None or population.value is None:
        return assignment
    if population.value not in POPULATIONS:
        fail(
            "domain",
            'population must be "randomised" (everyone randomised, analysed in the arm they '
            'were assigned to) or "per_protocol" (participants excluded after randomisation '
            "are left out). Leave it out if the file does not say.",
            population.span,
        )
    return replace(assignment, population=population.value)


def _arm_sizes(arguments: dict[str, LocatedValue]) -> AssignmentIR:
    for name in ("n_control", "n_treatment"):
        if arguments[name].value <= 0:
            fail("domain", f"{name} must be a positive integer.", arguments[name].span)
    return AssignmentIR(arguments["n_control"].value, arguments["n_treatment"].value)


def _assignment(arguments: dict[str, LocatedValue], span: Span) -> AssignmentIR:
    declared = _declare_randomisation(_arm_sizes(arguments), arguments, span)
    return _declare_population(declared, arguments)


def _stratum(arguments: dict[str, LocatedValue], span: Span) -> StratumIR:
    for name in ("control", "treatment"):
        if arguments[name].value < 0:
            fail("domain", f"{name} must be a whole number, zero or more.", arguments[name].span)
    if arguments["control"].value + arguments["treatment"].value == 0:
        fail("domain", "A stratum needs at least one unit.", span)
    return StratumIR(arguments["control"].value, arguments["treatment"].value)


def _cluster_assignment(arguments: dict[str, LocatedValue], span: Span) -> AssignmentIR:
    sizes = _arm_sizes(arguments)
    for arm in ("control", "treatment"):
        clusters, size = arguments[f"clusters_{arm}"], arguments[f"n_{arm}"].value
        if not 1 <= clusters.value <= size:
            fail(
                "domain",
                f"clusters_{arm} must be a positive integer no larger than n_{arm} ({size}).",
                clusters.span,
            )
    clustered = AssignmentIR(
        sizes.n_control,
        sizes.n_treatment,
        arguments["clusters_control"].value,
        arguments["clusters_treatment"].value,
    )
    declared = _declare_randomisation(clustered, arguments, span)
    return _declare_population(declared, arguments)


def _outcome_piece(kind: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> OutcomeIR:
        better = arguments["better"]
        if better.value not in (None, "higher", "lower"):
            fail("domain", 'better must be "higher" or "lower".', better.span)
        measurements = arguments.get("measurements")
        count = 1 if measurements is None or measurements.value is None else measurements.value
        if count < 1:
            fail("domain", "measurements must be a positive integer.", measurements.span)
        named = arguments.get("name")
        name = None if named is None or named.value is None else named.value.strip()
        if name is not None and (not name or "\n" in name or len(name) > MAX_NAME):
            fail(
                "domain",
                f'name must be one line of 1 to {MAX_NAME} characters, such as "response".',
                named.span,
            )
        return OutcomeIR(kind, better.value, count, name)

    return build


# Longest outcome name.
MAX_NAME = 100


def _leaves(members) -> Iterator[tuple[str, object]]:
    """The single analyses in a combination, inside nested ones too, with their names."""
    for name, analysis in members:
        if isinstance(analysis, (ComposedFamilyIR, FamilyIR)):
            yield from _leaves(analysis.analyses)
        else:
            yield name, analysis


def named_outcomes(members) -> list[str]:
    """The outcome names a combination's analyses declare, in order, each once."""
    names = (analysis.plan.model.measured.name for _, analysis in _leaves(members))
    return list(dict.fromkeys(name for name in names if name is not None))


def _question(analysis) -> str:
    """What an analysis asks, whatever its level: its test, its null and its design."""
    return json.dumps(
        {key: value for key, value in normalize(analysis).items() if key != "alpha"},
        sort_keys=True,
    )


def _outcome_words(outcome: OutcomeIR) -> str:
    better = f' with better="{outcome.better}"' if outcome.better else " with no better="
    return f"a {outcome.kind} outcome{better}"


def _check_named_outcomes(members, span: Span) -> None:
    """One name is one outcome, and a combination asks each question of it once."""
    first: dict[str, tuple[str, OutcomeIR]] = {}
    asked: dict[str, str] = {}
    for label, analysis in _leaves(members):
        outcome = analysis.plan.model.measured
        if outcome.name is None:
            continue
        earlier, seen = first.setdefault(outcome.name, (label, outcome))
        if (seen.kind, seen.better) != (outcome.kind, outcome.better):
            fail(
                "outcome_conflict",
                f'The outcome "{outcome.name}" is {_outcome_words(seen)} in {earlier} but '
                f"{_outcome_words(outcome)} in {label}. One name is one outcome; give different "
                "outcomes different names.",
                span,
            )
        question = _question(analysis)
        if question in asked:
            fail(
                "duplicate_analysis",
                f"{asked[question]} and {label} ask the same question of the outcome "
                f'"{outcome.name}": the same test of the same null on the same participants. '
                "Listed twice, one question would be reported as two. Keep one; if the other "
                "is a different outcome, give it its own name.",
                span,
            )
        asked[question] = label


# Lean-backed two-arm analyses rest on independent binomial arms (methods/identify.py).
BINOMIAL_ASSUMPTIONS = ("independent_binomial_arms",)


PLAIN_ASSUMPTIONS = {
    "independent_observations": "independent observations",
    "independent_participants": "independent participants",
    "independent_binomial_arms": "two independent binomial samples, one value per participant",
}


def _fitting(model) -> list[str]:
    """Registered tests for the model's outcome whose unit fits the assignment and whose
    assumptions no declared feature contradicts."""
    unit = "cluster" if model.assignment.clustered else "participant"
    contradicted = {a for feature in model.features for a in CONTRADICTED_BY[feature]}
    return [
        m.key
        for m in methods_for(model.outcome)
        if m.unit == unit and not {a.id for a in m.assumptions} & contradicted
    ]


def _design_remedy(feature: str, model) -> str:
    fitting = _fitting(model)
    if feature == "clusters":
        cited = (
            f"Use {', '.join(fitting)}, which takes one summary per cluster with the clusters "
            "as the sample size; or "
            if fitting
            else "Use "
        )
        return (
            f'{cited}randomisation_test, with randomisation="complete" declared on the '
            "assignment, whose level Lean proves. For another analysis that accounts for "
            "clustering, such as a mixed model with a random effect for cluster, use "
            "declared_test(...)."
        )
    kind = "that fits this design" if model.assignment.clustered else "for repeated measurements"
    tests = f"a test {kind} ({', '.join(fitting)})" if fitting else None
    summary = (
        "declare one value per participant, such as the final visit or the mean, as an "
        "outcome with one measurement"
    )
    return f"Use {tests}, or {summary}." if tests else f"{summary.capitalize()}."


def check_design(model, assumptions: tuple[str, ...], test: str, span: Span) -> None:
    """Refuse a test whose assumptions the declared design contradicts."""
    for feature in getattr(model, "features", ()):
        contradicted = [a for a in assumptions if a in CONTRADICTED_BY[feature]]
        if not contradicted:
            continue
        assumed = PLAIN_ASSUMPTIONS.get(contradicted[0], contradicted[0])
        if feature == "clusters":
            design = (
                f"the assignment randomises whole clusters ({model.assignment.clusters_control} "
                f"control and {model.assignment.clusters_treatment} treatment clusters), and "
                "participants in one cluster tend to be alike"
            )
        else:
            design = (
                f"the outcome is measured {model.measured.measurements} times on each "
                "participant, and measurements on one participant are correlated"
            )
        fail(
            "unit_mismatch",
            f"{test} assumes {assumed}, but {design}. The test would overstate the evidence. "
            f"{_design_remedy(feature, model)}",
            span,
        )


def _model_from_sizes(kind: str) -> Callable:
    """The one-call spelling: the same assignment and outcome as two_arm(...)."""

    def build(arguments: dict[str, LocatedValue], span: Span) -> TwoArmModelIR:
        return two_arm_model(_assignment(arguments, span), _outcome_piece(kind)(arguments, span))

    return build


def _two_arm(arguments: dict[str, LocatedValue], span: Span) -> TwoArmModelIR:
    return two_arm_model(arguments["assignment"].value, arguments["outcome"].value)


def _check_direction(form, model, span: Span) -> None:
    """A one-sided null must favour the treatment in the direction the model calls better."""
    if form.favours is None or model.better is None or form.favours == model.better:
        return
    outcome = OUTCOMES[model.outcome]
    mirror = next((f for f in outcome.nulls if f.favours == model.better), None)
    remedy = (
        f"Use {mirror.key}(...) to ask whether the treatment's outcome is {model.better}."
        if mirror
        else "No null for this outcome asks the other way. State the complementary outcome "
        "instead, such as alive rather than dead, for which higher is better."
    )
    fail(
        "direction_mismatch",
        f"{form.key} asks whether the treatment's outcome is {form.favours}, but the model "
        f'declares better="{model.better}". {remedy}',
        span,
    )


def _outcome_null(outcome, form) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> OutcomeNullIR:
        model = arguments["model"]
        if model.value.outcome != outcome.key:
            fail(
                "type",
                f"{form.key} is a null for a {outcome.key} outcome; this model's outcome is "
                f"{model.value.outcome}.",
                model.span,
            )
        _check_direction(form, model.value, span)
        value = arguments["value"].value if form.takes_value else Fraction(0)
        return OutcomeNullIR(model.value, form.key, value)

    return build
