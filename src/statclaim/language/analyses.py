"""Builders for tests, observational studies, results, families and sequences."""

from collections.abc import Callable
from fractions import Fraction

from statclaim.association import (
    CELLS,
    MAX_PARTICIPANTS,
    NAME,
    not_estimable,
    table_problem,
)
from statclaim.family import MAX_ENDPOINTS
from statclaim.incidence import (
    proportion_not_estimable,
)
from statclaim.language.core import (
    Constructor,
    LocatedValue,
    _constructor,
    fail,
)
from statclaim.language.designs import (
    BINOMIAL_ASSUMPTIONS,
    _check_direction,
    _check_named_outcomes,
    _fitting,
    check_design,
)
from statclaim.language.ir import (
    EXACT_CONTRACT_IDS,
    AnalysisIR,
    AssociationAnalysisIR,
    AssociationNullIR,
    AssociationResultIR,
    AssociationTableIR,
    CaseControlStudyIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    ClaimIR,
    CohortStudyIR,
    ComposedFamilyIR,
    CrossSectionalStudyIR,
    EffectIntervalIR,
    FamilyIR,
    FamilyLikeIR,
    HypothesisIR,
    LevelTestIR,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedPairsIR,
    MatchedResultIR,
    MatchedStudyIR,
    ObservationalStudyIR,
    ObservationIR,
    ObservedEventsIR,
    PersonTimeStudyIR,
    PlanIR,
    ProportionIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateRatioIR,
    RateResultIR,
    SequentialIR,
    SharpNullIR,
    TwoArmModelIR,
)
from statclaim.language_contracts import (
    HypothesisContract,
)
from statclaim.language_syntax import (
    Span,
)
from statclaim.matched import (
    MAX_PAIRS,
    PAIR_CELLS,
    pairs_problem,
)
from statclaim.methods import NULL_FORMS
from statclaim.methods.assumptions import (
    DECLARED_VALID,
)
from statclaim.methods.boundaries import SPENDING, floor_level
from statclaim.methods.boundaries import limits as boundary_limits
from statclaim.methods.core import SCOPES, CitedMethod
from statclaim.methods.observational import (
    MAX_COVARIATES,
    SCALES,
    SURVEYS,
    ObservationalMethod,
)
from statclaim.methods.observational import (
    METHODS as OBSERVATIONAL_METHODS,
)
from statclaim.planning import (
    MAX_MARGIN_ARM,
)
from statclaim.randomisation import (
    MAX_DRAWS,
    MAX_UNITS,
    count_splits,
    splits_needed,
)


def _cited_test(method: CitedMethod) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> CitedAnalysisIR:
        design, alpha = arguments["design"], arguments["alpha"]
        _observational_refused(design, method.key)
        model = design.value.model
        if getattr(model, "outcome", None) != method.outcome:
            fail(
                "type",
                f"{method.key} is a test for a {method.outcome} outcome; this design's "
                "model is of another kind.",
                design.span,
            )
        if method.unit == "cluster" and not model.assignment.clustered:
            fail(
                "unit_mismatch",
                f"{method.key} takes one summary per cluster, with the clusters as the sample "
                "size, but the assignment randomises participants one by one. Declare "
                "cluster_assignment(...) if whole clusters were randomised; otherwise use a "
                "test of participants, such as t_test.",
                design.span,
            )
        sizes = (
            (model.assignment.clusters_control, model.assignment.clusters_treatment)
            if method.unit == "cluster"
            else (model.n_control, model.n_treatment)
        )
        if min(sizes) < method.min_per_arm or sum(sizes) < method.min_total:
            counted = "clusters " if method.unit == "cluster" else ""
            fail(
                "domain",
                f"{method.key} needs at least {method.min_per_arm} {counted}per arm and "
                f"{method.min_total} in total to estimate the variance"
                + (f"; this design randomises {sizes[0]} and {sizes[1]}." if counted else "."),
                design.span,
            )
        if not 0 < alpha.value < 1:
            fail("domain", "alpha must lie strictly between 0 and 1 for this test.", alpha.span)
        check_design(model, tuple(a.id for a in method.assumptions), method.key, design.span)
        return CitedAnalysisIR(design.value, arguments["null"].value, alpha.value, method)

    return build


def _declared_test(arguments: dict[str, LocatedValue], span: Span) -> CitedAnalysisIR:
    """A test the author names and vouches for. Nothing about it is checked or cited."""
    design, null, alpha = arguments["design"], arguments["null"], arguments["alpha"]
    _observational_refused(design, "declared_test")
    HypothesisContract((null.value.predicate,), null.value.statement, "").check(
        "declared_test", arguments
    )
    if not 0 < alpha.value < 1:
        fail("domain", "alpha must lie strictly between 0 and 1 for this test.", alpha.span)
    title = arguments["method"]
    if not title.value.strip() or "\n" in title.value or len(title.value) > 200:
        fail("domain", "method must be one line of at most 200 characters.", title.span)
    scope = arguments["scope"]
    if scope.value is not None and scope.value not in SCOPES:
        fail("domain", f"scope must be one of: {', '.join(SCOPES)}.", scope.span)
    reference = arguments["reference"]
    if reference.value is not None and (not reference.value.strip() or "\n" in reference.value):
        fail("domain", "reference must be one non-empty line.", reference.span)
    method = CitedMethod(
        key="declared_test",
        module="tests.declared",
        title=title.value.strip(),
        version=1,
        outcome=design.value.model.outcome,
        null=null.value.predicate,
        relation="at_most",
        # Without a stated scope, nothing exact is claimed.
        scope=scope.value or "asymptotic",
        assumptions=(DECLARED_VALID,),
        references=(reference.value.strip(),) if reference.value else (),
        min_per_arm=1,
        min_total=2,
        grade="declared",
    )
    return CitedAnalysisIR(design.value, null.value, alpha.value, method)


def _no_effect(arguments: dict[str, LocatedValue], span: Span) -> SharpNullIR:
    model = arguments["model"]
    _observational_refused(model, "no_effect")
    if not isinstance(model.value, TwoArmModelIR):
        fail("type", "no_effect is a null for a two-arm model.", model.span)
    return SharpNullIR(model.value)


def _randomisation_test(arguments: dict[str, LocatedValue], span: Span) -> RandomisationAnalysisIR:
    design, alpha = arguments["design"], arguments["alpha"]
    _observational_refused(design, "randomisation_test")
    assignment = design.value.model.assignment
    unit, units, treated = assignment.randomised_units
    if assignment.randomisation is None:
        constructor = "cluster_assignment" if assignment.clustered else "assignment"
        fail(
            "undeclared_randomisation",
            "randomisation_test needs the assignment to say how it was randomised: its level "
            "follows from the randomisation alone. If every split of the "
            f"{units} {unit}s into arms of these sizes was equally likely, declare "
            f'randomisation="complete" in {constructor}(...); for strata or blocks, declare '
            'randomisation="stratified" with strata=[...] or "blocked" with block_size=...',
            design.span,
        )
    if assignment.population == "per_protocol":
        model = design.value.model
        others = "fisher" if model.outcome == "binary" else next(iter(_fitting(model)), "")
        fail(
            "population_mismatch",
            "randomisation_test needs every randomised unit analysed, in the arm it was "
            "assigned to: its level comes from how exactly those units were randomised. The "
            'assignment declares population="per_protocol", which leaves out units excluded '
            "after randomisation, so the units analysed were not randomised as a set. Analyse "
            'everyone randomised and declare population="randomised"'
            + (
                f"; for a per-protocol analysis, use another test, such as {others}, whose "
                "claim says it covers the per-protocol population only."
                if others
                else "."
            ),
            design.span,
        )
    if units > MAX_UNITS:
        fail(
            "domain",
            f"randomisation_test supports up to {MAX_UNITS} randomised units; this design has "
            f"{units}.",
            design.span,
        )
    if alpha.value == 0:
        fail("domain", "alpha must be positive for this test.", alpha.span)
    drawn = arguments.get("draws")
    draws = drawn.value if drawn is not None else None
    if draws is not None:
        if not 1 <= draws <= MAX_DRAWS:
            fail("domain", f"draws must be a whole number from 1 to {MAX_DRAWS}.", drawn.span)
        if Fraction(1, draws + 1) > alpha.value:
            fail(
                "never_rejects",
                f"With {draws} drawn assignments, no Monte Carlo p-value is below "
                f"1/{draws + 1}, which is above the level {alpha.value}. The test can never "
                f"reject. Draw at least {splits_needed(alpha.value) - 1}.",
                drawn.span,
            )
        return RandomisationAnalysisIR(design.value, arguments["null"].value, alpha.value, draws)
    splits = count_splits(assignment.groups)
    if Fraction(1, splits) > alpha.value:
        grouped = assignment.randomisation != "complete"
        layout = f", in {len(assignment.groups)} strata or blocks" if grouped else ""
        fail(
            "never_rejects",
            f"With {units} {unit}s, {treated} treated{layout}, there are {splits} equally likely "
            f"splits, so no p-value is below 1/{splits}, which is above the level "
            f"{alpha.value}. The test can never reject. It needs at least "
            f"{splits_needed(alpha.value)} splits: randomise more {unit}s, use fewer strata or "
            "larger blocks, or use a larger level.",
            design.span,
        )
    return RandomisationAnalysisIR(design.value, arguments["null"].value, alpha.value)


def _observational_refused(design: LocatedValue, test: str) -> None:
    """Tests built on randomised arms refuse an observational design, whose exposure was
    not assigned."""
    model = design.value.model if isinstance(design.value, PlanIR) else design.value
    if isinstance(model, ObservationalStudyIR):
        fail(
            "observational_design",
            f"{test} relies on randomised arms, but this is an observational "
            f"{model.design.replace('_', '-')} study: exposure was not assigned. Use "
            "fisher_exact from tests.association to test association.",
            design.span,
        )


def _study_name(arguments: dict[str, LocatedValue], key: str) -> str:
    argument = arguments.get(key)
    if argument is None or argument.value is None:
        return key
    if not NAME.fullmatch(argument.value):
        fail(
            "domain",
            f"{key} names what is studied in a few plain words, starting with a letter, "
            "at most 60 characters.",
            argument.span,
        )
    return argument.value


def _size(arguments: dict[str, LocatedValue], key: str) -> int | None:
    argument = arguments.get(key)
    if argument is None or argument.value is None:
        return None
    if argument.value < 1:
        fail("domain", f"{key} must be a positive whole number.", argument.span)
    if argument.value > MAX_PARTICIPANTS:
        fail("domain", f"{key} may be at most {MAX_PARTICIPANTS}.", argument.span)
    return argument.value


def _choice(arguments: dict[str, LocatedValue], key: str, choices: dict, default: str) -> str:
    argument = arguments.get(key)
    if argument is None or argument.value is None:
        return default
    if argument.value not in choices:
        fail("domain", f"{key} must be one of: {', '.join(choices)}.", argument.span)
    return argument.value


def _study_options(arguments: dict[str, LocatedValue], span: Span, n: int | None = None) -> dict:
    """Names, measurement scales and the survey design, as a study declares them."""
    options = {
        "exposure": _study_name(arguments, "exposure"),
        "outcome": _study_name(arguments, "outcome"),
        "exposure_scale": _choice(arguments, "exposure_scale", SCALES, "binary"),
        "outcome_scale": _choice(arguments, "outcome_scale", SCALES, "binary"),
        "survey": _choice(arguments, "survey", SURVEYS, "simple_random"),
    }
    clusters = _size(arguments, "clusters")
    if options["survey"] == "cluster":
        if clusters is None:
            fail(
                "domain",
                "A cluster survey declares how many clusters it sampled: clusters=....",
                span,
            )
        if clusters < 2 or (n is not None and clusters > n):
            fail(
                "domain",
                "clusters must be at least 2 and at most the number sampled.",
                arguments["clusters"].span,
            )
    elif clusters is not None:
        fail(
            "domain",
            'clusters belongs to a cluster survey: declare survey="cluster" with it.',
            arguments["clusters"].span,
        )
    options["clusters"] = clusters
    return options


def _simple_binary(
    argument: LocatedValue, test: str, *, outcome: bool = True, exposure: bool = True
) -> None:
    """Proved methods need yes-or-no variables and simple random sampling."""
    model = argument.value.model if isinstance(argument.value, PlanIR) else argument.value
    if not isinstance(model, ObservationalStudyIR):
        return
    for wanted, which, scale in (
        (outcome, "outcome", model.outcome_scale),
        (exposure, "exposure", model.exposure_scale),
    ):
        if wanted and scale != "binary":
            fail(
                "type",
                f"{test} needs a yes-or-no {which}; this study declares a continuous {which}. "
                "For continuous variables use linear_association from tests.regression or "
                "pearson_correlation from tests.correlation.",
                argument.span,
            )
    if model.survey != "simple_random":
        fail(
            "complex_sample",
            f"{test} assumes participants were sampled independently with equal probability; "
            f"this survey declares {model.survey} sampling. Use a design-based test from "
            "tests.survey, such as survey_logistic or rao_scott_test.",
            argument.span,
        )


def _cross_sectional(arguments: dict[str, LocatedValue], span: Span) -> CrossSectionalStudyIR:
    n = _size(arguments, "n")
    return CrossSectionalStudyIR(n=n, **_study_options(arguments, span, n))


def _cohort(arguments: dict[str, LocatedValue], span: Span) -> CohortStudyIR:
    exposed, unexposed, n = (_size(arguments, key) for key in ("exposed", "unexposed", "n"))
    if n is not None and (exposed is not None or unexposed is not None):
        fail(
            "domain",
            "Declare either exposed and unexposed, when the cohort sampled the groups in fixed "
            "numbers, or n, when it sampled one population and exposure was measured; not both.",
            span,
        )
    if n is None and (exposed is None or unexposed is None):
        fail(
            "domain",
            "A cohort needs exposed and unexposed group sizes, or its total n when the number "
            "exposed was not fixed.",
            span,
        )
    total = n if n is not None else exposed + unexposed
    if total > MAX_PARTICIPANTS:
        fail("domain", f"A study may have at most {MAX_PARTICIPANTS} participants.", span)
    return CohortStudyIR(
        exposed=exposed, unexposed=unexposed, n=n, **_study_options(arguments, span, total)
    )


def _case_control(arguments: dict[str, LocatedValue], span: Span) -> CaseControlStudyIR:
    cases, controls = _size(arguments, "cases"), _size(arguments, "controls")
    if cases + controls > MAX_PARTICIPANTS:
        fail("domain", f"A study may have at most {MAX_PARTICIPANTS} participants.", span)
    return CaseControlStudyIR(
        cases=cases, controls=controls, **_study_options(arguments, span, cases + controls)
    )


def _no_association(arguments: dict[str, LocatedValue], span: Span) -> AssociationNullIR:
    return AssociationNullIR(arguments["model"].value)


def _fisher_exact(arguments: dict[str, LocatedValue], span: Span) -> AssociationAnalysisIR:
    design, null = arguments["design"], arguments["null"]
    _matched_refused(
        design,
        "fisher_exact ignores the matching, so its guarantee does not apply to matched pairs. "
        "Use mcnemar for a matched study.",
    )
    _rates_refused(
        design,
        "fisher_exact compares counts of participants; a person-time cohort counts events over "
        "person-time. Use rate_test.",
    )
    _simple_binary(design, "fisher_exact")
    if not isinstance(design.value.model, ObservationalStudyIR):
        fail(
            "type",
            "fisher_exact tests association in an observational study, but this design is a "
            "randomised trial. Use fisher from tests.fisher to compare randomised arms.",
            design.span,
        )
    if design.value.model != null.value.model:
        fail(
            "model_mismatch",
            "fisher_exact: the null belongs to a different study. Declare "
            "no_association(model=...) over the study the design samples.",
            null.span,
        )
    return AssociationAnalysisIR(design.value, null.value, arguments["alpha"].value)


def _matched_refused(argument: LocatedValue, message: str) -> None:
    model = argument.value.model if isinstance(argument.value, PlanIR) else argument.value
    if isinstance(model, MatchedStudyIR):
        fail("matched_design", message, argument.span)


def _matched_case_control(arguments: dict[str, LocatedValue], span: Span) -> MatchedStudyIR:
    pairs = arguments["pairs"]
    if not 1 <= pairs.value <= MAX_PAIRS:
        fail("domain", f"pairs must be a whole number from 1 to {MAX_PAIRS}.", pairs.span)
    return MatchedStudyIR(pairs=pairs.value, **_study_options(arguments, span, pairs.value))


def _observed_pairs(arguments: dict[str, LocatedValue], span: Span) -> MatchedPairsIR:
    _simple_binary(arguments["model"], "observed_pairs", outcome=False)
    model = arguments["model"].value
    cells = []
    for key in PAIR_CELLS:
        argument = arguments[key]
        if argument.value < 0:
            fail("domain", f"{key} must be a whole number, zero or more.", argument.span)
        cells.append(argument.value)
    problem = pairs_problem(model.pairs, cells)
    if problem:
        fail("domain", problem, span)
    return MatchedPairsIR(model, *cells)


def _mcnemar(arguments: dict[str, LocatedValue], span: Span) -> MatchedAnalysisIR:
    design, null = arguments["design"], arguments["null"]
    _simple_binary(design, "mcnemar", outcome=False)
    if not isinstance(design.value.model, MatchedStudyIR):
        fail(
            "type",
            "mcnemar tests matched pairs, but this design is not matched. For unmatched "
            "groups use fisher_exact.",
            design.span,
        )
    if design.value.model != null.value.model:
        fail(
            "model_mismatch",
            "mcnemar: the null belongs to a different study. Declare no_association(model=...) "
            "over the study the design samples.",
            null.span,
        )
    return MatchedAnalysisIR(design.value, null.value, arguments["alpha"].value)


def _matched_result(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis, observed = arguments["analysis"], arguments["pairs"]
    if analysis.value.plan.model != observed.value.model:
        fail(
            "model_mismatch",
            "matched_result: the pairs belong to another study than the analysis.",
            observed.span,
        )
    return ClaimIR(
        "result",
        MatchedResultIR(analysis.value, observed.value),
        observed.name or analysis.name or "<expression>",
    )


def _conditional_odds_ratio(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    observed, level = arguments["pairs"], arguments["level"]
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    interval = MatchedIntervalIR(observed.value, level.value)
    try:
        interval.lower()
    except ValueError as error:
        fail("domain", str(error), observed.span)
    return ClaimIR("interval", interval, observed.name or "<expression>")


def _rates_refused(argument: LocatedValue, message: str) -> None:
    model = argument.value.model if isinstance(argument.value, PlanIR) else argument.value
    if isinstance(model, PersonTimeStudyIR):
        fail("type", message, argument.span)


def _person_time_cohort(arguments: dict[str, LocatedValue], span: Span) -> PersonTimeStudyIR:
    return PersonTimeStudyIR(**_study_options(arguments, span))


def _observed_events(arguments: dict[str, LocatedValue], span: Span) -> ObservedEventsIR:
    _simple_binary(arguments["model"], "observed_events", outcome=False)
    values = {}
    for key in ("exposed_events", "unexposed_events"):
        if arguments[key].value < 0:
            fail("domain", f"{key} must be a whole number, zero or more.", arguments[key].span)
        values[key] = arguments[key].value
    for key in ("exposed_time", "unexposed_time"):
        if arguments[key].value <= 0:
            fail("domain", f"{key} must be positive person-time.", arguments[key].span)
        values[key] = arguments[key].value
    events = ObservedEventsIR(
        arguments["model"].value,
        values["exposed_events"],
        values["exposed_time"],
        values["unexposed_events"],
        values["unexposed_time"],
    )
    try:
        events.lower()
    except ValueError as error:
        fail("domain", str(error), span)
    return events


def _rate_test(arguments: dict[str, LocatedValue], span: Span) -> RateAnalysisIR:
    design, null = arguments["design"], arguments["null"]
    _simple_binary(design, "rate_test", outcome=False)
    if not isinstance(design.value.model, PersonTimeStudyIR):
        fail(
            "type",
            "rate_test compares incidence rates over person-time, but this design does not "
            "count person-time. Use person_time_cohort, or fisher_exact to compare counts.",
            design.span,
        )
    if design.value.model != null.value.model:
        fail(
            "model_mismatch",
            "rate_test: the null belongs to a different study. Declare "
            "no_association(model=...) over the study the design samples.",
            null.span,
        )
    return RateAnalysisIR(design.value, null.value, arguments["alpha"].value)


def _rate_result(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis, events = arguments["analysis"], arguments["events"]
    if analysis.value.plan.model != events.value.model:
        fail(
            "model_mismatch",
            "rate_result: the events belong to another study than the analysis.",
            events.span,
        )
    return ClaimIR(
        "result",
        RateResultIR(analysis.value, events.value),
        events.name or analysis.name or "<expression>",
    )


def _rate_ratio(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    events, level = arguments["events"], arguments["level"]
    if not 0 < level.value < 1:
        fail("domain", "level must lie strictly between 0 and 1.", level.span)
    interval = RateRatioIR(events.value, level.value)
    try:
        interval.lower()
    except ValueError as error:
        fail("domain", str(error), events.span)
    return ClaimIR("interval", interval, events.name or "<expression>")


def _proportion(measure: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        model, cases, level = arguments["model"], arguments["cases"], arguments["level"]
        _simple_binary(model, measure, exposure=False)
        group = arguments.get("group")
        group = group.value if group is not None else None
        reason = proportion_not_estimable(measure, model.value.design)
        if reason:
            fail("not_estimable", f"{measure}: {reason}", model.span)
        if model.value.groups is not None and group is None:
            fail(
                "domain",
                "This cohort sampled exposed and unexposed groups separately, so say which: "
                'group="exposed" or group="unexposed".',
                span,
            )
        if model.value.groups is None and group is not None:
            fail(
                "domain",
                "This study did not fix exposed and unexposed groups; leave group out.",
                arguments["group"].span,
            )
        if not 0 < level.value < 1:
            fail("domain", "level must lie strictly between 0 and 1.", level.span)
        estimate = ProportionIR(measure, model.value, cases.value, level.value, group)
        if not 0 <= cases.value <= estimate.size:
            fail("domain", f"cases must be between 0 and {estimate.size}.", cases.span)
        try:
            estimate.lower()
        except ValueError as error:
            fail("domain", str(error), span)
        return ClaimIR("interval", estimate, model.name or "<expression>")

    return build


def _words(items) -> str:
    items = [item.replace("_", "-") for item in items]
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " or " + items[-1]


def _fitting_methods(model: "ObservationalStudyIR") -> str:
    """The cited methods whose design, scales and survey fit a study, as a hint."""
    keys = [
        m.key
        for m in OBSERVATIONAL_METHODS.values()
        if model.design in m.designs
        and model.outcome_scale in m.outcome_scales
        and model.exposure_scale in m.exposure_scales
        and model.survey in m.surveys
    ]
    return f" Methods that fit this study: {', '.join(keys)}." if keys else ""


def _cited_association(method: ObservationalMethod) -> Callable:
    """The contract of a cited observational method: design, scales, survey, size, covariates."""

    def build(arguments: dict[str, LocatedValue], span: Span) -> CitedAssociationIR:
        design, null, alpha = arguments["design"], arguments["null"], arguments["alpha"]
        model = design.value.model
        key = method.key
        if not isinstance(model, ObservationalStudyIR):
            fail(
                "type",
                f"{key} is for observational studies; this design is a randomised trial.",
                design.span,
            )
        if model != null.value.model:
            fail(
                "model_mismatch",
                f"{key}: the null belongs to a different study. Declare "
                "no_association(model=...) over the study the design samples.",
                null.span,
            )
        if model.design not in method.designs:
            kinds = _words(method.designs)
            code = (
                "not_estimable"
                if key == "modified_poisson" and model.design.endswith("case_control")
                else "type"
            )
            fail(
                code,
                f"{key} fits {kinds} studies; this is a {model.design.replace('_', '-')} study."
                + (
                    " A case-control study cannot estimate a risk or prevalence ratio."
                    if code == "not_estimable"
                    else ""
                )
                + _fitting_methods(model),
                design.span,
            )
        for which, scale, allowed in (
            ("outcome", model.outcome_scale, method.outcome_scales),
            ("exposure", model.exposure_scale, method.exposure_scales),
        ):
            if scale not in allowed:
                fail(
                    "type",
                    f"{key} needs a {' or '.join(allowed)} {which}; this study declares a "
                    f"{scale} {which}." + _fitting_methods(model),
                    design.span,
                )
        if model.survey not in method.surveys:
            fail(
                "complex_sample",
                f"{key} assumes participants were sampled independently with equal "
                f"probability; this survey declares {model.survey} sampling."
                + _fitting_methods(model),
                design.span,
            )
        total = (
            model.pairs
            if isinstance(model, MatchedStudyIR)
            else (model.total if not isinstance(model, PersonTimeStudyIR) else None)
        )
        if total is not None and total < method.min_total:
            fail(
                "domain",
                f"{key} needs at least {method.min_total} participants; this study has {total}.",
                design.span,
            )
        clustered = model.survey == "cluster"
        if method.min_clusters and clustered and model.clusters < method.min_clusters:
            fail(
                "domain",
                f"{key} needs at least {method.min_clusters} sampled clusters for its "
                f"design-based variance; this survey sampled {model.clusters}.",
                design.span,
            )
        if not 0 < alpha.value < 1:
            fail("domain", "alpha must lie strictly between 0 and 1 for this test.", alpha.span)
        covariates: list[str] = []
        listed = arguments.get("adjusted_for")
        if listed is not None and listed.value is not None:
            for item in listed.value:
                if not isinstance(item.value, str) or not NAME.fullmatch(item.value):
                    fail("domain", "Each covariate is a name in a few plain words.", item.span)
                if item.value in covariates or item.value in (model.exposure, model.outcome):
                    fail(
                        "domain",
                        "Each covariate is named once, and is neither the exposure nor the "
                        "outcome.",
                        item.span,
                    )
                covariates.append(item.value)
            if len(covariates) > MAX_COVARIATES:
                fail("domain", f"At most {MAX_COVARIATES} covariates.", listed.span)
        return CitedAssociationIR(design.value, null.value, alpha.value, method, tuple(covariates))

    return build


def _cited_association_constructor(method: ObservationalMethod) -> Constructor:
    parameters = [("design", PlanIR), ("null", AssociationNullIR), ("alpha", "level")]
    if method.covariates:
        parameters.append(("adjusted_for", "list", True))
    designs = _words(method.designs)
    return _constructor(
        method.key,
        tuple(parameters),
        "CitedAssociation",
        _cited_association(method),
        documentation=f"{method.title}. Fits {designs} studies with a "
        f"{' or '.join(method.outcome_scales)} outcome. Its guarantee is cited from the "
        "literature and not checked by Lean."
        + (" adjusted_for lists the covariates, by name." if method.covariates else ""),
    )


def _observed_table(arguments: dict[str, LocatedValue], span: Span) -> AssociationTableIR:
    _simple_binary(arguments["model"], "observed_table")
    _rates_refused(
        arguments["model"],
        "A person-time cohort records events and person-time, not a table of participants. "
        "Use observed_events.",
    )
    _matched_refused(
        arguments["model"],
        "observed_table records two unmatched groups, which loses the pairs. Use "
        "observed_pairs for a matched study.",
    )
    model = arguments["model"].value
    cells = []
    for key in CELLS:
        argument = arguments[key]
        if argument.value < 0:
            fail("domain", f"{key} must be a whole number, zero or more.", argument.span)
        cells.append(argument.value)
    problem = table_problem(
        model.design, model.groups, None if model.groups is not None else model.n, cells
    )
    if problem:
        fail("domain", problem, span)
    return AssociationTableIR(model, *cells)


def _association_result(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    analysis, table = arguments["analysis"], arguments["table"]
    if analysis.value.plan.model != table.value.model:
        fail(
            "model_mismatch",
            "association_result: the table belongs to another study than the analysis. "
            "Declare observed_table(model=...) over the study the analysis tests.",
            table.span,
        )
    return ClaimIR(
        "result",
        AssociationResultIR(analysis.value, table.value),
        table.name or analysis.name or "<expression>",
    )


def _effect_interval(measure: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
        table, level = arguments["table"], arguments["level"]
        reason = not_estimable(measure, table.value.model.design)
        if reason:
            fail("not_estimable", f"{measure}: {reason}", table.span)
        if not 0 < level.value < 1:
            fail("domain", "level must lie strictly between 0 and 1.", level.span)
        interval = EffectIntervalIR(measure, table.value, level.value)
        try:
            interval.lower()
        except ValueError as error:
            fail("domain", str(error), level.span)
        return ClaimIR("interval", interval, table.name or "<expression>")

    return build


def _fisher(alternative: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> AnalysisIR:
        plan, hypothesis = arguments["design"].value, arguments["null"].value
        test = "fisher" if alternative == "two_sided" else "fisher_one_sided"
        _observational_refused(arguments["design"], test)
        check_design(plan.model, BINOMIAL_ASSUMPTIONS, test, arguments["design"].span)
        return AnalysisIR(plan, hypothesis, arguments["alpha"].value, alternative)

    return build


def _difference(predicate: str) -> Callable:
    def build(arguments: dict[str, LocatedValue], span: Span) -> HypothesisIR:
        bound = arguments["value"]
        if not -1 <= bound.value <= 1:
            fail("domain", "A proportion-difference value must lie in [-1, 1].", bound.span)
        _check_direction(NULL_FORMS[predicate][1], arguments["model"].value, span)
        # This alias is backed by proportionDifference_zero_iff in the Lean model.
        canonical = (
            "equal_proportions"
            if predicate == "proportion_difference" and bound.value == 0
            else predicate
        )
        return HypothesisIR(arguments["model"].value, canonical, bound.value)

    return build


def _difference_test(arguments: dict[str, LocatedValue], span: Span) -> AnalysisIR:
    plan, null, alpha = arguments["design"].value, arguments["null"], arguments["alpha"]
    _observational_refused(arguments["design"], "difference_test")
    if not -1 < null.value.value < 1:
        fail("domain", "The margin must lie strictly between -1 and 1.", null.span)
    if alpha.value == 0:
        fail("domain", "alpha must be positive for this test.", alpha.span)
    check_design(plan.model, BINOMIAL_ASSUMPTIONS, "difference_test", arguments["design"].span)
    if max(plan.model.n_control, plan.model.n_treatment) > MAX_MARGIN_ARM:
        fail(
            "domain",
            f"The exact difference test currently supports up to {MAX_MARGIN_ARM} per arm; "
            "larger designs take too long to verify.",
            arguments["design"].span,
        )
    return AnalysisIR(plan, null.value, alpha.value, "margin")


def _members(
    argument: LocatedValue, what: str, *, combinations: bool = True, randomisation: bool = True
) -> list[tuple[str, object]]:
    """Named, distinct analyses for a family, a sequence, a graph or a design's looks.

    With combinations=True an entry may also be a whole design with looks, a
    family, a sequence or a graph. With randomisation=True an entry may be a
    randomisation test.
    """
    items = argument.value
    allowed = (
        (AnalysisIR, CitedAnalysisIR, ComposedFamilyIR, FamilyIR)
        if combinations
        else (AnalysisIR, CitedAnalysisIR)
    ) + ((RandomisationAnalysisIR,) if randomisation else ())
    if not 2 <= len(items) <= MAX_ENDPOINTS:
        fail("family_size", f"This needs between 2 and {MAX_ENDPOINTS} {what}.", argument.span)
    members = []
    for item in items:
        if not isinstance(item.value, allowed) or item.name is None:
            fail(
                "type",
                "Each entry must be a named analysis: an exact two-arm test"
                + (", a randomisation test" if randomisation else "")
                + (
                    ", a cited test, or a named design, family, sequence or graph."
                    if combinations
                    else " or a cited test."
                )
                + (
                    ""
                    if randomisation
                    else " A randomisation test counts splits of one fixed set of units, so it "
                    "cannot be a look of a sequential design."
                ),
                item.span,
            )
        value = item.value
        if isinstance(value, FamilyIR):
            # As a member, a proved Fisher family is one more combination of assumed parts.
            value = ComposedFamilyIR(value.analyses, value.alpha)
        members.append((item.name, value))
    if len({name for name, _ in members}) != len(members):
        fail("duplicate_analysis", "The entries must have distinct names.", argument.span)
    # A name labels one outcome or one look. Two names for one declaration would
    # count it twice while reporting two.
    if len({id(item.value) for item in items}) != len(members):
        fail(
            "duplicate_analysis",
            "Two entries are the same declaration under different names. "
            "Declare each analysis separately; its name is its label.",
            argument.span,
        )
    _check_named_outcomes(members, argument.span)
    return members


def _family(arguments: dict[str, LocatedValue], span: Span) -> FamilyLikeIR:
    analyses = _members(arguments["analyses"], "analyses")
    law = arguments["joint_law"]
    proved = all(
        isinstance(analysis, AnalysisIR) and analysis.alternative == "two_sided"
        for _, analysis in analyses
    )
    if not proved:
        # The union bound needs no joint law, so there is nothing to declare.
        if law.value is not None:
            fail(
                "sampling_contract",
                "Leave joint_law out unless every member is a two-sided Fisher analysis. "
                "The combination holds for any dependence between members.",
                law.span,
            )
        return ComposedFamilyIR(tuple(analyses), arguments["alpha"].value)
    if law.value not in (None, "binomial_marginals"):
        fail(
            "sampling_contract",
            'The supported joint contract is "binomial_marginals"; '
            "dependence between outcomes is unrestricted.",
            law.span,
        )
    return FamilyIR(tuple(analyses), arguments["alpha"].value, "binomial_marginals")


def _test_key(analysis: LevelTestIR) -> str:
    if isinstance(analysis, CitedAnalysisIR):
        return analysis.method.key
    return EXACT_CONTRACT_IDS[analysis.alternative].split("/")[1]


def _ordered_looks(arguments: dict[str, LocatedValue]) -> list[tuple[str, object]]:
    """The looks of a design: one test of one null, at growing cumulative sizes."""
    looks = _members(arguments["looks"], "looks", combinations=False, randomisation=False)
    first = looks[0][1]
    previous = None
    for name, look in looks:
        null, model = look.hypothesis, look.plan.model
        same = (
            _test_key(look) == _test_key(first)
            and type(model) is type(first.plan.model)
            and getattr(model, "outcome", None) == getattr(first.plan.model, "outcome", None)
            and (null.predicate, null.value) == (first.hypothesis.predicate, first.hypothesis.value)
        )
        if not same:
            fail(
                "sequential_question",
                f"{name}: every look must use the same test and the same null as the first "
                "look. Different questions belong in a bonferroni family.",
                arguments["looks"].span,
            )
        sizes = (model.n_control, model.n_treatment)
        if previous is not None and not (
            sizes[0] >= previous[0] and sizes[1] >= previous[1] and sum(sizes) > sum(previous)
        ):
            fail(
                "sequential_order",
                f"{name}: list the looks in order. Each look's model gives the cumulative "
                "arm sizes at that look, so they must grow.",
                arguments["looks"].span,
            )
        previous = sizes
    return looks


def _sequential(arguments: dict[str, LocatedValue], span: Span) -> SequentialIR:
    return SequentialIR(tuple(_ordered_looks(arguments)), arguments["alpha"].value)


def boundary_sides(look: object) -> int | None:
    """How many sides a look's boundary has, for the tests whose information at a look is
    read from its arm sizes: Fisher's test and the t-tests. None for any other test."""
    if isinstance(look, AnalysisIR) and look.alternative in ("two_sided", "greater"):
        return 2 if look.alternative == "two_sided" else 1
    if isinstance(look, CitedAnalysisIR) and look.method.module == "tests.t":
        return 1 if NULL_FORMS[look.hypothesis.predicate][1].favours else 2
    return None


def _group_sequential(arguments: dict[str, LocatedValue], span: Span) -> SequentialIR:
    looks = _ordered_looks(arguments)
    spending, alpha = arguments["spending"], arguments["alpha"].value
    if spending.value not in SPENDING:
        fail(
            "domain",
            'spending must be "obrien_fleming" or "pocock".',
            spending.span,
        )
    sides = boundary_sides(looks[-1][1])
    if sides is None:
        fail(
            "unsupported_claim",
            "Spending boundaries read the information at each look from its arm sizes, which "
            "holds for Fisher's test and the t-tests. Split the level with alpha_spending "
            "for other tests.",
            arguments["looks"].span,
        )
    sizes = [(look.plan.model.n_control, look.plan.model.n_treatment) for _, look in looks]
    limits = boundary_limits(sizes, alpha, sides, spending.value)
    over = [name for (name, look), limit in zip(looks, limits, strict=True) if look.alpha > limit]
    if over:
        suggested = ", ".join(
            f"{name} alpha={floor_level(float(limit), 6)}"
            for (name, _), limit in zip(looks, limits, strict=True)
        )
        fail(
            "sequential_boundary",
            f"{', '.join(over)}: the level exceeds the {spending.value} boundary at that look. "
            f"Each look may use at most the nominal level the spending function gives it at "
            f"its share of the information, for an overall level of {alpha}: {suggested}.",
            arguments["looks"].span,
        )
    return SequentialIR(
        tuple(looks), alpha, mode="spending", spending=spending.value, limits=limits
    )


def _fixed_sequence(arguments: dict[str, LocatedValue], span: Span) -> ComposedFamilyIR:
    analyses = _members(arguments["analyses"], "analyses")
    alpha = arguments["alpha"]
    for name, analysis in analyses:
        if analysis.alpha != alpha.value:
            fail(
                "sequence_level",
                f"{name} has alpha {analysis.alpha}, but every test in a fixed sequence uses "
                f"the full level {alpha.value}. The order, not a split of the level, controls "
                "the error. To split the level, use bonferroni.",
                arguments["analyses"].span,
            )
    return ComposedFamilyIR(tuple(analyses), alpha.value, "fixed_sequence")


def _share(item: LocatedValue, what: str) -> Fraction:
    value = Fraction(item.value) if type(item.value) is int else item.value
    if not isinstance(value, Fraction) or not 0 <= value <= 1:
        fail("graph_definition", f"Each {what} must be an exact number from 0 to 1.", item.span)
    return value


def _graphical(arguments: dict[str, LocatedValue], span: Span) -> ComposedFamilyIR:
    analyses = _members(arguments["analyses"], "analyses", combinations=False)
    alpha, count = arguments["alpha"], len(analyses)
    for name, analysis in analyses:
        if analysis.alpha != alpha.value:
            fail(
                "sequence_level",
                f"{name} has alpha {analysis.alpha}. In a graph, declare every test at the "
                f"overall level {alpha.value}; the weights say what share each starts with.",
                arguments["analyses"].span,
            )
    weights = arguments["weights"]
    if not isinstance(weights.value, tuple) or len(weights.value) != count:
        fail(
            "graph_definition",
            f"weights needs one number for each of the {count} tests.",
            weights.span,
        )
    shares = tuple(_share(item, "weight") for item in weights.value)
    if sum(shares) > 1:
        fail("graph_definition", f"The weights sum to {sum(shares)}, more than 1.", weights.span)
    table = arguments["transitions"]
    rows = table.value
    if len(rows) != count or any(
        not isinstance(row.value, tuple) or len(row.value) != count for row in rows
    ):
        fail(
            "graph_definition",
            f"transitions needs {count} rows of {count} numbers: row i says how test i's "
            "level is shared out when it is rejected.",
            table.span,
        )
    passed = tuple(tuple(_share(item, "transition") for item in row.value) for row in rows)
    for index, row in enumerate(passed):
        if row[index] != 0:
            fail("graph_definition", "A test cannot pass its level to itself.", rows[index].span)
        if sum(row) > 1:
            fail(
                "graph_definition",
                f"Row {index + 1} of transitions sums to {sum(row)}, more than 1.",
                rows[index].span,
            )
    return ComposedFamilyIR(tuple(analyses), alpha.value, "graphical", shares, passed)


def _familywise(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    family = arguments["family"]
    if isinstance(family.value, SequentialIR):
        fail(
            "type",
            "A sequential design tests one null, so ask for typeI(...) instead of familywise.",
            family.span,
        )
    return ClaimIR("familywise", family.value, family.name or "<expression>")


def _observe(arguments: dict[str, LocatedValue], span: Span) -> ObservationIR:
    analysis = arguments["analysis"].value
    for name, size in (
        ("control_successes", analysis.plan.model.n_control),
        ("treatment_successes", analysis.plan.model.n_treatment),
    ):
        argument = arguments[name]
        if not 0 <= argument.value <= size:
            fail("domain", f"{name} must be between 0 and {size} for this analysis.", argument.span)
    return ObservationIR(
        analysis, arguments["control_successes"].value, arguments["treatment_successes"].value
    )


def _claim(kind: str, argument: str) -> Callable:
    return lambda args, span: ClaimIR(
        kind, args[argument].value, args[argument].name or "<expression>"
    )
