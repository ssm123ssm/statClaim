"""The operations verify, calculate and simulate, and their checks."""

from fractions import Fraction
from typing import cast

from statclaim.language.checks import (
    ICC_REFUSED,
    POINT_SIGNATURES,
    clustered_test,
    exact_looks,
)
from statclaim.language.core import (
    LocatedValue,
    fail,
)
from statclaim.language.ir import (
    AnalysisIR,
    CandidatesIR,
    ClaimIR,
    ClusterCandidatesIR,
    LookCandidatesIR,
    SimulationIR,
    SizingIR,
    TotalCandidatesIR,
    planned_analysis,
)
from statclaim.language.points import (
    departs,
    participant_draws,
    skewed,
)
from statclaim.language_syntax import (
    Span,
)
from statclaim.look_search import allocation as look_allocation
from statclaim.methods import methods_for
from statclaim.plan_kinds import kind_of, resolve
from statclaim.simulation import (
    DEFAULT_RUNS,
    MAX_RUNS,
    MAX_SIMULATED_PARTICIPANTS,
    MAX_SIMULATED_STUDIES,
    MIN_RUNS,
)

MAX_SIMULATED_CLUSTER = 1000  # participants per cluster when simulating cluster proportions


def _calculation(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    claim = arguments["claim"]
    if claim.value.kind not in ("result", "meets", "sample_size", "interval"):
        fail(
            "type",
            "Only results, intervals and planning claims are numerical calculations. "
            "Use verify(claim) for design guarantees.",
            claim.span,
        )
    target = getattr(claim.value.subject, "target", None)
    point = getattr(target, "at", None)
    if claim.value.kind in ("meets", "sample_size"):
        # What the analysis's kind allows: see plan_kinds.KINDS.
        kind = kind_of(planned_analysis(claim.value.subject))
        if kind.calculate is None:
            fail("unsupported_claim", kind.refuse_calculate, claim.span)
        if kind.check_calculate is not None:
            resolve(kind.check_calculate)(claim)
    if getattr(point, "cluster_size_cv", None):
        fail(
            "unsupported_claim",
            "The noncentral t assumes clusters of equal size. For clusters whose sizes vary, "
            "use simulate(...), which draws the sizes.",
            claim.span,
        )
    if getattr(point, "effect_delay", None):
        fail(
            "unsupported_claim",
            "Schoenfeld's formula assumes the hazard ratio holds from entry on. For an effect "
            "that starts later, use simulate(...), which draws the survival times.",
            claim.span,
        )
    if departs(point):
        fail(
            "unsupported_claim",
            "The formula assumes normal data, with a common SD for two means. For unequal SDs "
            "or skewed data, use simulate(...), which runs the test on that scenario.",
            claim.span,
        )
    return claim.value


def _verification(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    claim = arguments["claim"]
    if claim.value.kind in ("meets", "sample_size"):
        kind = kind_of(planned_analysis(claim.value.subject))
        if kind.refuse_verify is not None:
            fail("unsupported_claim", kind.refuse_verify, claim.span)
    return claim.value


def simulation_settings(arguments: dict[str, LocatedValue]) -> SimulationIR:
    """The seed and number of runs of simulate(...), with the number of runs checked."""
    seed, runs = arguments["seed"], arguments["runs"]
    if seed.value < 0:
        fail("domain", "seed must be a whole number of at least 0.", seed.span)
    count = DEFAULT_RUNS if runs.value is None else runs.value
    if not MIN_RUNS <= count <= MAX_RUNS:
        fail(
            "domain",
            f"runs must be from {MIN_RUNS:,} to {MAX_RUNS:,}; the default is {DEFAULT_RUNS:,}.",
            runs.span,
        )
    return SimulationIR(seed.value, count)


def _simulation(arguments: dict[str, LocatedValue], span: Span) -> ClaimIR:
    """Power by simulation, for planning claims about tests that have a simulation model."""
    claim = arguments["claim"]
    if claim.value.kind not in ("meets", "sample_size"):
        fail(
            "type",
            "Only planning claims are simulated: meets(...) and sample-size searches. "
            "Use verify(claim) for guarantees and calculate(claim) for results.",
            claim.span,
        )
    subject = claim.value.subject
    analysis = planned_analysis(subject)
    kind = kind_of(analysis)
    if kind.check_simulate is None:
        fail("unsupported_claim", kind.refuse_simulate, claim.span)
    return resolve(kind.check_simulate)(analysis, subject, arguments, claim)


def check_cited_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A cited two-arm test is simulated by its method's model, at the model's point."""
    method = analysis.method
    if method.simulation is None:
        others = ", ".join(m.key for m in methods_for(method.outcome) if m.simulation) or "none"
        fail(
            "no_simulation_model",
            f"{method.key} has no simulation model yet. Tests for this outcome with one: "
            f"{others}." + (" calculate(...) gives its approximate power." if method.power else ""),
            claim.span,
        )
    kind, signature = POINT_SIGNATURES[method.simulation.point]
    if not isinstance(subject.target.at, kind):
        fail("planning_point", f"Simulate {method.key} at {signature}.", claim.span)
    if not clustered_test(analysis) and getattr(subject.target.at, "icc", None) is not None:
        fail("planning_point", ICC_REFUSED, claim.span)
    settings = simulation_settings(arguments)
    if clustered_test(analysis) and method.outcome == "binary":
        if isinstance(subject, SizingIR):
            # A test of cluster summaries is searched only by cluster_counts or cluster_sizes.
            assert isinstance(subject.candidates, ClusterCandidatesIR)
            largest = max(size for _, sizes in subject.candidates.designs() for size in sizes)
        else:
            model = analysis.plan.model
            largest = max(
                Fraction(model.n_control, model.assignment.clusters_control),
                Fraction(model.n_treatment, model.assignment.clusters_treatment),
            )
        if largest > MAX_SIMULATED_CLUSTER:
            fail(
                "domain",
                f"Simulating cluster proportions draws every participant, so clusters are "
                f"limited to {MAX_SIMULATED_CLUSTER:,} participants here.",
                claim.span,
            )
    if isinstance(subject, SizingIR):
        space = subject.candidates
        if isinstance(space, ClusterCandidatesIR):
            candidates = space.high - space.low + 1
        else:
            # A cited two-arm test's other searches are over sizes per arm.
            assert isinstance(space, CandidatesIR)
            candidates = space.max_per_arm - space.min_per_arm + 1
        if candidates * settings.runs > MAX_SIMULATED_STUDIES:
            fail(
                "domain",
                f"Searching {candidates:,} sizes with {settings.runs:,} runs each could "
                f"simulate more than {MAX_SIMULATED_STUDIES:,} studies. Narrow the range or "
                "use fewer runs.",
                claim.span,
            )
    if participant_draws(subject.target.at):
        # A search simulates each size for power, then confirms the one that passes with
        # power and Type I runs; a claim at the declared sizes runs power and Type I.
        if isinstance(subject, SizingIR):
            # Only a test of participants is simulated at points that draw every participant.
            arms = cast(CandidatesIR, subject.candidates)
            sizes = [s + arms.ratio * s for s in range(arms.min_per_arm, arms.max_per_arm + 1)]
            drawn = sum(sizes) + 2 * sizes[-1]
        else:
            drawn = 2 * (analysis.plan.model.n_control + analysis.plan.model.n_treatment)
        if drawn * settings.runs > MAX_SIMULATED_PARTICIPANTS:
            fail(
                "domain",
                "This scenario is simulated one participant at a time, and this could draw "
                f"more than {MAX_SIMULATED_PARTICIPANTS:,} participants. Narrow the range or "
                "use fewer runs.",
                claim.span,
            )
    return claim.value


def check_family_simulation(family, subject, arguments, claim) -> ClaimIR:
    """A family is simulated as declared; correlated endpoints draw every participant."""
    if isinstance(subject, SizingIR):
        fail(
            "unsupported_claim",
            "A family is simulated as declared; searching its sizes is not supported yet.",
            claim.span,
        )
    settings = simulation_settings(arguments)
    point = subject.target.at
    if point.correlation > 0:
        model = family.analyses[0][1].plan.model
        drawn = 2 * (model.n_control + model.n_treatment) * len(point.points)
        if drawn * settings.runs > MAX_SIMULATED_PARTICIPANTS:
            fail(
                "domain",
                "Correlated endpoints are simulated one participant at a time, and this could "
                f"draw more than {MAX_SIMULATED_PARTICIPANTS:,} outcomes. Use fewer runs.",
                claim.span,
            )
    return claim.value


def check_looks_calculation(claim: LocatedValue) -> None:
    """Fisher's test at looks is calculated as declared; t-test looks are simulated."""
    analysis = planned_analysis(claim.value.subject)
    if not exact_looks(analysis):
        fail(
            "unsupported_claim",
            "A design with t-test looks has no power formula. Use simulate(...), which runs "
            "the trial look by look.",
            claim.span,
        )
    subject = claim.value.subject
    if claim.value.kind == "sample_size" and not isinstance(subject.candidates, LookCandidatesIR):
        fail(
            "unsupported_claim",
            "Search a design with looks with look_sizes(design=...), which lets each look's "
            "size vary.",
            claim.span,
        )


def check_reestimation_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A re-estimated design chooses its own size, so it is simulated as declared."""
    if isinstance(subject, SizingIR):
        fail(
            "unsupported_claim",
            "A re-estimated design chooses its own size; simulate meets(...) for it.",
            claim.span,
        )
    simulation_settings(arguments)
    return claim.value


def is_margin_test(analysis: object) -> bool:
    """An exact two-arm test with a margin: the difference test."""
    return isinstance(analysis, AnalysisIR) and analysis.alternative == "margin"


def check_looks_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A design with looks is simulated as declared, look by look."""
    if exact_looks(analysis):
        fail(
            "unsupported_claim",
            "Fisher's test at looks has exact power, so there is nothing to simulate: "
            "calculate(...) sums it over every path of counts.",
            claim.span,
        )
    if isinstance(subject, SizingIR) and not isinstance(subject.candidates, LookCandidatesIR):
        fail(
            "unsupported_claim",
            "Search a design with looks with look_sizes(design=...), which lets each look's "
            "size vary.",
            claim.span,
        )
    settings = simulation_settings(arguments)
    if participant_draws(subject.target.at):
        model = analysis.final.plan.model
        largest = (model.n_control, model.n_treatment)
        if isinstance(subject, SizingIR):
            space = subject.candidates
            # Refused above unless the search is look_sizes(...).
            assert isinstance(space, LookCandidatesIR)
            largest = (space.max_per_arm, space.max_per_arm * (look_allocation(analysis) or 1))
        if 2 * sum(largest) * settings.runs > MAX_SIMULATED_PARTICIPANTS:
            fail(
                "domain",
                "This scenario is simulated one participant at a time, and this could draw more "
                f"than {MAX_SIMULATED_PARTICIPANTS:,} participants. Use fewer runs.",
                claim.span,
            )
    return claim.value


def check_association_simulation(analysis, subject, arguments, claim) -> ClaimIR:
    """A cited test of an observational study is simulated in a scenario its formula cannot
    describe: skewed data, for the tests of a correlation or a slope."""
    method = analysis.method
    if method.simulation is None:
        fail(
            "no_simulation_model",
            f"{method.key} has no simulation model yet. calculate(...) gives its power.",
            claim.span,
        )
    kind, signature = POINT_SIGNATURES[method.simulation.point]
    if not isinstance(subject.target.at, kind):
        fail("planning_point", f"Simulate {method.key} at {signature}.", claim.span)
    if not skewed(subject.target.at):
        fail(
            "unsupported_claim",
            "With normal data this test's power is exact, so there is nothing to simulate: "
            "calculate(...) gives it. Give skewness or exposure_skewness to simulate skewed data.",
            claim.span,
        )
    settings = simulation_settings(arguments)
    if isinstance(subject, SizingIR):
        space = subject.candidates
        if not isinstance(space, TotalCandidatesIR):
            fail(
                "unsupported_claim", "Simulation searches totals: use total_sizes(...).", claim.span
            )
        totals = list(range(space.min_n, space.max_n + 1))
        if len(totals) * settings.runs > MAX_SIMULATED_STUDIES:
            fail(
                "domain",
                f"Searching {len(totals):,} sizes with {settings.runs:,} runs each could "
                f"simulate more than {MAX_SIMULATED_STUDIES:,} studies. Narrow the range or "
                "use fewer runs.",
                claim.span,
            )
        drawn = sum(totals) + 2 * totals[-1]
    else:
        drawn = 2 * analysis.plan.model.total
    if drawn * settings.runs > MAX_SIMULATED_PARTICIPANTS:
        fail(
            "domain",
            "This scenario is simulated one participant at a time, and this could draw more "
            f"than {MAX_SIMULATED_PARTICIPANTS:,} participants. Narrow the range or use fewer "
            "runs.",
            claim.span,
        )
    return claim.value
