"""Power by simulation for cited tests: estimates with Monte Carlo error, never evidence.

The simulation model comes from the method's registry entry (methods/simulation.py) and
the draws from simulation.py. This module reads the declaration, runs the model and says
what the estimate rests on.

Every test is simulated through one shape, a Design: how one of its studies is drawn, at
the planning point or at the null, and how its sizes are reported. A two-arm test's
sizes are its arms; a test of cluster summaries has clusters per arm, and each arm's mean
cluster size and the variation of sizes go to the model; a test of an observational
study has a total and covariates.

A size passes when the whole 95% interval for its power is at or above the target. A
sample-size search goes up from the smallest size and simulates every size it passes, so
nothing assumes that power rises with the sample size. The first size that passes is
simulated again from an independent stream, and the reported power comes from that run,
so picking the size does not bias the estimate.

Simulated Type I is reported, not judged, while the test's level holds by theory. In a
scenario that leaves the theory (unequal SDs or skewed data on the planning point), Type I
is judged like power: met when its whole 95% interval is at or below maximum_typeI, and a
search passes over sizes where it is not met.
"""

import math
from collections.abc import Callable
from dataclasses import dataclass
from fractions import Fraction

from statclaim import association_planning
from statclaim import simulation as engine
from statclaim.cited_planning import (
    PLANNING_POINT,
    _cluster_record,
    _values,
    declared_clusters,
    describe_point,
)
from statclaim.fisher import fraction_record
from statclaim.language import (
    CitedAssociationIR,
    ClusterCandidatesIR,
    FeasibilityIR,
    PowerTargetIR,
    SimulationIR,
    clustered_test,
    departs,
    planned_analysis,
)
from statclaim.methods import NULL_FORMS
from statclaim.methods.identify import identify, mark
from statclaim.report import planning_report

ESTIMATE = "Monte Carlo estimate with a 95% interval, not a bound"
INTERVAL = f"{engine.INTERVAL}, {engine.CONFIDENCE:.0%}"
# A planning point's scenario, which the model reads beside the point itself.
SCENARIO = ("sd_treatment", "skewness", "exposure_skewness", "cluster_size_cv", "effect_delay")


@dataclass(frozen=True)
class Design:
    """One design to simulate: how one of its studies is drawn, and what is said of it.

    `trial(at_null)` gives one simulated study, at the planning point or at the null's
    boundary. `labels` tell this design's random streams from every other design's.
    `record` gives its sizes as a calculation reports them, `curve` as a search lists them.
    """

    labels: tuple
    trial: Callable[[bool], Callable[[engine.Stream], bool]]
    record: dict
    curve: dict
    scenario: str


def _observational(analysis) -> bool:
    return isinstance(analysis, CitedAssociationIR)


def _point_values(analysis, point, cluster_sizes=None) -> dict[str, float]:
    """The planning point as the model reads it, with any scenario and cluster sizes."""
    if _observational(analysis):
        values, _ = association_planning.inputs(analysis, point, 0)
    else:
        values = _values(point)
    for name in SCENARIO:
        if getattr(point, name, None) is not None:
            values[name] = float(getattr(point, name))
    if cluster_sizes is not None:
        values["size_control"], values["size_treatment"] = (float(m) for m in cluster_sizes)
    return values


def _at_null(analysis, values: dict) -> dict:
    """The same scenario at the null's boundary, where Type I error is simulated."""
    if _observational(analysis):
        return {**values, "value": 0.0}  # no association
    values = {**values, "value": float(analysis.hypothesis.value)}
    if "p_treatment" in values:
        values["p_treatment"] = values["p_control"]
    if "control_median" in values:
        values["value"] = 1.0  # equal survival: a hazard ratio of 1
    return values


def _two_arm(analysis, target: PowerTargetIR, sizes, cluster_sizes=None) -> Design:
    """A two-arm design: arm sizes, or for a cluster test clusters and their mean sizes."""
    model, point = analysis.method.simulation, target.at
    values = _point_values(analysis, point, cluster_sizes)
    null_value = float(analysis.hypothesis.value)
    side = NULL_FORMS[analysis.hypothesis.predicate][1].favours or "both"

    def trial(at_null: bool):
        drawn = _at_null(analysis, values) if at_null else values
        return model.trial(drawn, *sizes, null_value, float(analysis.alpha), side)

    if cluster_sizes is None:
        n_control, n_treatment = sizes
        record = {
            "n_control": n_control,
            "n_treatment": n_treatment,
            "total_sample_size": n_control + n_treatment,
        }
        curve = {"n_control": n_control, "n_treatment": n_treatment}
        labels = tuple(sizes)
    else:
        record = _cluster_record(target, sizes, cluster_sizes)
        if getattr(point, "cluster_size_cv", None):
            # 1 + (m - 1) icc holds for clusters of equal size only.
            record.pop("design_effect", None)
        if getattr(point, "cluster_size_cv", None) is not None:
            record["cluster_size_cv"] = fraction_record(point.cluster_size_cv)
        curve = {
            "n_control": sizes[0] * cluster_sizes[0],
            "n_treatment": sizes[1] * cluster_sizes[1],
            "clusters_control": sizes[0],
            "cluster_size": cluster_sizes[0],
        }
        labels = (*sizes, *(str(m) for m in cluster_sizes))
    return Design(labels, trial, record, curve, model.scenario(values))


def _total(analysis, target: PowerTargetIR, n: int) -> Design:
    """An observational design: a total of participants, analysed with its covariates."""
    model, covariates = analysis.method.simulation, len(analysis.covariates)
    values = _point_values(analysis, target.at)

    def trial(at_null: bool):
        drawn = _at_null(analysis, values) if at_null else values
        return model.trial(drawn, n, covariates, float(analysis.alpha))

    record = {
        "total_sample_size": n,
        "covariates": covariates,
        "degrees_of_freedom": n - covariates - 2,
    }
    return Design((n,), trial, record, {"total_sample_size": n}, model.scenario(values))


def _declared(analysis, target: PowerTargetIR) -> Design:
    """The study as declared."""
    if _observational(analysis):
        return _total(analysis, target, analysis.plan.model.total)
    if clustered_test(analysis):
        return _two_arm(analysis, target, *declared_clusters(analysis))
    model = analysis.plan.model
    return _two_arm(analysis, target, (model.n_control, model.n_treatment))


def _searched(analysis, target: PowerTargetIR, space) -> tuple[list[Design], dict]:
    """A search's designs, in order, and its bounds as the report states them."""
    if _observational(analysis):
        designs = [_total(analysis, target, n) for n in range(space.min_n, space.max_n + 1)]
        return designs, {"min_n": space.min_n, "max_n": space.max_n}
    if isinstance(space, ClusterCandidatesIR):
        designs = [_two_arm(analysis, target, *design) for design in space.designs()]
        if space.varies == "clusters":
            return designs, {
                "cluster_size": space.cluster_size,
                "min_clusters_per_arm": space.low,
                "max_clusters_per_arm": space.high,
            }
        return designs, {"min_cluster_size": space.low, "max_cluster_size": space.high}
    designs = [
        _two_arm(analysis, target, (size, space.ratio * size))
        for size in range(space.min_per_arm, space.max_per_arm + 1)
    ]
    return designs, {"min_per_arm": space.min_per_arm, "max_per_arm": space.max_per_arm}


def _bound(value: float, outward: str) -> dict:
    """An interval end rounded outward to six decimals, so rounding never narrows it."""
    scaled = value * 1_000_000
    rounded = Fraction(math.floor(scaled) if outward == "down" else math.ceil(scaled), 1_000_000)
    return {"fraction": str(rounded), "decimal_approximation": f"{float(rounded):.6f}"}


def _rate(found: engine.Estimate) -> dict:
    return fraction_record(Fraction(found.rejected, found.runs))


def _passes(found: engine.Estimate, minimum: Fraction) -> bool:
    return found.lower >= float(minimum)


def evaluate(
    analysis, target: PowerTargetIR, design: Design, settings: SimulationIR, stream: str
) -> dict:
    """Power at the planning point and Type I error at the null's boundary, by simulation."""
    power = engine.estimate(
        design.trial(False), settings.runs, engine.Stream(settings.seed, stream, *design.labels)
    )
    error = engine.estimate(
        design.trial(True), settings.runs, engine.Stream(settings.seed, "typeI", *design.labels)
    )
    model = analysis.method.simulation
    judged = departs(target.at)
    if judged:
        typeI_met = error.upper <= float(target.maximum_typeI)
        typeI_settled = typeI_met or error.lower > float(target.maximum_typeI)
    else:
        # Judged on the test's level, as calculate(...) does. Under these scenarios the
        # level holds exactly or nearly, so the simulated error is reported, not judged: an
        # interval above the target would mostly be chance.
        typeI_met, typeI_settled = analysis.alpha <= target.maximum_typeI, True
    met = _passes(power, target.minimum)
    return {
        **design.record,
        "power": _rate(power),
        "power_lower": _bound(power.lower, "down"),
        "power_upper": _bound(power.upper, "up"),
        "power_rejected": power.rejected,
        "minimum_power": fraction_record(target.minimum),
        "power_target_met": met,
        "power_settled": met or power.upper < float(target.minimum),
        "typeI": _rate(error),
        "typeI_lower": _bound(error.lower, "down"),
        "typeI_upper": _bound(error.upper, "up"),
        "typeI_rejected": error.rejected,
        "alpha": fraction_record(analysis.alpha),
        "maximum_typeI": fraction_record(target.maximum_typeI),
        "typeI_target_met": typeI_met,
        "typeI_settled": typeI_settled,
        "typeI_judged": judged,
        "runs": settings.runs,
        "seed": settings.seed,
        "stream": stream,
        "scenario": design.scenario,
        "model": model.key,
        "model_version": model.version,
        "engine_version": engine.ENGINE_VERSION,
        "generator": engine.GENERATOR,
        "interval": INTERVAL,
        "note": ESTIMATE,
    }


def assumptions(analysis) -> list[dict]:
    """The test's own assumptions, then the simulation's, then the planning point's."""
    model = analysis.method.simulation
    items = [mark(item) for item in (*analysis.assumptions, *model.assumptions)]
    return [*items, identify(PLANNING_POINT)]


def _scenario_words(point, observational: bool) -> str:
    parts = []
    if getattr(point, "sd_treatment", None) is not None:
        parts.append(f"standard deviation {point.sd_treatment} in the treatment arm")
    if getattr(point, "exposure_skewness", None):
        parts.append(f"exposure skewness {point.exposure_skewness}")
    if getattr(point, "skewness", None):
        parts.append(f"{'error ' if observational else ''}skewness {point.skewness}")
    if getattr(point, "effect_delay", None):
        parts.append(f"the hazard ratio applying from {point.effect_delay} after entry")
    return "".join(f", {part}" for part in parts)


def _goal(analysis, target: PowerTargetIR) -> str:
    point, observational = target.at, _observational(analysis)
    words = association_planning.describe_point(point) if observational else describe_point(point)
    typeI = (
        f"simulated Type I at most {target.maximum_typeI}, judged like power since the "
        "scenario leaves the test's theory"
        if departs(point)
        else f"the test's level {analysis.alpha} at most {target.maximum_typeI}"
    )
    return (
        f"power at least {target.minimum} at {words}{_scenario_words(point, observational)}, "
        f"and {typeI}"
    )


def _statement(subject, analysis, target: PowerTargetIR, runs: str) -> str:
    """What will be simulated: the declared study, or a search and its range."""
    title, goal = analysis.method.title, _goal(analysis, target)
    if isinstance(subject, FeasibilityIR):
        if _observational(analysis):
            sizes = f"with {analysis.plan.model.total} participants"
        elif clustered_test(analysis):
            (k_c, k_t), (m_c, m_t) = declared_clusters(analysis)
            sizes = f"with ({k_c}, {k_t}) clusters per arm of mean size ({m_c}, {m_t})"
        else:
            model = analysis.plan.model
            sizes = f"with arm sizes ({model.n_control}, {model.n_treatment})"
        return f"{title} {sizes}: {goal}, estimated from {runs}."
    space = subject.candidates
    passing = (
        f"whose simulated power has its 95% interval at or above {target.minimum}, confirmed "
        f"by an independent run: {goal}"
    )
    if _observational(analysis):
        return (
            f"{title}: the first total from {space.min_n} to {space.max_n} {passing}. Each "
            f"size uses {runs}."
        )
    if isinstance(space, ClusterCandidatesIR):
        varied = (
            f"clusters per arm from {space.low} to {space.high}, each of {space.cluster_size} "
            "participants"
            if space.varies == "clusters"
            else f"cluster sizes from {space.low} to {space.high}"
        )
        return f"{title}: the first design, with {varied}, {passing}. Each design uses {runs}."
    allocation = "equal-arm" if space.ratio == 1 else f"1:{space.ratio} allocation"
    return (
        f"{title}: the first {allocation} size from {space.min_per_arm} to {space.max_per_arm} "
        f"controls {passing}. Each size uses {runs}."
    )


def describe(subject, settings: SimulationIR) -> dict:
    """The simulated planning claim before running: what will be estimated and how."""
    analysis, target = planned_analysis(subject), subject.target
    method, model = analysis.method, analysis.method.simulation
    runs = f"{settings.runs:,} simulated studies from seed {settings.seed}"
    text = f"{_statement(subject, analysis, target, runs)} Power is a {ESTIMATE}."
    listed = assumptions(analysis)
    report = planning_report("simulated_planning", text, [item["text"] for item in listed])
    report["method"] = method.to_dict()
    report["simulation"] = {
        **model.to_dict(),
        "runs": settings.runs,
        "seed": settings.seed,
        "engine_version": engine.ENGINE_VERSION,
        "generator": engine.GENERATOR,
        "interval": INTERVAL,
    }
    report["assumptions"] = listed
    report["references"] = list(dict.fromkeys((*method.references, *model.references)))
    return report


def _decision(calculation: dict) -> str:
    """Met when both targets are met; not met when either is clearly missed; else undecided."""
    outcomes = [
        (calculation["power_target_met"], calculation["power_settled"]),
        (calculation["typeI_target_met"], calculation.get("typeI_settled", True)),
    ]
    if any(not met and settled for met, settled in outcomes):
        return "target_not_met"
    return "target_met" if all(met for met, _ in outcomes) else "undecided"


def run(report: dict, subject, settings: SimulationIR) -> dict:
    """Estimate power at the declared sizes, or search up the range for the first size that
    passes, and confirm it with an independent run."""
    analysis, target = planned_analysis(subject), subject.target
    if isinstance(subject, FeasibilityIR):
        calculation = evaluate(analysis, target, _declared(analysis, target), settings, "power")
        report["calculation"] = calculation
        report["decision"] = _decision(calculation)
        return report
    designs, search = _searched(analysis, target, subject.candidates)
    curve, confirmations = [], 0
    for evaluated, design in enumerate(designs, 1):
        found = engine.estimate(
            design.trial(False),
            settings.runs,
            engine.Stream(settings.seed, "search", *design.labels),
        )
        curve.append(
            {
                **design.curve,
                "power": round(found.rate, 6),
                "lower": round(found.lower, 6),
                "upper": round(found.upper, 6),
            }
        )
        if not _passes(found, target.minimum):
            continue
        confirmations += 1
        calculation = evaluate(analysis, target, design, settings, "confirm")
        if not calculation["power_target_met"]:
            continue
        if calculation["typeI_judged"] and not calculation["typeI_target_met"]:
            continue
        report["calculation"] = {
            **calculation,
            **search,
            "candidates_evaluated": evaluated,
            "confirmations": confirmations,
            "search_power": _rate(found),
            "curve": curve,
        }
        report["decision"] = _decision(calculation)
        return report
    report["calculation"] = {
        **search,
        "candidates_evaluated": len(curve),
        "confirmations": confirmations,
        "power_target_met": False,
        "minimum_power": fraction_record(target.minimum),
        "runs": settings.runs,
        "seed": settings.seed,
        "curve": curve,
        "note": ESTIMATE,
    }
    report["decision"] = "no_feasible_candidate"
    return report
