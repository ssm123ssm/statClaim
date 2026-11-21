"""Power by simulation for cited tests: estimates with Monte Carlo error, never evidence.

The simulation model comes from the method's registry entry (methods/simulation.py) and
the draws from simulation.py. This module reads the declaration, runs the model and says
what the estimate rests on.

A size passes when the whole 95% interval for its power is at or above the target. A
sample-size search goes up from the smallest size and simulates every size it passes, so
nothing assumes that power rises with the sample size. The first size that passes is
simulated again from an independent stream, and the reported power comes from that run,
so picking the size does not bias the estimate.

A test of cluster summaries is simulated in clusters: its sizes are clusters per arm, and
each arm's mean cluster size and the variation of sizes go to the model.

Simulated Type I is reported, not judged, while the test's level holds by theory. In a
scenario that leaves normal outcomes with a common SD (sd_treatment or skewness on the
planning point), the level no longer holds by theory, so Type I is judged like power: met
when its whole 95% interval is at or below maximum_typeI, and a search passes over sizes
where it is not met.
"""

import math
from fractions import Fraction

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
    CitedAnalysisIR,
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


def _side(analysis: CitedAnalysisIR) -> str:
    return NULL_FORMS[analysis.hypothesis.predicate][1].favours or "both"


def _simulated_values(point, cluster_sizes=None) -> dict[str, float]:
    """The planning point as the model reads it, with cluster sizes and any scenario."""
    values = _values(point)
    for name in ("sd_treatment", "skewness", "cluster_size_cv"):
        if getattr(point, name, None) is not None:
            values[name] = float(getattr(point, name))
    if cluster_sizes is not None:
        values["size_control"], values["size_treatment"] = (float(m) for m in cluster_sizes)
    return values


def _trial(
    analysis: CitedAnalysisIR, point, sizes: tuple[int, int], cluster_sizes=None, *, at_null=False
):
    """One simulated study at the planning point, or at the null's boundary for Type I error.
    For a cluster test, sizes are clusters and cluster_sizes the participants in each."""
    values = _simulated_values(point, cluster_sizes)
    null_value = float(analysis.hypothesis.value)
    if at_null:
        values = {**values, "value": null_value}
        if "p_treatment" in values:
            values["p_treatment"] = values["p_control"]
    return analysis.method.simulation.trial(
        values, *sizes, null_value, float(analysis.alpha), _side(analysis)
    )


def _bound(value: float, outward: str) -> dict:
    """An interval end rounded outward to six decimals, so rounding never narrows it."""
    scaled = value * 1_000_000
    rounded = Fraction(math.floor(scaled) if outward == "down" else math.ceil(scaled), 1_000_000)
    return {"fraction": str(rounded), "decimal_approximation": f"{float(rounded):.6f}"}


def _rate(found: engine.Estimate) -> dict:
    return fraction_record(Fraction(found.rejected, found.runs))


def _passes(found: engine.Estimate, minimum: Fraction) -> bool:
    return found.lower >= float(minimum)


def _labels(sizes, cluster_sizes) -> tuple:
    """What tells one design's streams from another's: the sizes, and cluster sizes."""
    return (*sizes, *(() if cluster_sizes is None else (str(m) for m in cluster_sizes)))


def evaluate(
    analysis: CitedAnalysisIR,
    target: PowerTargetIR,
    sizes: tuple[int, int],
    settings: SimulationIR,
    stream: str,
    cluster_sizes=None,
) -> dict:
    """Power at the planning point and Type I error at the null's boundary, by simulation."""
    n_control, n_treatment = sizes
    labels = _labels(sizes, cluster_sizes)
    power = engine.estimate(
        _trial(analysis, target.at, sizes, cluster_sizes),
        settings.runs,
        engine.Stream(settings.seed, stream, *labels),
    )
    error = engine.estimate(
        _trial(analysis, target.at, sizes, cluster_sizes, at_null=True),
        settings.runs,
        engine.Stream(settings.seed, "typeI", *labels),
    )
    model = analysis.method.simulation
    if cluster_sizes is None:
        design = {
            "n_control": n_control,
            "n_treatment": n_treatment,
            "total_sample_size": n_control + n_treatment,
        }
    else:
        design = _cluster_record(target, sizes, cluster_sizes)
        if getattr(target.at, "cluster_size_cv", None):
            # 1 + (m - 1) icc holds for clusters of equal size only.
            design.pop("design_effect", None)
        if getattr(target.at, "cluster_size_cv", None) is not None:
            design["cluster_size_cv"] = fraction_record(target.at.cluster_size_cv)
    judged = departs(target.at)
    if judged:
        typeI_met = error.upper <= float(target.maximum_typeI)
        typeI_settled = typeI_met or error.lower > float(target.maximum_typeI)
    else:
        # Judged on the test's level, as calculate(...) does. Under these scenarios the
        # level holds exactly or nearly, so the simulated error is reported, not judged: an
        # interval above the target would mostly be chance.
        typeI_met, typeI_settled = analysis.alpha <= target.maximum_typeI, True
    return {
        **design,
        "power": _rate(power),
        "power_lower": _bound(power.lower, "down"),
        "power_upper": _bound(power.upper, "up"),
        "power_rejected": power.rejected,
        "minimum_power": fraction_record(target.minimum),
        "power_target_met": _passes(power, target.minimum),
        "power_settled": _passes(power, target.minimum) or power.upper < float(target.minimum),
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
        "scenario": model.scenario(_simulated_values(target.at, cluster_sizes)),
        "model": model.key,
        "model_version": model.version,
        "engine_version": engine.ENGINE_VERSION,
        "generator": engine.GENERATOR,
        "interval": INTERVAL,
        "note": ESTIMATE,
    }


def assumptions(analysis: CitedAnalysisIR) -> list[dict]:
    """The test's own assumptions, then the simulation's, then the planning point's."""
    model = analysis.method.simulation
    items = [mark(item) for item in (*analysis.assumptions, *model.assumptions)]
    return [*items, identify(PLANNING_POINT)]


def describe(subject, settings: SimulationIR) -> dict:
    """The simulated planning claim before running: what will be estimated and how."""
    analysis, target = planned_analysis(subject), subject.target
    method, model = analysis.method, analysis.method.simulation
    point = target.at
    scenario = ""
    if getattr(point, "sd_treatment", None) is not None:
        scenario += f", standard deviation {point.sd_treatment} in the treatment arm"
    if getattr(point, "skewness", None):
        scenario += f", skewness {point.skewness}"
    typeI = (
        f"simulated Type I at most {target.maximum_typeI}, judged like power since the "
        "scenario leaves normal outcomes with a common SD"
        if departs(point)
        else f"the test's level {analysis.alpha} at most {target.maximum_typeI}"
    )
    goal = f"power at least {target.minimum} at {describe_point(point)}{scenario}, and {typeI}"
    runs = f"{settings.runs:,} simulated studies from seed {settings.seed}"
    if isinstance(subject, FeasibilityIR) and clustered_test(analysis):
        (k_c, k_t), (m_c, m_t) = declared_clusters(analysis)
        text = (
            f"{method.title} with ({k_c}, {k_t}) clusters per arm of mean size ({m_c}, {m_t}): "
            f"{goal}, estimated from {runs}."
        )
    elif isinstance(getattr(subject, "candidates", None), ClusterCandidatesIR):
        candidates = subject.candidates
        varied = (
            f"clusters per arm from {candidates.low} to {candidates.high}, each of "
            f"{candidates.cluster_size} participants"
            if candidates.varies == "clusters"
            else f"cluster sizes from {candidates.low} to {candidates.high}"
        )
        text = (
            f"{method.title}: the first design, with {varied}, whose simulated power has its 95% "
            f"interval at or above {target.minimum}, confirmed by an independent run: {goal}. "
            f"Each design uses {runs}."
        )
    elif isinstance(subject, FeasibilityIR):
        model_sizes = analysis.plan.model
        text = (
            f"{method.title} with arm sizes ({model_sizes.n_control}, "
            f"{model_sizes.n_treatment}): {goal}, estimated from {runs}."
        )
    else:
        candidates = subject.candidates
        allocation = "equal-arm" if candidates.ratio == 1 else f"1:{candidates.ratio} allocation"
        text = (
            f"{method.title}: the first {allocation} size from {candidates.min_per_arm} to "
            f"{candidates.max_per_arm} controls whose simulated power has its 95% interval at "
            f"or above {target.minimum}, confirmed by an independent run: {goal}. Each size "
            f"uses {runs}."
        )
    text += f" Power is a {ESTIMATE}."
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
        model = analysis.plan.model
        if clustered_test(analysis):
            clusters, cluster_sizes = declared_clusters(analysis)
            calculation = evaluate(analysis, target, clusters, settings, "power", cluster_sizes)
        else:
            sizes = (model.n_control, model.n_treatment)
            calculation = evaluate(analysis, target, sizes, settings, "power")
        report["calculation"] = calculation
        report["decision"] = _decision(calculation)
        return report
    candidates = subject.candidates
    if isinstance(candidates, ClusterCandidatesIR):
        designs = list(candidates.designs())
        search = (
            {
                "cluster_size": candidates.cluster_size,
                "min_clusters_per_arm": candidates.low,
                "max_clusters_per_arm": candidates.high,
            }
            if candidates.varies == "clusters"
            else {"min_cluster_size": candidates.low, "max_cluster_size": candidates.high}
        )
    else:
        designs = [
            ((size, candidates.ratio * size), None)
            for size in range(candidates.min_per_arm, candidates.max_per_arm + 1)
        ]
        search = {"min_per_arm": candidates.min_per_arm, "max_per_arm": candidates.max_per_arm}
    curve, confirmations = [], 0
    for evaluated, (sizes, cluster_sizes) in enumerate(designs, 1):
        found = engine.estimate(
            _trial(analysis, target.at, sizes, cluster_sizes),
            settings.runs,
            engine.Stream(settings.seed, "search", *_labels(sizes, cluster_sizes)),
        )
        point = {
            "n_control": sizes[0],
            "n_treatment": sizes[1],
            "power": round(found.rate, 6),
            "lower": round(found.lower, 6),
            "upper": round(found.upper, 6),
        }
        if cluster_sizes is not None:
            point.update(
                clusters_control=sizes[0],
                cluster_size=cluster_sizes[0],
                n_control=sizes[0] * cluster_sizes[0],
                n_treatment=sizes[1] * cluster_sizes[1],
            )
        curve.append(point)
        if not _passes(found, target.minimum):
            continue
        confirmations += 1
        calculation = evaluate(analysis, target, sizes, settings, "confirm", cluster_sizes)
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
