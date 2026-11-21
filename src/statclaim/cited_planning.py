"""Approximate power for cited tests: a calculation, never evidence and never a bound.

The formula comes from the method's registry entry (methods/power.py). This module
only reads the declaration, calls the formula and reports what it rests on. A test of
cluster summaries is sized in clusters: its formula also sees the intracluster correlation
and each arm's mean cluster size.
"""

from fractions import Fraction

from statclaim.fisher import fraction_record
from statclaim.language import (
    CitedAnalysisIR,
    ClusterCandidatesIR,
    ExponentialSurvivalIR,
    FeasibilityIR,
    HazardRatioIR,
    MeanDifferenceIR,
    PowerTargetIR,
    RatesIR,
    cited_formula,
    clustered_test,
    planned_analysis,
)
from statclaim.methods import NULL_FORMS
from statclaim.methods.core import PowerResult
from statclaim.methods.identify import identify, mark
from statclaim.methods.power import LOGISTIC_WALD, wald_rejection
from statclaim.report import planning_report

APPROXIMATE = "normal approximation, not a bound"
# Clusters so large that a cluster's summary varies only through the cluster effect.
UNBOUNDED_CLUSTER = 1e15
PLANNING_POINT = "The planning point is an input for planning, not an established fact."


def _values(point) -> dict[str, float]:
    if isinstance(point, MeanDifferenceIR):
        values = {"value": float(point.value), "sd": float(point.sd)}
    elif isinstance(point, RatesIR):
        values = {"p_control": float(point.p_control), "p_treatment": float(point.p_treatment)}
    elif isinstance(point, ExponentialSurvivalIR):
        values = {
            "value": float(point.hazard_ratio),
            "control_median": float(point.control_median),
            "accrual": float(point.accrual),
            "follow_up": float(point.follow_up),
        }
        if point.dropout is not None:
            values.update(dropout=float(point.dropout), dropout_time=float(point.dropout_time))
    else:
        values = {"value": float(point.value), "events": float(point.events)}
    if getattr(point, "icc", None) is not None:
        values["icc"] = float(point.icc)
    return values


def describe_point(point) -> str:
    icc = getattr(point, "icc", None)
    clustering = "" if icc is None else f" and intracluster correlation {icc}"
    if isinstance(point, MeanDifferenceIR):
        return f"a mean difference of {point.value} with standard deviation {point.sd}{clustering}"
    if isinstance(point, HazardRatioIR):
        return f"a hazard ratio of {point.value} with {point.events} events"
    if isinstance(point, ExponentialSurvivalIR):
        lost = (
            f", {point.dropout} dropping out by time {point.dropout_time}"
            if point.dropout is not None
            else ""
        )
        return (
            f"a hazard ratio of {point.hazard_ratio}, a control median of "
            f"{point.control_median}, accrual over {point.accrual} and follow-up of "
            f"{point.follow_up}{lost}"
        )
    return f"p_control = {point.p_control}, p_treatment = {point.p_treatment}{clustering}"


def declared_clusters(analysis: CitedAnalysisIR):
    """The declared clusters per arm, and each arm's mean number of participants per cluster."""
    assignment = analysis.plan.model.assignment
    clusters = (assignment.clusters_control, assignment.clusters_treatment)
    sizes = (
        Fraction(assignment.n_control, clusters[0]),
        Fraction(assignment.n_treatment, clusters[1]),
    )
    return clusters, sizes


def approximate_power(
    analysis: CitedAnalysisIR, point, n_control: int, n_treatment: int, cluster_sizes=None
):
    """Power from the method's formula. For a test of cluster summaries, the sizes count
    clusters and cluster_sizes gives each arm's participants per cluster."""
    null = analysis.hypothesis
    values = _values(point)
    if cluster_sizes is not None:
        values["size_control"], values["size_treatment"] = (float(m) for m in cluster_sizes)
    return cited_formula(analysis, point).function(
        values,
        n_control,
        n_treatment,
        float(null.value),
        float(analysis.alpha),
        NULL_FORMS[null.predicate][1].favours or "both",
    )


def _record(value: float) -> dict:
    """A rounded decimal: exact as written, but only an approximation of the formula's value."""
    rounded = Fraction(f"{value:.6f}")
    return {"fraction": str(rounded), "decimal_approximation": f"{value:.6f}"}


def _cluster_record(target: PowerTargetIR, clusters, cluster_sizes) -> dict:
    """Clusters, participants and the design effect of a cluster-randomised candidate."""
    (k_c, k_t), (m_c, m_t) = clusters, cluster_sizes
    icc = target.at.icc
    n_control, n_treatment = k_c * m_c, k_t * m_t
    record = {
        "clusters_control": k_c,
        "clusters_treatment": k_t,
        "total_clusters": k_c + k_t,
        "cluster_size_control": fraction_record(m_c),
        "cluster_size_treatment": fraction_record(m_t),
        "n_control": int(n_control),
        "n_treatment": int(n_treatment),
        "total_sample_size": int(n_control + n_treatment),
        "icc": fraction_record(icc),
        "degrees_of_freedom": k_c + k_t - 2,
    }
    if m_c == m_t:
        record["design_effect"] = fraction_record(1 + (m_c - 1) * icc)
    return record


def evaluate(
    analysis: CitedAnalysisIR, target: PowerTargetIR, sizes: tuple[int, int], cluster_sizes=None
) -> dict:
    """The formula's numbers for one design. For a test of cluster summaries, sizes are the
    clusters per arm and cluster_sizes the participants in each cluster."""
    n_control, n_treatment = sizes
    result: PowerResult = approximate_power(
        analysis, target.at, n_control, n_treatment, cluster_sizes
    )
    formula = cited_formula(analysis, target.at)
    if cluster_sizes is None:
        design = {
            "n_control": n_control,
            "n_treatment": n_treatment,
            "total_sample_size": n_control + n_treatment,
        }
    else:
        design = _cluster_record(target, sizes, cluster_sizes)
    if formula.key == LOGISTIC_WALD.key:
        # Exact too: the Wald test's rejection rate when both arms share the control rate.
        null = analysis.hypothesis
        control = float(target.at.p_control)
        design["typeI_at_control_rate"] = _record(
            wald_rejection(
                n_control,
                n_treatment,
                float(analysis.alpha),
                NULL_FORMS[null.predicate][1].favours or "both",
                control,
                control,
            )
        )
    if result.expected_events is not None:
        design["expected_events"] = _record(result.expected_events)
        design["event_probability_control"] = _record(result.event_probabilities[0])
        design["event_probability_treatment"] = _record(result.event_probabilities[1])
    return {
        **design,
        "power": _record(result.power),
        "minimum_power": fraction_record(target.minimum),
        "power_target_met": result.power >= target.minimum,
        "critical_estimate": _record(result.critical),
        "reject_when": result.direction,
        "standard_error": _record(result.standard_error),
        "alpha": fraction_record(analysis.alpha),
        "maximum_typeI": fraction_record(target.maximum_typeI),
        "typeI_target_met": analysis.alpha <= target.maximum_typeI,
        "formula": formula.key,
        "formula_version": formula.version,
        "approximation": formula.approximation,
    }


def assumptions(analysis: CitedAnalysisIR, point) -> list[dict]:
    """The test's own assumptions, then the formula's, then the planning point's."""
    formula = cited_formula(analysis, point)
    items = [mark(item) for item in (*analysis.assumptions, *formula.assumptions)]
    return [*items, identify(PLANNING_POINT)]


def describe(subject) -> dict:
    """The planning claim before calculation: what will be computed and what it rests on."""
    analysis, target = planned_analysis(subject), subject.target
    method = analysis.method
    point = describe_point(target.at)
    goal = (
        f"power at least {target.minimum} at {point}, and the test's level {analysis.alpha} "
        f"at most {target.maximum_typeI}"
    )
    if isinstance(subject, FeasibilityIR) and clustered_test(analysis):
        (k_c, k_t), (m_c, m_t) = declared_clusters(analysis)
        text = (
            f"{method.title} with ({k_c}, {k_t}) clusters per arm of mean size ({m_c}, {m_t}): "
            f"{goal}."
        )
    elif isinstance(subject, FeasibilityIR):
        model = analysis.plan.model
        text = f"{method.title} with arm sizes ({model.n_control}, {model.n_treatment}): {goal}."
    elif isinstance(subject.candidates, ClusterCandidatesIR):
        candidates = subject.candidates
        if candidates.varies == "clusters":
            text = (
                f"{method.title}: the first number of clusters per arm from {candidates.low} "
                f"to {candidates.high}, each of {candidates.cluster_size} participants, with "
                f"{goal}."
            )
        else:
            (k_c, k_t), _ = declared_clusters(analysis)
            text = (
                f"{method.title}: the first cluster size from {candidates.low} to "
                f"{candidates.high} participants, with the declared ({k_c}, {k_t}) clusters "
                f"per arm, with {goal}."
            )
    else:
        candidates = subject.candidates
        allocation = "equal-arm" if candidates.ratio == 1 else f"1:{candidates.ratio} allocation"
        text = (
            f"{method.title}: the first {allocation} size from {candidates.min_per_arm} to "
            f"{candidates.max_per_arm} controls with {goal}."
        )
    formula = cited_formula(analysis, target.at)
    text += f" Power is a {formula.approximation}."
    listed = assumptions(analysis, target.at)
    report = planning_report("cited_planning", text, [item["text"] for item in listed])
    report["method"] = method.to_dict()
    report["formula"] = formula.to_dict()
    report["assumptions"] = listed
    report["references"] = [*method.references, *formula.references]
    return report


def run(report: dict, subject) -> dict:
    """Calculate approximate power, or search ascending for the first size that reaches it."""
    analysis, target = planned_analysis(subject), subject.target
    if isinstance(subject, FeasibilityIR):
        model = analysis.plan.model
        if clustered_test(analysis):
            calculation = evaluate(analysis, target, *declared_clusters(analysis))
        else:
            calculation = evaluate(analysis, target, (model.n_control, model.n_treatment))
        met = calculation["power_target_met"] and calculation["typeI_target_met"]
        report["calculation"] = calculation
        report["decision"] = "target_met" if met else "target_not_met"
        return report
    candidates = subject.candidates
    if isinstance(candidates, ClusterCandidatesIR):
        return _run_clusters(report, analysis, target, candidates)
    search = {"min_per_arm": candidates.min_per_arm, "max_per_arm": candidates.max_per_arm}
    for evaluated, size in enumerate(range(candidates.min_per_arm, candidates.max_per_arm + 1), 1):
        sizes = (size, candidates.ratio * size)
        if approximate_power(analysis, target.at, *sizes).power >= target.minimum:
            calculation = evaluate(analysis, target, sizes)
            met = calculation["typeI_target_met"]
            report["calculation"] = {**calculation, **search, "candidates_evaluated": evaluated}
            report["decision"] = "target_met" if met else "target_not_met"
            return report
    report["calculation"] = {
        **search,
        "candidates_evaluated": candidates.max_per_arm - candidates.min_per_arm + 1,
        "power_target_met": False,
        "approximation": cited_formula(analysis, target.at).approximation,
    }
    report["decision"] = "no_feasible_candidate"
    return report


def _run_clusters(report: dict, analysis, target, candidates: ClusterCandidatesIR) -> dict:
    """Search clusters per arm, or participants per cluster, ascending for the first design
    that reaches the target. When cluster sizes are searched and none is enough, the power
    as clusters grow without bound shows that more participants cannot help."""
    if candidates.varies == "clusters":
        search = {
            "cluster_size": candidates.cluster_size,
            "min_clusters_per_arm": candidates.low,
            "max_clusters_per_arm": candidates.high,
        }
    else:
        search = {"min_cluster_size": candidates.low, "max_cluster_size": candidates.high}
    evaluated = 0
    for evaluated, (clusters, sizes) in enumerate(candidates.designs(), 1):
        if approximate_power(analysis, target.at, *clusters, sizes).power >= target.minimum:
            calculation = evaluate(analysis, target, clusters, sizes)
            report["calculation"] = {**calculation, **search, "candidates_evaluated": evaluated}
            met = calculation["typeI_target_met"]
            report["decision"] = "target_met" if met else "target_not_met"
            return report
    calculation = {
        **search,
        "candidates_evaluated": evaluated,
        "power_target_met": False,
        "approximation": cited_formula(analysis, target.at).approximation,
    }
    if candidates.varies == "cluster_size" and target.at.icc > 0:
        clusters, _ = declared_clusters(analysis)
        limit = (UNBOUNDED_CLUSTER, UNBOUNDED_CLUSTER)
        calculation["power_ceiling"] = _record(
            approximate_power(analysis, target.at, *clusters, limit).power
        )
    report["calculation"] = calculation
    report["decision"] = "no_feasible_candidate"
    return report
