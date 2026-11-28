"""The canonical JSON form of typed objects, for derivations and reports."""

from fractions import Fraction

from statclaim.association import (
    CELLS,
)
from statclaim.composition import MODES
from statclaim.language.core import (
    LocatedValue,
    fail,
)
from statclaim.language.ir import (
    AnalysisIR,
    AssignmentIR,
    AssociationAnalysisIR,
    AssociationNullIR,
    AssociationResultIR,
    AssociationTableIR,
    AsymptoticMcNemarAnalysisIR,
    CalculationResultIR,
    CandidatesIR,
    CaseControlStudyIR,
    CitedAnalysisIR,
    CitedAssociationIR,
    ClaimIR,
    ClusterCandidatesIR,
    CohortStudyIR,
    ComposedFamilyIR,
    CorrelationIR,
    CountCandidatesIR,
    CrossSectionalStudyIR,
    DifferenceIntervalIR,
    DiscordantPairsIR,
    EffectIntervalIR,
    EndpointPointsIR,
    ExponentialSurvivalIR,
    ExposurePrevalenceIR,
    FamilyIR,
    FarringtonManningAnalysisIR,
    FeasibilityIR,
    FieldIR,
    GroupCandidatesIR,
    HazardRatioIR,
    HypothesisIR,
    IncidenceRatesIR,
    IntervalCandidatesIR,
    IntervalIR,
    LookCandidatesIR,
    MatchedAnalysisIR,
    MatchedIntervalIR,
    MatchedPairsIR,
    MatchedResultIR,
    MatchedStudyIR,
    MeanDifferenceIR,
    NullScenariosIR,
    ObservationalStudyIR,
    ObservationIR,
    ObservedEventsIR,
    OddsPerSdIR,
    OneArmCandidatesIR,
    OneArmModelIR,
    OneSampleAnalysisIR,
    OneSampleObservationIR,
    OneSampleScoreAnalysisIR,
    OutcomeIR,
    OutcomeMeansIR,
    OutcomeNullIR,
    OutcomePrevalenceIR,
    PearsonAnalysisIR,
    PersonTimeStudyIR,
    PlanIR,
    PlannedIntervalIR,
    PowerTargetIR,
    PrecisionTargetIR,
    PriorIR,
    ProportionIR,
    ProportionZAnalysisIR,
    RandomisationAnalysisIR,
    RateAnalysisIR,
    RateIR,
    RateRatioIR,
    RateResultIR,
    RatesIR,
    ReestimationIR,
    RisksIR,
    RuleIR,
    SequentialIR,
    SharpNullIR,
    SingleProportionIR,
    SizingIR,
    SlopeIR,
    StratumIR,
    TotalCandidatesIR,
    TwoArmModelIR,
    TwoStageAnalysisIR,
    TwoStageCandidatesIR,
    TwoStageModelIR,
    TwoStageObservationIR,
    VerificationResultIR,
)
from statclaim.matched import (
    PAIR_CELLS,
)
from statclaim.methods import NULL_FORMS, OUTCOMES
from statclaim.observational_planning import SEARCH_KEYS as GROUP_SEARCH_KEYS


def _study_extras(study: "ObservationalStudyIR") -> dict:
    """Scales and survey designs, recorded only when they differ from the defaults."""
    extras: dict[str, object] = {}
    if study.exposure_scale != "binary":
        extras["exposure_scale"] = study.exposure_scale
    if study.outcome_scale != "binary":
        extras["outcome_scale"] = study.outcome_scale
    if study.survey != "simple_random":
        extras["survey"] = study.survey
    if study.clusters is not None:
        extras["clusters"] = study.clusters
    return extras


def _with_cluster_cv(point: dict, value) -> dict:
    """How much cluster sizes vary, and a simulation's scenario, are written only when given."""
    for name in ("cluster_size_cv", "sd_treatment", "skewness", "exposure_skewness"):
        if getattr(value, name, None) is not None:
            point = {**point, name: str(getattr(value, name))}
    return point


def _check_skewed_point(analysis: object, target: LocatedValue) -> None:
    """Skewed data are simulated for the correlation and slope tests, without covariates."""
    if not isinstance(analysis, CitedAssociationIR) or not analysis.method.simulation:
        key = getattr(getattr(analysis, "method", None), "key", "this analysis")
        fail(
            "planning_point",
            f"{key} is not simulated with skewed data. skewness and exposure_skewness are for "
            "simulating the tests of a correlation or a regression slope.",
            target.span,
        )
    if analysis.covariates:
        fail(
            "planning_point",
            "Skewed data are simulated without covariates for now. With covariates and normal "
            "data, calculate(...) gives the slope's exact power.",
            target.span,
        )


def _with_design_effect(point: dict, value) -> dict:
    """A survey's design effect is written only when the point gives one."""
    effect = getattr(value, "design_effect", None)
    return point if effect is None else {**point, "design_effect": str(effect)}


def normalize(value: object) -> object:
    """Serialize semantic objects, without implying a proof or executing a backend."""
    match value:
        case Fraction():
            return str(value)
        case TwoArmModelIR(assignment=assignment, measured=measured):
            # Only what a file declared beyond the arm sizes is written, so a model keeps
            # the same record however it is spelled and whatever was added later.
            outcome, sizes = normalize(measured), normalize(assignment)
            assert isinstance(outcome, dict) and isinstance(sizes, dict)  # see their cases below
            return {
                "module": OUTCOMES[measured.kind].constructor,
                **sizes,
                **{key: value for key, value in outcome.items() if key not in ("outcome", "name")},
                **({"outcome_name": outcome["name"]} if "name" in outcome else {}),
            }
        case AssignmentIR(n_control=nc, n_treatment=nt, clusters_control=cc):
            result: dict[str, object] = {"n_control": nc, "n_treatment": nt}
            if cc is not None:
                result.update(clusters_control=cc, clusters_treatment=value.clusters_treatment)
            if value.randomisation is not None:
                result["randomisation"] = value.randomisation
            if value.strata:
                result["strata"] = [list(stratum) for stratum in value.strata]
            if value.block_size is not None:
                result["block_size"] = value.block_size
            if value.population is not None:
                result["population"] = value.population
            return result
        case StratumIR(control=control, treatment=treatment):
            return {"control": control, "treatment": treatment}
        case OutcomeIR(kind=kind, better=better, measurements=measurements):
            return {
                "outcome": kind,
                **({"better": better} if better else {}),
                **({"measurements": measurements} if measurements > 1 else {}),
                **({"name": value.name} if value.name is not None else {}),
            }
        case OutcomeNullIR(model=model, predicate=predicate, value=bound):
            result = {"predicate": predicate, "model": normalize(model)}
            if NULL_FORMS[predicate][1].takes_value:
                result["value"] = str(bound)
            return result
        case SharpNullIR(model=model, predicate=predicate):
            return {"predicate": predicate, "model": normalize(model)}
        case CrossSectionalStudyIR(n=n, exposure=exposure, outcome=outcome):
            return {
                "study": "cross_sectional",
                "n": n,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case CohortStudyIR(exposure=exposure, outcome=outcome):
            sizes = (
                {"n": value.n}
                if value.groups is None
                else {"exposed": value.exposed, "unexposed": value.unexposed}
            )
            return {
                "study": "cohort",
                **sizes,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case CaseControlStudyIR(cases=cases, controls=controls, exposure=exposure, outcome=outcome):
            return {
                "study": "case_control",
                "cases": cases,
                "controls": controls,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case PersonTimeStudyIR(exposure=exposure, outcome=outcome):
            return {
                "study": "person_time_cohort",
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case RateAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "rate_test",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
        case ObservedEventsIR(model=model):
            return {
                "model": normalize(model),
                "exposed_events": value.exposed_events,
                "exposed_time": str(value.exposed_time),
                "unexposed_events": value.unexposed_events,
                "unexposed_time": str(value.unexposed_time),
            }
        case RateResultIR(analysis=analysis, events=events):
            return {"analysis": normalize(analysis), "events": normalize(events)}
        case RateRatioIR(events=events, level=level):
            return {"events": normalize(events), "level": str(level)}
        case ProportionIR(measure=measure, model=model, cases=cases, level=level, group=group):
            return {
                "measure": measure,
                "model": normalize(model),
                "cases": cases,
                "level": str(level),
                **({"group": group} if group else {}),
            }
        case MatchedStudyIR(pairs=pairs, exposure=exposure, outcome=outcome):
            return {
                "study": "matched_case_control",
                "pairs": pairs,
                "exposure": exposure,
                "outcome": outcome,
                **_study_extras(value),
            }
        case MatchedAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "mcnemar",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
        case MatchedPairsIR(model=model):
            return {"model": normalize(model), **dict(zip(PAIR_CELLS, value.cells, strict=True))}
        case MatchedResultIR(analysis=analysis, observed=observed):
            return {"analysis": normalize(analysis), "pairs": normalize(observed)}
        case MatchedIntervalIR(observed=observed, level=level):
            return {"pairs": normalize(observed), "level": str(level)}
        case AssociationTableIR(model=model):
            return {"model": normalize(model), **dict(zip(CELLS, value.cells, strict=True))}
        case AssociationResultIR(analysis=analysis, table=table):
            return {"analysis": normalize(analysis), "table": normalize(table)}
        case EffectIntervalIR(measure=measure, table=table, level=level):
            return {"measure": measure, "table": normalize(table), "level": str(level)}
        case AssociationNullIR(model=model, predicate=predicate):
            return {"predicate": predicate, "model": normalize(model)}
        case CitedAssociationIR(plan=plan, hypothesis=hypothesis, alpha=alpha, method=method):
            return {
                "test": method.key,
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
                **({"adjusted_for": list(value.covariates)} if value.covariates else {}),
            }
        case AssociationAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha):
            return {
                "test": "fisher_exact",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
        case RandomisationAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha, draws=draws):
            result = {
                "test": "randomisation",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
            if draws is not None:
                result["draws"] = draws
            return result
        case CitedAnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha, method=method):
            result = {
                "test": method.key,
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
            if method.grade == "declared":
                # A declared test is described by the file, not by the registry.
                result.update(
                    method=method.title, scope=method.scope, references=list(method.references)
                )
            return result
        case PlanIR(model=model, stopping=stopping):
            return {"model": normalize(model), "stopping": stopping}
        case HypothesisIR(model=model, predicate=predicate, value=bound):
            result = {"predicate": predicate, "model": normalize(model)}
            if predicate != "equal_proportions":
                result["value"] = str(bound)
            return result
        case PearsonAnalysisIR(plan, hypothesis, alpha, cutoff, correction):
            return {
                "test": value.test,
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
                "squared_cutoff": str(cutoff),
                "correction": correction,
            }
        case (
            ProportionZAnalysisIR(plan, hypothesis, alpha, cutoff)
            | AsymptoticMcNemarAnalysisIR(plan, hypothesis, alpha, cutoff)
            | FarringtonManningAnalysisIR(plan, hypothesis, alpha, cutoff)
        ):
            return {
                "test": value.test,
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
                "squared_cutoff": str(cutoff),
            }
        case AnalysisIR(plan=plan, hypothesis=hypothesis, alpha=alpha, alternative=alternative):
            result = {
                "test": "fisher",
                "design": normalize(plan),
                "null": normalize(hypothesis),
                "alpha": str(alpha),
            }
            if alternative != "two_sided":
                result["alternative"] = alternative
            return result
        case ComposedFamilyIR(
            analyses=analyses, alpha=alpha, mode=mode, weights=weights, transitions=transitions
        ):
            result = {
                "method": MODES[mode].method,
                "composition": "conditional",
                "alpha": str(alpha),
                "analyses": [
                    {"name": name, "analysis": normalize(analysis)} for name, analysis in analyses
                ],
            }
            if mode == "graphical":
                result["weights"] = [str(weight) for weight in weights]
                result["transitions"] = [[str(share) for share in row] for row in transitions]
            if mode == "spending":
                # Only group_sequential(...) builds this mode, as a design with looks.
                assert isinstance(value, SequentialIR)
                result["spending"] = value.spending
            return result
        case FamilyIR(analyses=analyses, alpha=alpha, joint_law=law):
            return {
                "method": "bonferroni",
                "alpha": str(alpha),
                "joint_law": law,
                "analyses": [
                    {"name": name, "analysis": normalize(analysis)} for name, analysis in analyses
                ],
            }
        case ObservationIR(
            analysis=analysis, control_successes=control, treatment_successes=treatment
        ):
            return {
                "analysis": normalize(analysis),
                "control_successes": control,
                "treatment_successes": treatment,
            }
        case RatesIR(p_control=control, p_treatment=treatment, icc=icc):
            point: dict[str, object] = {"p_control": str(control), "p_treatment": str(treatment)}
            point = point if icc is None else {**point, "icc": str(icc)}
            return _with_cluster_cv(point, value)
        case RateIR(value=rate):
            return {"response_rate": str(rate)}
        case RisksIR(unexposed=unexposed, exposed=exposed, exposed_share=share):
            point = {"risk_unexposed": str(unexposed), "risk_exposed": str(exposed)}
            return point if share is None else {**point, "exposed_share": str(share)}
        case OutcomePrevalenceIR(unexposed=unexposed, exposed=exposed, exposed_share=share):
            point = {
                "prevalence_unexposed": str(unexposed),
                "prevalence_exposed": str(exposed),
                "exposed_share": str(share),
            }
            return _with_design_effect(point, value)
        case TotalCandidatesIR(analysis=analysis, min_n=low, max_n=high):
            return {"analysis": normalize(analysis), "min_n": low, "max_n": high}
        case ExposurePrevalenceIR(controls=controls, cases=cases):
            return {"exposure_controls": str(controls), "exposure_cases": str(cases)}
        case DiscordantPairsIR(share=share, odds_ratio=ratio):
            return {"discordant": str(share), "odds_ratio": str(ratio)}
        case IncidenceRatesIR(rate_ratio=ratio, exposed_time=exposed, unexposed_time=unexposed):
            point = {
                "rate_ratio": str(ratio),
                "exposed_time": str(exposed),
                "unexposed_time": str(unexposed),
            }
            return point if value.events is None else {**point, "events": value.events}
        case CountCandidatesIR(analysis=analysis, min_size=low, max_size=high):
            unit = value.unit
            return {"analysis": normalize(analysis), f"min_{unit}": low, f"max_{unit}": high}
        case GroupCandidatesIR(analysis=analysis, min_size=low, max_size=high, ratio=ratio):
            study = analysis.plan.model
            # Fisher's test of association and the cited observational tests take a study.
            assert isinstance(study, ObservationalStudyIR)
            low_key, high_key, ratio_key = GROUP_SEARCH_KEYS[study.design]
            return {"analysis": normalize(analysis), low_key: low, high_key: high, ratio_key: ratio}
        case MeanDifferenceIR(value=difference, sd=sd, icc=icc):
            point = {"mean_difference": str(difference), "sd": str(sd)}
            point = point if icc is None else {**point, "icc": str(icc)}
            return _with_cluster_cv(point, value)
        case HazardRatioIR(value=ratio, events=events):
            return {"hazard_ratio": str(ratio), "events": events}
        case CorrelationIR(value=rho):
            return _with_cluster_cv({"correlation": str(rho)}, value)
        case OutcomeMeansIR(unexposed=unexposed, exposed=exposed, sd=sd, exposed_share=share):
            point = {"mean_unexposed": str(unexposed), "mean_exposed": str(exposed), "sd": str(sd)}
            point = point if share is None else {**point, "exposed_share": str(share)}
            return _with_design_effect(point, value)
        case OddsPerSdIR(odds_ratio=ratio, baseline=baseline, exposure_r2=share):
            point = {"odds_ratio_per_sd": str(ratio), "baseline": str(baseline)}
            point = point if share is None else {**point, "exposure_r2": str(share)}
            return _with_design_effect(point, value)
        case SlopeIR(value=slope, exposure_sd=exposure, residual_sd=residual):
            point = {
                "slope": str(slope),
                "exposure_sd": str(exposure),
                "residual_sd": str(residual),
            }
            if value.exposure_r2 is not None:
                point["exposure_r2"] = str(value.exposure_r2)
            return _with_cluster_cv(_with_design_effect(point, value), value)
        case ExponentialSurvivalIR(hazard_ratio=ratio, control_median=median):
            point = {
                "hazard_ratio": str(ratio),
                "control_median": str(median),
                "accrual": str(value.accrual),
                "follow_up": str(value.follow_up),
            }
            if value.dropout is not None:
                point.update(dropout=str(value.dropout), dropout_time=str(value.dropout_time))
            if value.effect_delay is not None:
                point["effect_delay"] = str(value.effect_delay)
            return point
        case SingleProportionIR(value=rate):
            point = {"proportion": str(rate)}
            if value.population_size is not None:
                point["population_size"] = value.population_size
            return _with_design_effect(point, value)
        case PrecisionTargetIR(at=at, level=level):
            result = {"at": normalize(at), "level": str(level)}
            if value.margin is not None:
                result["margin_of_error"] = str(value.margin)
            else:
                result["relative_margin_of_error"] = str(value.relative)
            if value.assurance is not None:
                result["assurance"] = str(value.assurance)
            return result
        case PlannedIntervalIR(model=model, measure=measure, method=method, group=group):
            result = {"interval": measure, "model": normalize(model), "method": method}
            return result if group is None else {**result, "group": group}
        case IntervalCandidatesIR(interval=interval, min_size=low, max_size=high, ratio=ratio):
            return {
                "interval": normalize(interval),
                "min_size": low,
                "max_size": high,
                "ratio": ratio,
            }
        case PowerTargetIR(at=at, minimum=minimum, maximum_typeI=maximum):
            target = {
                "at": normalize(at),
                "minimum_power": str(minimum),
                "maximum_typeI": str(maximum),
            }
            if value.nulls is not None:
                target["nulls"] = [normalize(null) for null in value.nulls.points]
            if value.rejecting is not None:
                target["rejecting"] = value.rejecting
            return target
        case EndpointPointsIR(points=points, correlation=correlation):
            return {
                "endpoints": [normalize(point) for point in points],
                "correlation": str(correlation),
            }
        case NullScenariosIR(points=points):
            return {"null_scenarios": [normalize(point) for point in points]}
        case ReestimationIR(analysis=analysis):
            return {
                "rule": "blinded_reestimation",
                "analysis": normalize(analysis),
                "interim_per_arm": value.interim_per_arm,
                "max_per_arm": value.max_per_arm,
                "difference": str(value.difference),
                "power": str(value.power),
            }
        case TwoStageModelIR(n_stage1=first, n_stage2=second):
            return {"module": "two_stage_binomial", "n_stage1": first, "n_stage2": second}
        case PriorIR(a=a, b=b):
            return {"distribution": "beta", "a": a, "b": b}
        case RuleIR(rule=rule):
            return rule.to_dict()
        case TwoStageAnalysisIR(design=design, rule=rule, null_rate=rate):
            return {
                "test": "two_stage",
                "design": normalize(design),
                "rule": normalize(rule),
                "null_rate": str(rate),
            }
        case OneArmModelIR(n=n):
            return {"module": "one_arm_binomial", "n": n}
        case OneSampleScoreAnalysisIR(model, rate, alpha, cutoff):
            return {
                "test": "binomial_score_test",
                "model": normalize(model),
                "null_rate": str(rate),
                "alpha": str(alpha),
                "squared_cutoff": str(cutoff),
            }
        case OneSampleAnalysisIR(model=model, null_rate=rate, alpha=alpha):
            return {
                "test": "binomial_exact_one_sided",
                "model": normalize(model),
                "null_rate": str(rate),
                "alpha": str(alpha),
            }
        case TwoStageObservationIR(
            analysis=analysis, stage1_responses=first, stage2_responses=second
        ):
            return {
                "analysis": normalize(analysis),
                "stage1_responses": first,
                "stage2_responses": second,
            }
        case OneSampleObservationIR(analysis=analysis, responses=responses):
            return {"analysis": normalize(analysis), "responses": responses}
        case DifferenceIntervalIR(
            model=model, control_successes=control, treatment_successes=treatment, level=level
        ):
            return {
                "model": normalize(model),
                "control_successes": control,
                "treatment_successes": treatment,
                "level": str(level),
            }
        case IntervalIR(model=model, responses=responses, level=level):
            return {"model": normalize(model), "responses": responses, "level": str(level)}
        case TwoStageCandidatesIR(null_rate=rate, max_total=total, criterion=criterion):
            return {
                "design": "two_stage_threshold",
                "null_rate": str(rate),
                "max_total": total,
                "criterion": criterion,
            }
        case LookCandidatesIR(
            design=design, min_per_arm=low, max_per_arm=high, step=step, criterion=criterion
        ):
            return {
                "analysis": normalize(design),
                "min_per_arm": low,
                "max_per_arm": high,
                "step": step,
                "criterion": criterion,
            }
        case OneArmCandidatesIR(analysis=analysis, min_n=low, max_n=high):
            return {"analysis": normalize(analysis), "min_n": low, "max_n": high}
        case FeasibilityIR(analysis=analysis, target=target):
            return {"analysis": normalize(analysis), "target": normalize(target)}
        case ClusterCandidatesIR(analysis=analysis, low=low, high=high, cluster_size=size):
            if value.varies == "clusters":
                return {
                    "analysis": normalize(analysis),
                    "cluster_size": size,
                    "min_clusters_per_arm": low,
                    "max_clusters_per_arm": high,
                }
            return {
                "analysis": normalize(analysis),
                "min_cluster_size": low,
                "max_cluster_size": high,
            }
        case CandidatesIR(analysis=analysis, min_per_arm=low, max_per_arm=high, ratio=ratio):
            return {
                "analysis": normalize(analysis),
                "allocation": "equal_arms" if ratio == 1 else f"1:{ratio}",
                "min_per_arm": low,
                "max_per_arm": high,
            }
        case SizingIR(candidates=candidates, target=target, minimal=minimal):
            return {
                "candidates": normalize(candidates),
                "target": normalize(target),
                "claim": "smallest_in_range" if minimal else "sufficient",
            }
        case ClaimIR(kind=kind, subject=subject, name=name):
            return {"kind": kind, "subject_name": name, "subject": normalize(subject)}
        case VerificationResultIR(request_id=index) | CalculationResultIR(request_id=index):
            return {"request_id": index}
        case FieldIR(subject=subject, name=name, value_type=value_type):
            return {"field": name, "subject": normalize(subject), "value_type": value_type.label}
        case tuple():
            return [normalize(item.value) for item in value]
        case _:
            return value
