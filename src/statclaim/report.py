"""Combine exact numerical results with explicit formal-verification status."""

from fractions import Fraction
from pathlib import Path

from statclaim.composition import composition_claims
from statclaim.design import Design, inspect_design
from statclaim.family import FisherFamily, inspect_family
from statclaim.fisher import FisherResult, fisher_exact
from statclaim.planning import (
    DIFFERENCE_ASSUMPTIONS,
    INTERVAL_ASSUMPTIONS,
    RESULT_ASSUMPTIONS,
    BinomialInterval,
    DifferenceInterval,
    MarginTest,
    OneSamplePlan,
    OneSampleResult,
    PowerPlan,
    TwoStagePlan,
    TwoStageResult,
    margin_assumptions,
    search_equal_arms,
    search_one_sample,
    search_two_stage,
    stage_result_assumptions,
)
from statclaim.verification import NEEDS_LEAN

DESIGN_ASSUMPTIONS = [
    "The samples follow two independent binomial distributions.",
    "Positive arm sizes were fixed before outcomes were observed.",
    "The error bound is under the null of equal success probabilities, for every p in [0, 1].",
]


def test_design(design: Design, *, control_successes: int, treatment_successes: int) -> dict:
    result = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
        alpha=design.alpha,
        alternative=design.alternative,
    )
    return _result_report(design, result)


def _result_report(design: Design, result: FisherResult) -> dict:
    report = inspect_design(design)
    report["verification_scope"] = "result"
    report["formal_reference"].update(
        theorem="StatClaim.fisher_typeI_error_le_alpha",
        application_to_this_run="unresolved_implementation_correspondence",
    )
    report["outstanding_obligations"] = [
        "Check the exact p-value, table probability, and decision against the Lean definition.",
        "Bind the result and model guarantee to checked artifacts and the exact inputs.",
        *[item for item in report["outstanding_obligations"] if "Data-dependent" in item],
    ]
    report["calculation"] = result.to_dict()
    report["evidence"] = [
        {
            "kind": "exact_computation",
            "scope": "Conditional table probabilities, two-sided p-value, and threshold comparison",
            "implementation": "Python integer combinatorics and fractions.Fraction",
            "formally_verified_implementation": False,
        }
    ]
    if design.stopping == "fixed":
        report["decision"] = "reject_null" if result.reject_null else "do_not_reject_null"
        report["decision_scope"] = (
            "Decision of the specified fixed-sample test under the listed sampling assumptions. "
            "This is an exact computation, not a Lean verification certificate."
        )
    else:
        report["decision"] = None
        report["decision_scope"] = (
            "The fixed-margin p-value and its threshold comparison were computed, but no "
            "decision is endorsed for the data-dependent stopping procedure. "
            "Its Type I error guarantee needs separate justification."
        )
    return report


def _from_program(report: dict) -> dict | None:
    """The report with the evidence of the program certificate `check` built for this run,
    when it covers the request being run; otherwise None. See program_evidence.py."""
    from statclaim.program_evidence import attach

    return attach(report)


def verify_design(
    design: Design,
    *,
    control_successes: int,
    treatment_successes: int,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> dict:
    result = fisher_exact(
        n_control=design.n_control,
        n_treatment=design.n_treatment,
        control_successes=control_successes,
        treatment_successes=treatment_successes,
        alpha=design.alpha,
        alternative=design.alternative,
    )
    report = _result_report(design, result)
    if design.stopping != "fixed":
        report["verification"] = {
            "stage": "sampling_scope",
            "message": (
                "Data-dependent stopping needs a separate justification; no certificate issued."
            ),
        }
        return report
    return _certified(report)


def verify_design_only(
    design: Design,
    *,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> dict:
    """Check a pre-data design guarantee; no numerical calculation is performed."""
    report = inspect_design(design)
    report["verification_scope"] = "design"
    if design.alternative == "two_sided":
        report["required_assumptions"] = list(DESIGN_ASSUMPTIONS)
    report["formal_reference"]["theorem"] = "StatClaim.Modules.Fisher.typeI_statement"
    report["formal_reference"]["application_to_this_run"] = "unresolved_design_verification"
    report["outstanding_obligations"] = [
        "Instantiate the declared analysis, discharge sampling compatibility, "
        "and check the uniform Type I error bound in Lean.",
    ]
    if design.stopping != "fixed":
        report["outstanding_obligations"] = [
            "Specify and justify the sampling law induced by data-dependent stopping.",
            "Establish compatibility or provide a suitable replacement error-bound theorem.",
        ]
        report["verification"] = {
            "stage": "sampling_scope",
            "message": "Data-dependent stopping needs separate justification. "
            "The fixed-sample theorem does not establish its guarantee; "
            "this is not evidence of inflated error.",
        }
        return report
    return _certified(report)


def verify_family(
    family: FisherFamily, *, project: Path, output: Path | None = None, timeout: float = 120
) -> dict:
    report = inspect_family(family)
    if not family.supported or family.allocated_alpha > family.alpha:
        report["verification"] = {
            "stage": "allocation" if family.supported else "sampling_scope",
            "message": "The allocated alpha exceeds the requested familywise bound."
            if family.supported
            else "Data-dependent stopping needs separate justification; "
            "this is not evidence of inflated error.",
        }
        return report
    return _certified(report)


def planning_report(scope: str, target_property: str, assumptions: list[str]) -> dict:
    """A planning request before execution. This never issues a certificate."""
    return {
        "schema_version": 1,
        "status": "unresolved_obligation",
        "verification_scope": scope,
        "certificate_issued": False,
        "backend_invoked": False,
        "target_property": target_property,
        "required_assumptions": list(assumptions),
        "established_properties": [],
        "evidence": [],
        "calculation": None,
        "decision": None,
    }


def run_composition(report: dict, composition, *, project: Path, output, timeout: float) -> dict:
    """How the members' levels combine, proved in Lean with the program: outright when Lean
    proves every member, otherwise conditional on the members' premises."""
    report["combination_words"] = composition_claims(composition)
    return _certified(report)


def _approx(record: dict) -> str:
    return f"approximately {record['decimal_approximation']}"


def _unmet(report: dict, stage: str, code: str, message: str) -> dict:
    report["verification"] = {"stage": stage, "code": code, "message": message}
    return report


def _certified(report: dict) -> dict:
    """The claim's evidence from the program certificate `check` built for this run, or
    why it has none: no Lean here, or a claim the program's Lean build did not prove."""
    attached = _from_program(report)
    if attached is not None:
        return attached
    from statclaim.program_evidence import CURRENT

    if CURRENT.get() is None:
        report["verification"] = {"stage": "project", "message": NEEDS_LEAN}
    else:
        report["backend_invoked"] = True
        report["verification"] = {
            "stage": "semantics",
            "message": "Lean's build of the program did not prove this claim, so it has no proof.",
        }
    return report


def run_power_plan(
    report: dict, plan: PowerPlan, *, verify: bool, project: Path, output, timeout: float
) -> dict:
    """Assess a fixed Fisher design; verify certifies only when every component is met."""
    calculation = plan.evaluate()
    report["calculation"] = calculation
    met = calculation["power_target_met"] and calculation["typeI_target_met"]
    report["decision"] = "target_met" if met else "target_not_met"
    report["components"] = {
        "typeI": "supported_by_theorem" if calculation["typeI_target_met"] else "not_established",
        "power": "met" if calculation["power_target_met"] else "not_met",
    }
    if not verify:
        return report
    if not calculation["typeI_target_met"]:
        return _unmet(
            report,
            "typeI_target",
            "typeI_target_not_established",
            f"The analysis's alpha {plan.design.alpha} exceeds the requested Type I bound "
            f"{plan.maximum_typeI}. The Fisher theorem bounds error by alpha only; "
            "this is not evidence that the actual error exceeds the request.",
        )
    if not calculation["power_target_met"]:
        return _unmet(
            report,
            "power_target",
            "power_target_not_met",
            f"Calculated power, {_approx(calculation['power'])}, is below the required "
            f"{plan.minimum_power} at the planning point. No evidence is issued for the "
            "combined planning claim. The Type I component is supported separately by the "
            "Fisher theorem. This says nothing about whether the null is true.",
        )
    return _certified(report)


def run_sample_size(
    report: dict,
    alpha,
    target: tuple,
    bounds: tuple[int, int],
    *,
    minimal: bool = False,
    ratio: int = 1,
    alternative: str = "two_sided",
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for a sufficient design with the given allocation ratio."""
    p_control, p_treatment, minimum, maximum = target
    plan, evaluated = search_equal_arms(
        alpha, p_control, p_treatment, minimum, maximum, *bounds, minimal, ratio, alternative
    )
    search = {
        "min_per_arm": bounds[0],
        "max_per_arm": bounds[1],
        "candidates_evaluated": evaluated,
        "minimum_sample_size_claim": "requested" if minimal else "not_requested",
    }
    if plan is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No candidate with {bounds[0]} to {bounds[1]} controls meets the power target. "
                "Nothing is claimed about other designs or larger samples.",
            )
        return report
    report = run_power_plan(
        report, plan, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {**report["calculation"], **search}
    return report


def run_association_plan(
    report: dict, plan, *, verify: bool, project: Path, output, timeout: float
) -> dict:
    """Exact power of an observational test: Fisher's test of association, McNemar's test or
    the rate test. verify certifies only when every component is met."""
    from statclaim.association import NOT_CAUSAL

    calculation = plan.evaluate()
    report["calculation"] = calculation
    report["limitations"] = [NOT_CAUSAL]
    met = calculation["power_target_met"] and calculation["typeI_target_met"]
    report["decision"] = "target_met" if met else "target_not_met"
    report["components"] = {
        "typeI": "supported_by_theorem" if calculation["typeI_target_met"] else "not_established",
        "power": "met" if calculation["power_target_met"] else "not_met",
    }
    if not verify:
        return report
    if not calculation["typeI_target_met"]:
        return _unmet(
            report,
            "typeI_target",
            "typeI_target_not_established",
            f"The analysis's alpha {plan.test.alpha} exceeds the requested Type I bound "
            f"{plan.maximum_typeI}. The theorem bounds error by alpha only; this is not "
            "evidence that the actual error exceeds the request.",
        )
    if not calculation["power_target_met"]:
        return _unmet(
            report,
            "power_target",
            "power_target_not_met",
            f"Calculated power, {_approx(calculation['power'])}, is below the required "
            f"{plan.minimum_power} at the planning point. No evidence is issued for the "
            "combined planning claim. The Type I component is supported separately by the "
            "theorem. This says nothing about whether there is an association.",
        )
    report = _certified(report)
    report["limitations"] = [NOT_CAUSAL]
    return report


def run_association_search(
    report: dict,
    test,
    target: tuple[Fraction, Fraction, Fraction, Fraction],
    bounds: tuple[int, int],
    *,
    minimal: bool,
    ratio: int,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for the smallest group size, keeping the ratio between the groups."""
    from statclaim.observational_planning import GROUPS, search_groups

    found, evaluated = search_groups(test, *target, *bounds, minimal, ratio)
    second = GROUPS[test.design][1]
    search = {
        f"min_{second}": bounds[0],
        f"max_{second}": bounds[1],
        "candidates_evaluated": evaluated,
        "minimum_sample_size_claim": "requested" if minimal else "not_requested",
    }
    if found is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No candidate with {bounds[0]} to {bounds[1]} {second} meets the power target. "
                "Nothing is claimed about other designs or larger samples.",
            )
        return report
    report = run_association_plan(
        report, found, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {**report["calculation"], **search}
    return report


def run_total_search(
    report: dict,
    plan,
    bounds: tuple[int, int],
    *,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for a sufficient total when the design fixes only its total."""
    from statclaim.observational_planning import search_totals

    found, evaluated = search_totals(plan, *bounds)
    search = {
        "min_n": bounds[0],
        "max_n": bounds[1],
        "candidates_evaluated": evaluated,
        "minimum_sample_size_claim": "not_requested",
    }
    if found is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No total from {bounds[0]} to {bounds[1]} meets the power target. Nothing is "
                "claimed about other designs or larger samples.",
            )
        return report
    report = run_association_plan(
        report, found, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {**report["calculation"], **search}
    return report


def run_count_search(
    report: dict,
    plan,
    bounds: tuple[int, int],
    *,
    minimal: bool,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for the fewest pairs of a matched study, or events for the rate test."""
    from statclaim.observational_planning import MatchedPowerPlan, search_events, search_pairs

    matched = isinstance(plan, MatchedPowerPlan)
    unit = "pairs" if matched else "events"
    found, evaluated = (search_pairs if matched else search_events)(plan, *bounds, minimal)
    search = {
        f"min_{unit}": bounds[0],
        f"max_{unit}": bounds[1],
        "candidates_evaluated": evaluated,
        "minimum_sample_size_claim": "requested" if minimal else "not_requested",
    }
    if found is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No candidate with {bounds[0]} to {bounds[1]} {unit} meets the power target. "
                "Nothing is claimed about other designs or larger samples.",
            )
        return report
    report = run_association_plan(
        report, found, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {**report["calculation"], **search}
    return report


def run_policy_plan(
    report: dict,
    plan: TwoStagePlan | OneSamplePlan,
    *,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Assess a single-arm design at its declared null and alternative rates."""
    calculation = plan.evaluate()
    report["calculation"] = calculation
    met = calculation["power_target_met"] and calculation["typeI_target_met"]
    report["decision"] = "target_met" if met else "target_not_met"
    report["components"] = {
        "typeI": "met" if calculation["typeI_target_met"] else "not_met",
        "power": "met" if calculation["power_target_met"] else "not_met",
    }
    if not verify:
        return report
    if not calculation["typeI_target_met"]:
        return _unmet(
            report,
            "typeI_target",
            "typeI_target_not_met",
            f"The calculated rejection probability at the null rate, "
            f"{_approx(calculation['typeI'])}, exceeds the requested {plan.maximum_typeI}. "
            "No evidence is issued.",
        )
    if not calculation["power_target_met"]:
        return _unmet(
            report,
            "power_target",
            "power_target_not_met",
            f"Calculated power, {_approx(calculation['power'])}, is below the required "
            f"{plan.minimum_power} at the alternative rate. No evidence is issued for the "
            "combined planning claim.",
        )
    return _certified(report)


def run_one_sample_search(
    report: dict,
    template: OneSamplePlan,
    bounds: tuple[int, int],
    *,
    minimal: bool = False,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for a sufficient one-sample size."""
    plan, evaluated = search_one_sample(template, *bounds, minimal)
    search = {
        "min_n": bounds[0],
        "max_n": bounds[1],
        "candidates_evaluated": evaluated,
        "minimum_sample_size_claim": "requested" if minimal else "not_requested",
    }
    if plan is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No sample size from {bounds[0]} to {bounds[1]} meets the targets. "
                "Nothing is claimed about other designs or larger samples.",
            )
        return report
    report = run_policy_plan(
        report, plan, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {**report["calculation"], **search}
    return report


def run_binomial_result(
    result: OneSampleResult, *, verify: bool, project: Path, output, timeout: float
) -> dict:
    """Calculate, and optionally certify, an observed one-sample result."""
    report = planning_report(
        "result",
        f"Exact one-sided p-value and decision for {result.responses} responses out of "
        f"{result.n} at alpha {result.alpha}."
        + (" Also check the test's Type I bound." if verify else " Calculate only."),
        RESULT_ASSUMPTIONS,
    )
    report["calculation"] = result.evaluate()
    report["decision"] = "reject_null" if result.reject_null else "do_not_reject_null"
    if not verify:
        return report
    return _certified(report)


def interval_report(interval: "BinomialInterval | DifferenceInterval", *, verify: bool) -> dict:
    if isinstance(interval, DifferenceInterval):
        return planning_report(
            "interval",
            f"Interval at level {interval.level} for p_treatment - p_control, from "
            f"{interval.control_successes} of {interval.n_control} control and "
            f"{interval.treatment_successes} of {interval.n_treatment} treatment successes"
            + (", with joint coverage for every pair of rates." if verify else ". Calculate only."),
            DIFFERENCE_ASSUMPTIONS,
        )
    return planning_report(
        "interval",
        f"Exact confidence interval at level {interval.level} for {interval.responses} "
        f"responses out of {interval.n}"
        + (", with coverage for every true rate." if verify else ". Calculate only."),
        INTERVAL_ASSUMPTIONS,
    )


def run_interval(
    interval: "BinomialInterval | DifferenceInterval",
    *,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Calculate, and optionally certify, an exact confidence interval."""
    report = interval_report(interval, verify=verify)
    report["calculation"] = interval.evaluate()
    report["decision"] = "interval_reported"
    if not verify:
        return report
    return _certified(report)


def run_two_stage_search(
    report: dict,
    null_rate,
    target: tuple,
    max_total: int,
    criterion: str,
    *,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search two-stage designs; the selected design is certified, the ranking is not."""
    alternative, minimum, maximum = target
    plan, evaluated = search_two_stage(
        null_rate, alternative, minimum, maximum, max_total, criterion
    )
    search = {
        "criterion": criterion,
        "max_total": max_total,
        "candidates_evaluated": evaluated,
        "ranking": "calculated_not_certified",
    }
    if plan is None:
        report["calculation"] = {**search, "power_target_met": False}
        report["decision"] = "no_feasible_candidate"
        if verify:
            _unmet(
                report,
                "search_exhausted",
                "no_feasible_candidate",
                f"No two-stage design with at most {max_total} participants meets the "
                "targets. Nothing is claimed about larger designs.",
            )
        return report
    report = run_policy_plan(
        report, plan, verify=verify, project=project, output=output, timeout=timeout
    )
    report["calculation"] = {
        **report["calculation"],
        "continue_above": plan.rule.continue_above,
        "reject_above": plan.rule.reject_above,
        **search,
    }
    return report


def stage_result_report(result: TwoStageResult, *, verify: bool) -> dict:
    counts = f"{result.first} responses in stage one"
    if result.second is not None:
        counts += f" and {result.second} in stage two"
    return planning_report(
        "result",
        f"Decision of the declared two-stage design for {counts}"
        + (", with the design's error bound." if verify else ". Calculate only."),
        stage_result_assumptions(result),
    )


def run_stage_result(
    result: TwoStageResult, *, verify: bool, project: Path, output, timeout: float
) -> dict:
    """Calculate, and optionally certify, the decision for observed two-stage counts."""
    report = stage_result_report(result, verify=verify)
    report["calculation"] = result.evaluate()
    report["decision"] = result.decision
    if not verify:
        return report
    return _certified(report)


def proportion_z_report(n: int, cutoff: Fraction, alpha: Fraction, *, pooled: bool) -> dict:
    test = "pooled score" if pooled else "unpooled Wald"
    return planning_report(
        "design",
        f"Two-sided {test} test with {n} per arm and squared cutoff {cutoff} "
        f"has Type I error at most {alpha} for every common null proportion.",
        [
            "The arm counts are independent binomial samples.",
            "The arm sizes and the cutoff are fixed before outcomes are observed.",
        ],
    )


def run_proportion_z(n: int, cutoff: Fraction, alpha: Fraction, *, pooled: bool) -> dict:
    from statclaim.wald import find_certificate

    report = _certified(proportion_z_report(n, cutoff, alpha, pooled=pooled))
    if (
        report.get("verification", {}).get("stage") == "proof"
        and find_certificate(n, cutoff, alpha, pooled=pooled) is None
    ):
        message = f"The interval check did not establish the requested ceiling {alpha}."
        if pooled:
            return _unmet(report, "typeI_target", "score_bound_unproved", message)
        return _unmet(report, "typeI_target", "wald_bound_unproved", message)
    return report


def margin_report(test: MarginTest, *, verify: bool) -> dict:
    null = f"p_treatment - p_control <= {test.margin}"
    text = (
        f"Exact difference test with arm sizes ({test.n_control}, {test.n_treatment}): "
        f"Type I error <= {test.maximum_typeI if test.has_target else test.alpha} whenever {null}"
    )
    if test.has_target:
        text += (
            f"; power >= {test.minimum_power} at p_control = {test.p_control}, "
            f"p_treatment = {test.p_treatment}"
        )
    if test.observed is not None:
        text += f"; decision for counts {test.observed}"
    report = planning_report("margin_test", text + ".", margin_assumptions(test))
    if not verify:
        report["target_property"] += " Calculate only."
    return report


def run_margin(test: MarginTest, *, verify: bool, project: Path, output, timeout: float) -> dict:
    """Assess an exact difference test; verify certifies only when every component is met."""
    report = margin_report(test, verify=verify)
    calculation = test.evaluate()
    report["calculation"] = calculation
    if test.observed is not None:
        report["decision"] = "reject_null" if test.reject_null else "do_not_reject_null"
    elif test.has_target:
        met = calculation["power_target_met"] and calculation["typeI_target_met"]
        report["decision"] = "target_met" if met else "target_not_met"
    else:
        report["decision"] = "design_described"
    if not verify:
        return report
    if test.has_target and not calculation["typeI_target_met"]:
        return _unmet(
            report,
            "typeI_target",
            "typeI_target_not_established",
            f"The analysis's alpha {test.alpha} exceeds the requested Type I bound "
            f"{test.maximum_typeI}. The test is built to have error at most alpha only.",
        )
    if test.has_target and not calculation["power_target_met"]:
        return _unmet(
            report,
            "power_target",
            "power_target_not_met",
            f"Calculated power, {_approx(calculation['power'])}, is below the required "
            f"{test.minimum_power} at the planning point. No evidence is issued for the "
            "combined planning claim.",
        )
    return _certified(report)


def run_margin_search(
    template: MarginTest,
    bounds: tuple[int, int],
    ratio: int,
    *,
    verify: bool,
    project: Path,
    output,
    timeout: float,
) -> dict:
    """Search ascending for a sufficient size; each candidate has its own critical value."""
    search = {"min_per_arm": bounds[0], "max_per_arm": bounds[1]}
    minimum = template.minimum_power
    if minimum is None:
        raise ValueError("A sample-size search needs a minimum power.")
    for evaluated, size in enumerate(range(bounds[0], bounds[1] + 1), 1):
        candidate = MarginTest(
            size,
            ratio * size,
            template.margin,
            template.alpha,
            template.p_control,
            template.p_treatment,
            template.minimum_power,
            template.maximum_typeI,
        )
        if candidate.power >= minimum:
            report = run_margin(
                candidate, verify=verify, project=project, output=output, timeout=timeout
            )
            report["calculation"] = {
                **report["calculation"],
                **search,
                "candidates_evaluated": evaluated,
            }
            return report
    report = margin_report(template, verify=verify)
    report["calculation"] = {
        **search,
        "candidates_evaluated": bounds[1] - bounds[0] + 1,
        "power_target_met": False,
    }
    report["decision"] = "no_feasible_candidate"
    if verify:
        _unmet(
            report,
            "search_exhausted",
            "no_feasible_candidate",
            f"No candidate with {bounds[0]} to {bounds[1]} controls meets the power target. "
            "Nothing is claimed about other designs or larger samples.",
        )
    return report


def randomisation_report(test, *, stopping: str = "fixed") -> dict:
    """A randomisation test's Type I claim before it is checked."""
    from statclaim.randomisation import NULL_STATEMENT, randomisation_assumptions

    report = planning_report(
        "randomisation_test",
        f"Randomisation test with {test.describe()}: Type I error <= {test.alpha} whenever "
        f"{NULL_STATEMENT}, for every statistic fixed in advance.",
        list(randomisation_assumptions(test)),
    )
    report["calculation"] = {
        "units": test.units,
        "treated_units": test.treated,
        "unit": test.unit,
        "splits": str(test.splits),
        **({"draws": test.draws} if test.draws else {}),
        "smallest_p_value": str(test.smallest_p_value),
        "alpha": str(test.alpha),
    }
    if stopping != "fixed":
        report["outstanding_obligations"] = [
            "Specify the randomisation and stopping procedure as one design; the test counts "
            "splits of a fixed set of units."
        ]
    return report


def run_randomisation(test, *, stopping: str, project: Path, output, timeout: float) -> dict:
    """Have Lean check the randomisation test's error bound for the declared assignment."""
    report = randomisation_report(test, stopping=stopping)
    if stopping != "fixed":
        return _unmet(
            report,
            "sampling_scope",
            "sampling_scope",
            "Data-dependent stopping changes which units are analysed, so the splits of a "
            "fixed set of units no longer describe the design. This is not evidence of "
            "inflated error.",
        )
    report = _certified(report)
    if report["status"] == "verified":
        report["limitations"] = [
            "The randomisation and who is analysed are declared by the file; how the p-value "
            "counts is assumed, as listed."
            if test.population
            else "Complete randomisation and analysis as randomised are assumed, as listed.",
            "The bound is under the sharp null only; it says nothing about equal means.",
        ]
    return report


def association_report(test, *, stopping: str = "fixed") -> dict:
    """Fisher's test of association in an observational study, before it is checked."""
    from statclaim.association import NOT_CAUSAL, association_assumptions, null_words

    report = planning_report(
        "association_test",
        f"Fisher's exact test of no association in {test.describe()}: Type I error <= "
        f"{test.alpha} whenever {null_words(test)}.",
        list(association_assumptions(test)),
    )
    sizes = {"group_sizes": list(test.groups)} if test.groups is not None else {"total": test.n}
    report["calculation"] = {"design": test.design, **sizes, "alpha": str(test.alpha)}
    report["limitations"] = [NOT_CAUSAL]
    if stopping != "fixed":
        report["outstanding_obligations"] = [
            "Specify the stopping procedure with its own guarantee; the test assumes the "
            "study's size was fixed in advance."
        ]
    return report


def run_association(test, *, stopping: str, project: Path, output, timeout: float) -> dict:
    """Have Lean check the test's error bound for the declared observational design."""
    from statclaim.association import NOT_CAUSAL

    report = association_report(test, stopping=stopping)
    if stopping != "fixed":
        return _unmet(
            report,
            "sampling_scope",
            "sampling_scope",
            "Data-dependent stopping changes the sampling law of the table. This is not "
            "evidence of inflated error.",
        )
    report = _certified(report)
    if report["status"] == "verified":
        report["limitations"] = [NOT_CAUSAL]
    return report


def association_result_report(result, *, verify: bool) -> dict:
    """Fisher's test for an observed table, before it is checked."""
    from statclaim.association import NOT_CAUSAL, result_assumptions

    report = planning_report(
        "result",
        f"Exact p-value and decision of Fisher's test of no association for the observed "
        f"table ({result.table.describe()}) at level {result.test.alpha}."
        + (" Also check the test's Type I bound." if verify else " Calculate only."),
        list(result_assumptions(result)),
    )
    report["limitations"] = [NOT_CAUSAL]
    return report


def run_association_result(
    result, *, verify: bool, stopping: str, project: Path, output, timeout: float
) -> dict:
    """Calculate the p-value and decision; with verify, Lean checks them and the bound."""
    from statclaim.association import NOT_CAUSAL

    report = association_result_report(result, verify=verify)
    report["calculation"] = result.evaluate()
    report["decision"] = "reject_null" if result.fisher.reject_null else "do_not_reject"
    if not verify:
        return report
    if stopping != "fixed":
        return _unmet(
            report,
            "sampling_scope",
            "sampling_scope",
            "Data-dependent stopping changes the sampling law of the table. This is not "
            "evidence of inflated error.",
        )
    report = _certified(report)
    report["limitations"] = [NOT_CAUSAL]
    return report


def effect_interval_report(interval, *, verify: bool) -> dict:
    """An interval for an effect measure, before it is checked."""
    from statclaim.association import MEASURES, NOT_CAUSAL, interval_assumptions

    report = planning_report(
        "interval",
        f"Interval at level {interval.level} for the {MEASURES[interval.measure][0]}, from the "
        f"observed table ({interval.table.describe()})"
        + (
            ", with joint coverage for every pair of probabilities."
            if verify
            else ". Calculate only."
        ),
        list(interval_assumptions(interval)),
    )
    report["limitations"] = [NOT_CAUSAL]
    return report


def run_effect_interval(interval, *, verify: bool, project: Path, output, timeout: float) -> dict:
    """Calculate, and optionally certify, an interval for an effect measure."""
    from statclaim.association import NOT_CAUSAL

    report = effect_interval_report(interval, verify=verify)
    report["calculation"] = interval.evaluate()
    report["decision"] = "interval_reported"
    if not verify:
        return report
    report = _certified(report)
    report["limitations"] = [NOT_CAUSAL]
    return report


def matched_report(subject, *, stopping: str = "fixed", verify: bool = True) -> dict:
    """A matched design's test, result or interval, before it is checked."""
    from statclaim import matched

    if isinstance(subject, matched.MatchedInterval):
        report = planning_report(
            "interval",
            f"Interval at level {subject.level} for the conditional odds ratio, from the "
            f"observed pairs ({subject.observed.describe()})"
            + (", with coverage for every probability." if verify else ". Calculate only."),
            list(matched.interval_assumptions(subject)),
        )
    elif isinstance(subject, matched.MatchedResult):
        report = planning_report(
            "result",
            f"Exact p-value and decision of McNemar's test for the observed pairs "
            f"({subject.observed.describe()}) at level {subject.test.alpha}."
            + (" Also check the test's Type I bound." if verify else " Calculate only."),
            list(matched.result_assumptions(subject)),
        )
    else:
        report = planning_report(
            "matched_test",
            f"McNemar's exact test of no association within {subject.pairs} matched pairs: "
            f"Type I error <= {subject.alpha} whenever {matched.null_words(subject)}.",
            list(matched.matched_assumptions(subject)),
        )
        if stopping != "fixed":
            report["outstanding_obligations"] = [
                "Specify the stopping procedure with its own guarantee; the test assumes the "
                "number of pairs was fixed in advance."
            ]
    from statclaim.association import NOT_CAUSAL

    report["limitations"] = [NOT_CAUSAL]
    return report


def run_matched(subject, *, verify: bool, stopping: str, project: Path, output, timeout: float):
    """Calculate a matched result or interval, and with verify have Lean check it."""
    from statclaim import matched
    from statclaim.association import NOT_CAUSAL

    report = matched_report(subject, stopping=stopping, verify=verify)
    if isinstance(subject, matched.MatchedResult):
        report["calculation"] = subject.evaluate()
        report["decision"] = "reject_null" if subject.reject_null else "do_not_reject"
    elif isinstance(subject, matched.MatchedInterval):
        report["calculation"] = subject.evaluate()
        report["decision"] = "interval_reported"
    if not verify:
        return report
    if stopping != "fixed":
        return _unmet(
            report,
            "sampling_scope",
            "sampling_scope",
            "Data-dependent stopping changes the law of the pairs. This is not evidence of "
            "inflated error.",
        )
    report = _certified(report)
    report["limitations"] = [NOT_CAUSAL]
    return report


def incidence_report(subject, *, stopping: str = "fixed", verify: bool = True) -> dict:
    """A proportion, rate test, rate result or rate ratio, before it is checked."""
    from statclaim import incidence
    from statclaim.association import NOT_CAUSAL

    calculate = "" if verify else " Calculate only."
    if isinstance(subject, incidence.ProportionEstimate):
        words = incidence.PROPORTIONS[subject.measure][0]
        report = planning_report(
            "interval",
            f"Exact interval at level {subject.level} for the {words} of {subject.outcome}, "
            f"from {subject.cases} cases among {subject.who()}.{calculate}",
            list(incidence.proportion_assumptions(subject)),
        )
        return report
    if isinstance(subject, incidence.RateRatioInterval):
        report = planning_report(
            "interval",
            f"Interval at level {subject.level} for the incidence rate ratio, from the observed "
            f"events ({subject.events.describe()}).{calculate}",
            list(incidence.rate_ratio_assumptions(subject)),
        )
    elif isinstance(subject, incidence.RateResult):
        report = planning_report(
            "result",
            f"Exact p-value and decision of the rate test for the observed events "
            f"({subject.events.describe()}) at level {subject.test.alpha}."
            + (" Also check the test's Type I bound." if verify else " Calculate only."),
            list(incidence.rate_result_assumptions(subject)),
        )
    else:
        report = planning_report(
            "rate_test",
            f"Exact test of equal incidence rates: Type I error <= {subject.alpha} whenever "
            f"{incidence.rate_null_words(subject)}, for any person-time.",
            list(incidence.rate_assumptions(subject)),
        )
        if stopping != "fixed":
            report["outstanding_obligations"] = [
                "Specify the stopping procedure with its own guarantee; the test assumes "
                "follow-up ends without regard to the events."
            ]
    report["limitations"] = [NOT_CAUSAL]
    return report


def run_incidence(subject, *, verify: bool, stopping: str, project: Path, output, timeout: float):
    """Calculate a proportion, rate result or rate ratio, and with verify have Lean check it."""
    from statclaim import incidence

    report = incidence_report(subject, stopping=stopping, verify=verify)
    if isinstance(subject, incidence.RateResult):
        report["calculation"] = subject.evaluate()
        report["decision"] = "reject_null" if subject.reject_null else "do_not_reject"
    elif not isinstance(subject, incidence.RateTest):
        report["calculation"] = subject.evaluate()
        report["decision"] = "interval_reported"
    if not verify:
        return report
    if stopping != "fixed":
        return _unmet(
            report,
            "sampling_scope",
            "sampling_scope",
            "Data-dependent stopping changes the law of the events. This is not evidence of "
            "inflated error.",
        )
    limitations = report.get("limitations")
    report = _certified(report)
    if limitations:
        report["limitations"] = limitations
    return report
