"""Reported values and kernel hints supplied to the semantics by the numerical backend."""

from dataclasses import replace
from fractions import Fraction
from pathlib import Path

from statclaim.incidence import tails_at
from statclaim.language import MatchedIntervalIR, MatchedResultIR, RateRatioIR, RateResultIR
from statclaim.language_runner import _run_request
from statclaim.lean_translation import data
from statclaim.matched import tails
from statclaim.observational_planning import binomial_region
from statclaim.planning import fisher_bounds, fisher_cuts, fisher_rejection_probability


def result_output(request, calculation: dict) -> dict:
    subject = request.claim.subject
    if "p_value" not in calculation:
        if "continued" in calculation:
            return {
                "continued": calculation["continued"],
                "reject_null": bool(calculation["reject_null"]),
                "typeI_bound": calculation["typeI_bound"]["fraction"],
            }
        return {"reject_null": calculation["reject_null"]}
    reported = {
        "p_value": calculation["p_value"]["fraction"],
        "reject_null": calculation.get("reject_null", calculation.get("p_value_le_alpha")),
    }
    if isinstance(subject, MatchedResultIR):
        observed = subject.lower().observed
        upper, lower = tails(observed.discordant, observed.case_exposed)
        reported.update(upper_tail=upper, lower_tail=lower)
    elif isinstance(subject, RateResultIR):
        events = subject.lower().events
        upper, lower, _ = tails_at(events.total, events.exposed_events, events.share)
        reported.update(upper_tail=upper, lower_tail=lower)
    elif "critical_value" in calculation:
        reported["critical_value"] = calculation["critical_value"]
    elif "table" not in calculation or subject.analysis.alternative != "greater":
        reported["observed_table_probability"] = calculation["observed_table_probability"][
            "fraction"
        ]
        if "control_success_support" in calculation:
            support = calculation["control_success_support"]
            reported.update(support_min=support["min"], support_max=support["max"])
    return reported


def interval_output(request, calculation: dict) -> dict:
    found = request.claim.subject.lower()
    reported = {
        key: calculation[key]["fraction"] if calculation[key] is not None else None
        for key in ("lower", "upper")
    }
    arms = getattr(found, "groups", found)
    if hasattr(arms, "control"):
        reported["tail"] = str(arms.control.tail_level)
        for name in ("control", "treatment"):
            arm = getattr(arms, name)
            reported[name] = [str(arm.lower), str(arm.upper)]
    else:
        arm = getattr(found, "binomial", found)
        reported["tail"] = str(arm.tail_level)
        if isinstance(request.claim.subject, (MatchedIntervalIR, RateRatioIR)):
            reported["arm"] = [str(arm.lower), str(arm.upper)]
    return reported


def plan_output(subject: dict, calculation: dict) -> dict:
    candidates = subject.get("candidates", {})
    analysis = subject.get("analysis", candidates.get("analysis", {}))
    if "n_stage1" in calculation:
        rule = analysis.get("rule") or {
            "kind": "threshold",
            "continue_above": calculation["continue_above"],
            "reject_above": calculation["reject_above"],
        }
        return {key: calculation[key] for key in ("n_stage1", "n_stage2")} | {"rule": rule}
    if "n_control" in calculation:
        return {key: calculation[key] for key in ("n_control", "n_treatment")}
    if "controls" in calculation:
        return {"n_control": calculation["controls"], "n_treatment": calculation["cases"]}
    if "unexposed" in calculation:
        return {"n_control": calculation["unexposed"], "n_treatment": calculation["exposed"]}
    if "critical_value" in calculation:
        return {key: calculation[key] for key in ("n", "critical_value")}
    for key in ("pairs", "events", "total_sample_size"):
        if key in calculation:
            return {"n": calculation[key]}
    raise data.Outside("The planning run did not report a supported design.")


def fisher_hint(nc: int, nt: int, alpha: Fraction, one_sided: bool = False) -> str:
    cuts, nexts = (fisher_bounds(nc, nt, alpha), ()) if one_sided else fisher_cuts(nc, nt, alpha)
    return f"⟨{list(cuts)}, {list(nexts)}⟩"


def pairs_hint(n: int, alpha: Fraction) -> str:
    lows, highs = zip(
        *(binomial_region(k, Fraction(1, 2), alpha) for k in range(n + 1)), strict=True
    )
    return f"⟨{list(lows)}, {list(highs)}⟩"


def plan_hint(subject: dict, output: dict) -> str | None:
    candidates = subject.get("candidates", {})
    analysis = subject.get("analysis", candidates.get("analysis", {}))
    point = subject["target"]["at"]
    method = analysis.get("test")
    minimal = subject.get("claim") == "smallest_in_range"
    if method == "fisher":
        nc, nt = output["n_control"], output["n_treatment"]
        alpha = Fraction(analysis["alpha"])
        one = data.one_sided(analysis)
        ratio = nt // nc
        first = candidates["min_per_arm"] if minimal else nc
        smaller = ", ".join(fisher_hint(n, ratio * n, alpha, one) for n in range(first, nc))
        return f"⟨{fisher_hint(nc, nt, alpha, one)}, [{smaller}]⟩"
    if method == "fisher_exact":
        alpha = Fraction(analysis["alpha"])
        if "n_control" in output:
            nc, nt = output["n_control"], output["n_treatment"]
            ratio = nc // nt
            first = candidates.get("min_cases", candidates.get("min_exposed")) if minimal else nt
            smaller = ", ".join(fisher_hint(ratio * n, n, alpha) for n in range(first, nt))
            return f"⟨{fisher_hint(nc, nt, alpha)}, [{smaller}]⟩"
        n = output["n"]
        if "risk_unexposed" in point:
            pc, pt = (Fraction(point[key]) for key in ("risk_unexposed", "risk_exposed"))
        else:
            pc, pt = (
                Fraction(point[key]) for key in ("prevalence_unexposed", "prevalence_exposed")
            )
        cuts, nexts = zip(*(fisher_cuts(n - k, k, alpha) for k in range(n + 1)), strict=True)
        parts = [
            int(
                fisher_rejection_probability(n - k, k, alpha, pc, pt)
                * pc.denominator ** (n - k)
                * pt.denominator**k
            )
            for k in range(n + 1)
        ]
        return f"⟨{[list(c) for c in cuts]}, {[list(c) for c in nexts]}, {parts}⟩"
    if method == "mcnemar":
        n, alpha = output["n"], Fraction(analysis["alpha"])
        first = candidates["min_pairs"] if minimal else n
        smaller = ", ".join(pairs_hint(k, alpha) for k in range(first, n))
        return f"⟨{pairs_hint(n, alpha)}, [{smaller}]⟩"
    if method == "rate_test":
        n, alpha = output["n"], Fraction(analysis["alpha"])
        exposed, unexposed = (Fraction(point[key]) for key in ("exposed_time", "unexposed_time"))
        share = exposed / (exposed + unexposed)
        low, high = binomial_region(n, share, alpha)
        first = candidates["min_events"] if minimal else n
        other = [binomial_region(k, share, alpha) for k in range(first, n)]
        return f"⟨{low}, {high}, ⟨{[x for x, _ in other]}, {[y for _, y in other]}⟩⟩"
    return None


def material(compiled, project: Path) -> tuple[list[dict | None], dict[int, str]]:
    """Use the same numerical path as the run to get the values that Lean will check."""
    reported = []
    hints = {}
    canonical = data.verify_claims(compiled.to_dict())
    requests = [request for request in compiled.requests if request.operation == "verify"]
    for index, (request, claim) in enumerate(zip(requests, canonical, strict=True)):
        kind, subject = claim["kind"], claim["subject"]
        output = None
        hint = None
        if kind == "typeI":
            hint = data.level_hint(subject)
        elif kind == "result" and data.fixed(subject):
            calculated = _run_request(
                replace(request, operation="calculate"), project, project, 120
            )
            output = result_output(request, calculated["calculation"])
            hint = data.level_hint(subject["analysis"])
        elif kind == "interval":
            calculated = _run_request(
                replace(request, operation="calculate"), project, project, 120
            )
            output = interval_output(request, calculated["calculation"])
        elif kind in {"meets", "sample_size"} and data.supported_plan(subject):
            calculated = _run_request(
                replace(request, operation="calculate"), project, project, 120
            )
            if calculated["decision"] == "target_met":
                output = plan_output(subject, calculated["calculation"])
                hint = plan_hint(subject, output)
        reported.append(output)
        if hint is not None:
            hints[index] = hint
    return reported, hints
