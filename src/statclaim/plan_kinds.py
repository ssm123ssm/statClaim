"""Every kind of analysis a planning claim can be about, and what each kind does.

A planning claim, meets(...) or a sample-size search, is about one analysis. The analysis's
kind decides five things: how calculate(...), verify(...) and simulate(...) are checked when
the claim is written, how the claim is described before it runs, how calculate(...) runs it,
how its derivation is built for the independent checker, and which record a calculation
publishes. Each kind lists all of them here, so a new kind of analysis is one new entry, not
a branch in each module.

Entries name their functions as "module:function", resolved on first use, so this table
imports nothing from the rest of StatClaim and every module can read it. The checker in
derivation_checker.py stays apart on purpose: it re-derives claims from their serialized
form, without this code.

Functions take:
    describe(subject, request) -> report             before running, for any operation
    calculate(report, subject, request, options)     runs calculate(...) or verify(...)
    derive(name, claim, analysis) -> Derivation      why the claim's contract holds
    check_calculate(claim) / check_simulate(analysis, subject, arguments, claim)
                                                     extra checks when the claim is written
"""

import importlib
from dataclasses import dataclass
from functools import cache

EXACT_SIMULATE = (
    "This analysis has exact power, so there is nothing to simulate. Use calculate(...) for the "
    "exact value, or verify(...) to prove it."
)
CITED_VERIFY = (
    "The power of a cited test is an approximate calculation, with no proof or cited theorem "
    "behind it, so it cannot be verified. Use calculate(...) instead."
)


@dataclass(frozen=True)
class PlanKind:
    name: str
    # The analysis's class, by name: the kind applies when any class in its MRO is named.
    classes: tuple[str, ...]
    describe: str
    derive: str
    details: str  # the record calculate(...) publishes, "module:Class"
    calculate: str | None = None  # None: calculate(...) is refused with refuse_calculate
    refuse_calculate: str = ""
    check_calculate: str | None = None
    refuse_verify: str | None = None  # None: verify(...) may prove the claim
    check_simulate: str | None = None  # None: simulate(...) is refused with refuse_simulate
    refuse_simulate: str = EXACT_SIMULATE
    when: str | None = None  # a further test of the analysis, when classes are not enough


KINDS = (
    PlanKind(
        "precision",
        ("PlannedIntervalIR",),
        describe="statclaim.language_inspection:describe_precision",
        derive="statclaim.derivations:derive_precision",
        details="statclaim.language_values:PrecisionDetails",
        calculate="statclaim.language_runner:calculate_precision",
        refuse_verify="A planned interval's precision is calculated, not proved: Lean does not "
        "check precision yet. Use calculate(...).",
        refuse_simulate="A planned interval's precision is summed exactly over the counts, so "
        "there is nothing to simulate. Use calculate(...).",
    ),
    PlanKind(
        "looks",
        ("SequentialIR",),
        describe="statclaim.language_inspection:describe_looks",
        derive="statclaim.derivations:derive_sequential_planning",
        details="statclaim.language_values:LooksPowerDetails",
        calculate="statclaim.language_runner:calculate_looks",
        check_calculate="statclaim.language:check_looks_calculation",
        refuse_verify="The power of a design with looks is calculated or simulated, not proved, "
        "so it cannot be verified. Use calculate(...) for Fisher's test, simulate(...) for "
        "t-tests.",
        check_simulate="statclaim.language:check_looks_simulation",
    ),
    PlanKind(
        "family",
        ("FamilyLikeIR",),
        describe="statclaim.language_inspection:describe_simulated_only",
        derive="statclaim.derivations:derive_family_planning",
        details="statclaim.language_values:PlanningDetails",
        refuse_calculate="A family's power has no formula. Use simulate(...), which runs every "
        "endpoint together.",
        refuse_verify=CITED_VERIFY,
        check_simulate="statclaim.language:check_family_simulation",
    ),
    PlanKind(
        "reestimation",
        ("ReestimationIR",),
        describe="statclaim.language_inspection:describe_simulated_only",
        derive="statclaim.derivations:derive_reestimation_planning",
        details="statclaim.language_values:PlanningDetails",
        refuse_calculate="A re-estimated design has no power formula and no proved Type I "
        "error. Use simulate(...), which judges both.",
        refuse_verify=CITED_VERIFY,
        check_simulate="statclaim.language:check_reestimation_simulation",
    ),
    PlanKind(
        "cited",
        ("CitedAnalysisIR",),
        describe="statclaim.language_inspection:describe_cited",
        derive="statclaim.derivations:derive_cited_planning",
        details="statclaim.language_values:ApproximatePowerDetails",
        calculate="statclaim.language_runner:calculate_cited",
        refuse_verify=CITED_VERIFY,
        check_simulate="statclaim.language:check_cited_simulation",
    ),
    PlanKind(
        "cited_association",
        ("CitedAssociationIR",),
        describe="statclaim.language_inspection:describe_cited_association",
        derive="statclaim.derivations:derive_cited_association_planning",
        details="statclaim.language_values:ApproximatePowerDetails",
        calculate="statclaim.language_runner:calculate_cited_association",
        refuse_verify=CITED_VERIFY,
        check_simulate="statclaim.language:check_association_simulation",
    ),
    PlanKind(
        "association",
        ("AssociationAnalysisIR",),
        describe="statclaim.language_inspection:describe_association",
        derive="statclaim.derivations:derive_association_planning",
        details="statclaim.language_values:AssociationPowerDetails",
        calculate="statclaim.language_runner:calculate_association",
    ),
    PlanKind(
        "matched",
        ("MatchedAnalysisIR",),
        describe="statclaim.language_inspection:describe_count",
        derive="statclaim.derivations:derive_association_planning",
        details="statclaim.language_values:MatchedPowerDetails",
        calculate="statclaim.language_runner:calculate_count",
    ),
    PlanKind(
        "rate",
        ("RateAnalysisIR",),
        describe="statclaim.language_inspection:describe_count",
        derive="statclaim.derivations:derive_association_planning",
        details="statclaim.language_values:RatePowerDetails",
        calculate="statclaim.language_runner:calculate_count",
    ),
    PlanKind(
        "margin",
        ("AnalysisIR",),
        when="statclaim.language:is_margin_test",
        describe="statclaim.language_inspection:describe_margin",
        derive="statclaim.derivations:derive_exact_planning",
        details="statclaim.language_values:MarginDetails",
        calculate="statclaim.language_runner:calculate_margin",
    ),
    PlanKind(
        "fisher",
        ("AnalysisIR",),
        describe="statclaim.language_inspection:describe_fisher",
        derive="statclaim.derivations:derive_exact_planning",
        details="statclaim.language_values:PlanningDetails",
        calculate="statclaim.language_runner:calculate_exact",
    ),
    PlanKind(
        "one_sample",
        ("OneSampleAnalysisIR",),
        describe="statclaim.language_inspection:describe_policy",
        derive="statclaim.derivations:derive_exact_planning",
        details="statclaim.language_values:OneSampleDetails",
        calculate="statclaim.language_runner:calculate_exact",
    ),
    PlanKind(
        "two_stage",
        ("TwoStageAnalysisIR",),
        describe="statclaim.language_inspection:describe_policy",
        derive="statclaim.derivations:derive_exact_planning",
        details="statclaim.language_values:PolicyDetails",
        calculate="statclaim.language_runner:calculate_exact",
    ),
)


@cache
def resolve(path: str):
    """The function or class a "module:name" path names."""
    module, name = path.split(":")
    return getattr(importlib.import_module(module), name)


def kind_of(analysis: object) -> PlanKind:
    """The first kind whose classes and further test match the analysis."""
    names = {cls.__name__ for cls in type(analysis).__mro__}
    for kind in KINDS:
        if names.intersection(kind.classes) and (kind.when is None or resolve(kind.when)(analysis)):
            return kind
    raise LookupError(f"No planning kind for {type(analysis).__name__}.")
