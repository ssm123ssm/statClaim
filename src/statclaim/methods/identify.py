"""Ids and kinds for the assumption sentences of the Lean-backed modules.

Those sentences are bound into certificates, so their wording stays as it is.
This table recognises each one and says what kind of assumption it is, which
lets reports list every assumption of a study in one structured table. A new
Lean-backed module adds a line here for each new sentence; a test fails if an
example emits a sentence this table does not recognise.
"""

import re

from statclaim.methods.core import ASSUMPTION_KINDS

# (pattern, id, kind). The first match wins, so put specific patterns first.
RECOGNISED = [
    # Observational studies (statclaim.association).
    (r"^The exposed and unexposed groups were sampled separately", "cohort_groups", "design"),
    (r"^Cases and controls were sampled separately", "case_control_groups", "design"),
    (r"^Participants were sampled independently from one population", "random_sample", "sampling"),
    (r"^Participants' outcomes are independent of one another", "independent_outcomes", "sampling"),
    (r"^Participants' exposures are independent", "independent_exposures", "sampling"),
    (r"^Controls come from the population that gave rise", "source_population", "sampling"),
    (r"^The odds ratio of exposure between cases and controls", "odds_ratio_identity", "sampling"),
    (r"^Each case was matched to one control", "matched_pairs", "design"),
    (r"^In each group events occur independently at one", "poisson_events", "sampling"),
    (r"^Person-time is measured without error", "person_time", "sampling"),
    (r"supplied events and person-time describe", "data_match_declaration", "data"),
    (r"^In every discordant pair the case has the same", "common_conditional_odds", "sampling"),
    (r"supplied pairs describe the declared", "data_match_declaration", "data"),
    (r"^The confidence level was chosen before", "prespecified_analysis", "design"),
    (r"supplied table describes the declared", "data_match_declaration", "data"),
    # The randomisation test (statclaim.randomisation).
    (r"^Every split of the randomised units", "complete_randomisation", "design"),
    (r"^Within each stratum or block, every split", "stratified_randomisation", "design"),
    # With population="randomised" the file states who is analysed.
    (
        r"^Every randomised unit is analysed.*the assignment declares",
        "analysed_as_randomised",
        "design",
    ),
    (r"^Every randomised unit is analysed.*drawn independently", "analysed_with_draws", "data"),
    (r"^Every randomised unit is analysed", "analysed_as_randomised", "data"),
    (r"^The p-value counts every split", "counts_every_split", "data"),
    (r"^The p-value compares the observed assignment", "analysed_with_draws", "data"),
    # Which population a bound covers, when the assignment declares it (assumptions.py).
    (r"^The bound covers the randomised population", "randomised_population", "scope"),
    (r"^The bound covers the per-protocol population", "per_protocol_population", "scope"),
    # Before the generic "fixed before": this one is assumed, not stated by the file.
    (r"^Who is excluded after randomisation", "prespecified_exclusions", "sampling"),
    (r"null that treatment changes no participant's outcome", "bound_under_null", "scope"),
    (r"posterior rule is the binomial-sum form", "posterior_closed_form", "unproved_step"),
    (r"planning point", "planning_point_is_input", "scope"),
    (r"joint sampling law is a probability law", "common_probability_law", "sampling"),
    (r"^Each endpoint null is", "bound_under_null", "scope"),
    (r"^The null hypothesis is|^The error bound is under the null", "bound_under_null", "scope"),
    (r"supplied counts? describes? the declared", "data_match_declaration", "data"),
    (r"^Stage sizes and the interim and final rules", "prespecified_stages", "design"),
    (r"set of analyses and their levels are chosen before", "prespecified_family", "design"),
    # Choosing the analysis in advance is a different promise from fixing the sizes.
    (r"analysis and its level are chosen before", "prespecified_analysis", "design"),
    (r"fixed before", "prespecified_design", "design"),
    (r"independent with one common response rate", "independent_common_rate", "sampling"),
    (
        r"independent binomial|independent-binomial|samples are independent, each with one",
        "independent_binomial_arms",
        "sampling",
    ),
    (r"own two-arm model; dependence between outcomes", "common_probability_law", "sampling"),
]
STATUS = {"design": "declared", "scope": "condition"}


def mark(assumption) -> dict:
    """A structured assumption with its status: design ones are stated by the file itself,
    scope ones say which null, population or planning point a claim is about, the rest are
    assumed."""
    return {**assumption.to_dict(), "status": STATUS.get(assumption.kind, "assumed")}


def identify(text: str) -> dict:
    """The id, kind and status of one assumption sentence; id None if unrecognised."""
    for pattern, identifier, kind in RECOGNISED:
        if re.search(pattern, text):
            assert kind in ASSUMPTION_KINDS
            return {
                "id": identifier,
                "kind": kind,
                "text": text,
                "status": STATUS.get(kind, "assumed"),
            }
    return {"id": None, "kind": None, "text": text, "status": "assumed"}
