"""A compiled program as Lean data for `StatClaim.Semantics`, and the check that Lean's
encoding of that data is the canonical program (docs/proposals/lean-semantics.md).

The writer is not trusted. It reads the canonical program, the form certificates bind,
and refuses every key it does not know, so it cannot drop a field silently. Lean prints
the data's canonical form (`StatClaim/Semantics/Encode.lean`), and `binding_problem`
compares it with the canonical program's `verify` claims: a mistake in the writer makes
that comparison fail, never a statement about another program.
"""

import json
import re
from fractions import Fraction

from statclaim.composition import CITED_RULES, cited_rule
from statclaim.lean_translation.emit import rational
from statclaim.methods import METHODS, NULL_FORMS, OBSERVATIONAL, OUTCOMES
from statclaim.planning import MarginTest, fisher_bounds, margin_grid

SEMANTICS = "StatClaim.Semantics"
# Every program Lean reads is checked for its contracts and for canonical form: the form
# it prints then determines it (`Program.form_injective`).
CONTRACTS = "theorem contracts : program.Contracts := by decide +kernel"
CANONICAL = "theorem canonical : program.Canonical := by decide +kernel"
MARKER = "STATCLAIM_PROGRAM"
GRADES = "STATCLAIM_GRADES"
# The model constructor each outcome kind's module names, as the canonical program writes it.
MODULES = {outcome.constructor: key for key, outcome in OUTCOMES.items()}
STOPPING = ("fixed", "data_dependent")
# The combinations Lean proves, by method. Cited ones are `.procedure` with a registry rule.
COMBINATIONS = {
    "bonferroni": "bonferroni",
    "fixed_sequence": "sequence",
    "alpha_spending": "looks",
}
CITED_METHODS = {dict(rule.fields)["method"] for rule in CITED_RULES}
# What a model may declare beyond its outcome and sizes.
MODEL_EXTRAS = (
    "clusters_control",
    "clusters_treatment",
    "randomisation",
    "strata",
    "block_size",
    "population",
    "better",
    "measurements",
    "outcome_name",
)
ANALYSIS = {"test", "design", "null", "alpha"}
# A declared test is described by the file: its method, scope and references.
DECLARED = "declared_test"
DECLARED_FIELDS = {"method", "scope", "references"}
SCOPES = {"finite_sample": "finiteSample", "asymptotic": "largeSample"}
# Bindings the semantics declares: tests and combinations, whose contracts it checks. Every
# other typed value is read inside the tests and claims that use it: a model, a design, a
# null, observed data, a planning input or a claim declares nothing of its own, however the
# file binds it. A test checks that every kind of test and combination is listed here.
DECLARATIONS = (
    "AnalysisIR",
    "AssociationAnalysisIR",
    "MatchedAnalysisIR",
    "RateAnalysisIR",
    "RandomisationAnalysisIR",
    "OneSampleAnalysisIR",
    "TwoStageAnalysisIR",
    "CitedAnalysisIR",
    "CitedAssociationIR",
    "ComposedFamilyIR",
    "SequentialIR",
    "FamilyIR",
)
EXACT_STUDY = {"fisher_exact", "mcnemar", "rate_test"}
# What an observational study declares: its design, the sizes it fixes, its variables,
# and how they were measured and sampled. Scales and surveys must be ones the registry's
# methods name, so Lean has them.
STUDY_SIZES = ("n", "cases", "controls", "exposed", "unexposed", "pairs")
DESIGNS = sorted({d for m in OBSERVATIONAL.values() for d in m.designs})
SCALES = sorted(
    {s for m in OBSERVATIONAL.values() for s in (*m.outcome_scales, *m.exposure_scales)}
)
SURVEYS = sorted({s for m in OBSERVATIONAL.values() for s in m.surveys})


class Outside(ValueError):
    """The program has a part the semantics does not cover yet."""


def fields(value: object, required: set[str], what: str, optional: set[str] = set()) -> dict:  # noqa: B006
    """The value as a record with exactly the expected keys."""
    if not isinstance(value, dict):
        raise Outside(f"{what} is not a record.")
    missing, unknown = required - value.keys(), value.keys() - required - optional
    if missing:
        raise Outside(f"{what} lacks fields the semantics reads: {sorted(missing)}.")
    if unknown:
        raise Outside(f"{what} has fields the semantics does not read: {sorted(unknown)}.")
    return value


def count(value: object, what: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise Outside(f"{what} is not a count.")
    return value


def string(value: object, what: str = "A name") -> str:
    """A Lean string literal."""
    if not isinstance(value, str) or re.search(r"[\x00-\x1f\x7f]", value):
        raise Outside(f"{what} is not plain text.")
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def exact(value: object, what: str) -> str:
    if not isinstance(value, str):
        raise Outside(f"{what} is not an exact number.")
    return rational(Fraction(value))


def level(value: object) -> str:
    return f"⟨{exact(value, 'A level')}, by norm_num, by norm_num⟩"


def probability(value: object) -> str:
    if not isinstance(value, str):
        raise Outside("A probability is not an exact number.")
    num, den = Fraction(value).as_integer_ratio()
    return f"⟨{count(num, 'A probability numerator')}, {den}, by decide, by decide, by decide⟩"


def boolean(value: object) -> str:
    if not isinstance(value, bool):
        raise Outside("A reported decision is not a Boolean.")
    return str(value).lower()


def natural_option(value: object) -> str:
    return "none" if value is None else f"(some {count(value, 'An optional count')})"


def model(value: object) -> str:
    record = fields(value, {"module", "n_control", "n_treatment"}, "A model", set(MODEL_EXTRAS))
    if record["module"] not in MODULES:
        raise Outside(f"The model {record['module']!r} is not a two-arm model.")
    control, treatment = (
        count(record["n_control"], "A size"),
        count(record["n_treatment"], "A size"),
    )
    parts = [
        f"outcome := .{MODULES[record['module']]}",
        f"sizes := ⟨{control}, {treatment}, by decide, by decide⟩",
    ]
    clusters = [key in record for key in ("clusters_control", "clusters_treatment")]
    if any(clusters):
        if not all(clusters):
            raise Outside("A model declares clusters in one arm only.")
        parts.append(
            f"clusters := some ({count(record['clusters_control'], 'A count')}, "
            f"{count(record['clusters_treatment'], 'A count')})"
        )
    if "randomisation" in record:
        parts.append(f"randomisation := some {string(record['randomisation'])}")
    if "strata" in record:
        strata = record["strata"]
        if not isinstance(strata, list) or not strata:
            raise Outside("Strata are not a list of strata.")
        pairs = []
        for stratum in strata:
            if not isinstance(stratum, list) or len(stratum) != 2:
                raise Outside("A stratum is not a pair of counts.")
            pairs.append(f"({count(stratum[0], 'A count')}, {count(stratum[1], 'A count')})")
        parts.append(f"strata := [{', '.join(pairs)}]")
    if "block_size" in record:
        parts.append(f"blockSize := some {count(record['block_size'], 'A block size')}")
    if "population" in record:
        parts.append(f"population := some {string(record['population'])}")
    if "better" in record:
        parts.append(f"better := some {string(record['better'])}")
    if "measurements" in record:
        parts.append(f"measurements := some {count(record['measurements'], 'A count')}")
    if "outcome_name" in record:
        parts.append(f"name := some {string(record['outcome_name'])}")
    return "{ " + ", ".join(parts) + " }"


def study(value: object) -> str:
    optional = {*STUDY_SIZES, "exposure_scale", "outcome_scale", "survey", "clusters"}
    record = fields(value, {"study", "exposure", "outcome"}, "A study", optional)
    if record["study"] not in DESIGNS:
        raise Outside(f"The study design {record['study']!r} is not in the semantics.")
    parts = [f"design := .{record['study']}"]
    parts += [
        f"{size} := some {count(record[size], 'A size')}" for size in STUDY_SIZES if size in record
    ]
    parts += [
        f"exposure := {string(record['exposure'])}",
        f"outcome := {string(record['outcome'])}",
    ]
    for key, field, known in (
        ("exposure_scale", "exposureScale", SCALES),
        ("outcome_scale", "outcomeScale", SCALES),
        ("survey", "survey", SURVEYS),
    ):
        if key in record:
            if record[key] not in known:
                raise Outside(
                    f"The {key.replace('_', ' ')} {record[key]!r} is not in the semantics."
                )
            parts.append(f"{field} := .{record[key]}")
    if "clusters" in record:
        parts.append(f"clusters := some {count(record['clusters'], 'A count')}")
    return "{ " + ", ".join(parts) + " }"


def study_design(value: object) -> str:
    record = fields(value, {"model", "stopping"}, "A design")
    if record["stopping"] not in STOPPING:
        raise Outside(f"The stopping rule {record['stopping']!r} is not one the semantics reads.")
    return f"{{ model := {study(record['model'])}, stopping := .{record['stopping']} }}"


def design(value: object) -> str:
    record = fields(value, {"model", "stopping"}, "A design")
    if record["stopping"] not in STOPPING:
        raise Outside(f"The stopping rule {record['stopping']!r} is not one the semantics reads.")
    return f"{{ model := {model(record['model'])}, stopping := .{record['stopping']} }}"


def null(value: object) -> str:
    record = fields(value, {"predicate", "model"}, "A null", {"value"})
    if record["predicate"] not in NULL_FORMS:
        raise Outside(f"The null {record['predicate']!r} is not a two-arm null form.")
    parts = [f"key := .{record['predicate']}", f"model := {model(record['model'])}"]
    if "value" in record:
        parts.append(f"value := some {exact(record['value'], 'A null value')}")
    return "{ " + ", ".join(parts) + " }"


def one_sided(value: object) -> bool:
    return (
        isinstance(value, dict)
        and value.get("test") == "fisher"
        and value.get("alternative") == "greater"
    )


def exact_member(value: dict) -> bool:
    return value.get("test") in {*EXACT_STUDY, "randomisation"} or value.get("alternative") in (
        "greater",
        "margin",
    )


def margin_test(subject: dict) -> MarginTest:
    model = subject["design"]["model"]
    return MarginTest(
        model["n_control"],
        model["n_treatment"],
        Fraction(subject["null"]["value"]),
        Fraction(subject["alpha"]),
    )


def test(name: object, value: object) -> str:
    """A test or combination, named as its declaration is."""
    label = string(name)
    if isinstance(value, dict) and "analyses" in value:
        method = value["method"]
        rule = cited_rule(value) if method in CITED_METHODS else None
        if method not in COMBINATIONS and rule is None:
            raise Outside(f"The combination {method!r} is not in the semantics yet.")
        # A family of Fisher tests records its joint law instead of a composition.
        joint = method == "bonferroni" and "joint_law" in value
        extra = (
            set()
            if rule is None
            else {key for key, _ in rule.fields[1:]}
            | ({"weights", "transitions"} if rule.graph else set())
        )
        composition_field = {"joint_law"} if joint else {"composition"}
        record = fields(
            value, {"method", "alpha", "analyses", *composition_field, *extra}, "A combination"
        )
        if not joint and record["composition"] != "conditional":
            raise Outside("A combination is not a conditional combination of analyses.")
        if not isinstance(record["analyses"], list):
            raise Outside("A combination's members are not a list.")
        members = []
        for entry in record["analyses"]:
            member = fields(entry, {"name", "analysis"}, "A member")
            encoded = test(member["name"], member["analysis"])
            if not joint and exact_member(member["analysis"]):
                encoded = f".member ({encoded})"
            members.append(encoded)
        listed = "[" + ",\n    ".join(members) + "]"
        if rule is not None:
            weights = [exact(w, "A weight") for w in record.get("weights", [])]
            rows = [
                [exact(t, "A transition") for t in row] for row in record.get("transitions", [])
            ]
            shares = (
                "["
                + ", ".join(weights)
                + "] ["
                + ", ".join("[" + ", ".join(row) + "]" for row in rows)
                + "]"
            )
            alpha = level(record["alpha"])
            return f".procedure {label} .{rule.key}\n    {listed}\n    {alpha} {shares}"
        stated = f".{COMBINATIONS[method]} {label}\n    {listed}\n    {level(record['alpha'])}"
        if method == "bonferroni":
            law = f"(some {string(record['joint_law'], 'A joint law')})" if joint else "none"
            return f"{stated} {law}"
        return stated
    declared = isinstance(value, dict) and value.get("test") == DECLARED
    if isinstance(value, dict) and value.get("test") in ("binomial_exact_one_sided", "two_stage"):
        return policy_test(label, value)
    if isinstance(value, dict) and value.get("test") == "randomisation":
        return randomised(label, value)
    if isinstance(value, dict) and value.get("test") in EXACT_STUDY:
        return exact_study(label, value)
    association = isinstance(value, dict) and value.get("test") in OBSERVATIONAL
    if association:
        return associated(label, value)
    exact_fisher = isinstance(value, dict) and value.get("test") == "fisher" and exact_member(value)
    extra = DECLARED_FIELDS if declared else {"alternative"} if exact_fisher else set()
    record = fields(value, ANALYSIS | extra, "An analysis")
    cited = METHODS.get(record["test"])
    known = record["test"] == "fisher" or declared or (cited is not None and cited.grade == "cited")
    if not known:
        raise Outside(f"The test {record['test']!r} is not in the semantics yet.")
    parts = (
        f"{design(record['design'])}\n      {null(record['null'])}\n      {level(record['alpha'])}"
    )
    if record["test"] == "fisher":
        if exact_fisher:
            if record["alternative"] == "margin":
                selected = margin_test(record)
                assert selected.thresholds is not None
                kind = f"(.margin {rational(selected.margin)} {list(selected.thresholds)})"
            else:
                kind = ".fisherOneSided"
            return f".exact {label} {kind}\n      {parts}"
        return f".fisher {label}\n      {parts}"
    if declared:
        if record["scope"] not in SCOPES or not isinstance(record["references"], list):
            raise Outside("A declared test's scope or references are not ones the semantics reads.")
        references = ", ".join(string(r, "A reference") for r in record["references"])
        guarantee = (
            f"(.declared {string(record['method'], 'A method')} .{SCOPES[record['scope']]} "
            f"[{references}])"
        )
        return f".assumed {label} {guarantee}\n      {parts}"
    assert cited is not None
    return f".assumed {label} (.cited StatClaim.Generated.Methods.{cited.key})\n      {parts}"


def associated(label: str, value: object) -> str:
    """A cited test of association in an observational study."""
    record = fields(value, ANALYSIS, "An analysis", {"adjusted_for"})
    method = OBSERVATIONAL[record["test"]]
    covariates = record.get("adjusted_for", [])
    if not isinstance(covariates, list) or not covariates and "adjusted_for" in record:
        raise Outside("A test's covariates are not a list of names.")
    adjusted = ", ".join(string(c, "A covariate") for c in covariates)
    return (
        f".associated {label} StatClaim.Generated.Methods.{method.key}\n"
        f"      {study_design(record['design'])}\n"
        f"      {study_null(record['null'])}\n"
        f"      {level(record['alpha'])} [{adjusted}]"
    )


def study_null(value: object) -> str:
    record = fields(value, {"predicate", "model"}, "A study null")
    if record["predicate"] != "no_association":
        raise Outside(f"The null {record['predicate']!r} is not one a study has.")
    return f"{{ model := {study(record['model'])} }}"


def exact_study(label: str, value: object) -> str:
    record = fields(value, ANALYSIS, "An exact association analysis")
    model = fields(record["design"], {"model", "stopping"}, "A design")["model"]
    method = record["test"]
    if method == "fisher_exact":
        has_groups = model["study"] == "case_control" or {"exposed", "unexposed"} <= model.keys()
        kind = "fisherGroups" if has_groups else "fisherMixture"
    else:
        kind = "matched" if method == "mcnemar" else "incidence"
    return (
        f".exactStudy {label} .{kind}\n      {study_design(record['design'])}\n"
        f"      {study_null(record['null'])}\n      {level(record['alpha'])}"
    )


def randomised(label: str, value: object) -> str:
    record = fields(value, ANALYSIS, "A randomisation test", {"draws"})
    stated_null = fields(record["null"], {"predicate", "model"}, "A sharp null")
    if stated_null["predicate"] != "no_effect":
        raise Outside("A randomisation test requires a sharp null.")
    draws = f"some {count(record['draws'], 'A draw count')}" if "draws" in record else "none"
    return (
        f".randomised {label} {{ design := {design(record['design'])}, "
        f"nullModel := {model(stated_null['model'])}, alpha := {level(record['alpha'])}, "
        f"draws := {draws} }}"
    )


def policy_test(label: str, value: dict) -> str:
    if value["test"] == "binomial_exact_one_sided":
        record = fields(value, {"test", "model", "null_rate", "alpha"}, "A one-sample analysis")
        model = fields(record["model"], {"module", "n"}, "A one-arm model")
        if model["module"] != "one_arm_binomial":
            raise Outside("A one-sample analysis requires a one-arm model.")
        return (
            f".oneSample {label} {count(model['n'], 'A sample size')} "
            f"{probability(record['null_rate'])} {probability(record['alpha'])}"
        )
    record = fields(value, {"test", "design", "rule", "null_rate"}, "A two-stage analysis")
    stages = fields(record["design"], {"module", "n_stage1", "n_stage2"}, "Stage sizes")
    if stages["module"] != "two_stage_binomial":
        raise Outside("A two-stage analysis requires a two-stage binomial model.")
    first = count(stages["n_stage1"], "A stage size")
    second = count(stages["n_stage2"], "A stage size")
    sizes = f"⟨{first}, {second}⟩"
    return (
        f".twoStage {label} {sizes} {stage_rule(record['rule'])} {probability(record['null_rate'])}"
    )


def table_data(value: object) -> str:
    keys = ("exposed_cases", "exposed_noncases", "unexposed_cases", "unexposed_noncases")
    o = fields(value, {"model", *keys}, "An observed table")
    counts = ", ".join(str(count(o[key], "A table count")) for key in keys)
    return f"⟨{study(o['model'])}, {counts}⟩"


def pairs_data(value: object) -> str:
    keys = ("both_exposed", "case_exposed_only", "control_exposed_only", "neither_exposed")
    o = fields(value, {"model", *keys}, "Observed pairs")
    counts = ", ".join(str(count(o[key], "A pair count")) for key in keys)
    return f"⟨{study(o['model'])}, {counts}⟩"


def events_data(value: object) -> str:
    o = fields(
        value,
        {"model", "exposed_events", "unexposed_events", "exposed_time", "unexposed_time"},
        "Observed events",
    )
    return (
        f"⟨{study(o['model'])}, {count(o['exposed_events'], 'An event count')}, "
        f"{count(o['unexposed_events'], 'An event count')}, {exact(o['exposed_time'], 'A time')}, "
        f"{exact(o['unexposed_time'], 'A time')}⟩"
    )


def result_data(name: str, subject: dict, reported: dict | None) -> str:
    if reported is None:
        raise Outside("The result's reported values are missing.")
    analysis = subject["analysis"]
    test_term = test(name, analysis)
    method = analysis["test"]
    reject = boolean(reported["reject_null"])
    if method == "fisher":
        o = fields(
            subject, {"analysis", "control_successes", "treatment_successes"}, "An observation"
        )
        control = count(o["control_successes"], "An observed count")
        treatment = count(o["treatment_successes"], "An observed count")
        observed = f"⟨{control}, {treatment}⟩"
        if one_sided(analysis):
            found = fields(reported, {"p_value", "reject_null"}, "A reported result")
            return (
                f".result {string(name)} ({test_term}) {observed} "
                f"⟨{probability(found['p_value'])}, {reject}⟩"
            )
        if analysis.get("alternative") == "margin":
            fields(reported, {"reject_null"}, "A reported margin result")
            grid, shift = margin_grid(Fraction(analysis["null"]["value"]))
            gridded = (
                f"((((({max(shift, 0)} : ℕ) : ℚ) - (({max(-shift, 0)} : ℕ) : ℚ)) "
                f"/ (({grid} : ℕ) : ℚ)))"
            )
            data = f".margin {observed} {reject} {probability(analysis['alpha'])} {gridded}"
        else:
            found = fields(
                reported,
                {
                    "p_value",
                    "reject_null",
                    "observed_table_probability",
                    "support_min",
                    "support_max",
                },
                "A Fisher result",
            )
            values = (
                f"⟨⟨{probability(found['p_value'])}, {reject}⟩, "
                f"{probability(found['observed_table_probability'])}⟩"
            )
            data = (
                f".fisher {observed} {values} {count(found['support_min'], 'A bound')} "
                f"{count(found['support_max'], 'A bound')} {probability(analysis['alpha'])}"
            )
    elif method == "fisher_exact":
        o = fields(subject, {"analysis", "table"}, "An observed association")
        found = fields(
            reported,
            {"p_value", "reject_null", "observed_table_probability"},
            "An association result",
        )
        data = (
            f".association {table_data(o['table'])} ⟨⟨{probability(found['p_value'])}, {reject}⟩, "
            f"{probability(found['observed_table_probability'])}⟩"
        )
    elif method in {"mcnemar", "rate_test"}:
        is_matched = method == "mcnemar"
        key = "pairs" if is_matched else "events"
        o = fields(subject, {"analysis", key}, "An observed exact test")
        found = fields(
            reported,
            {"p_value", "reject_null", "upper_tail", "lower_tail"},
            "A reported exact result",
        )
        tails = (
            f"⟨⟨{probability(found['p_value'])}, {reject}⟩, "
            f"{count(found['upper_tail'], 'A tail numerator')}, "
            f"{count(found['lower_tail'], 'A tail numerator')}⟩"
        )
        if is_matched:
            data = f".matched {pairs_data(o[key])} {tails}"
        else:
            event = o[key]
            exposed, unexposed = Fraction(event["exposed_time"]), Fraction(event["unexposed_time"])
            share = probability(str(exposed / (exposed + unexposed)))
            data = f".rate {events_data(event)} {share} {tails}"
    elif method == "binomial_exact_one_sided":
        o = fields(subject, {"analysis", "responses"}, "An observed count")
        found = fields(reported, {"p_value", "reject_null", "critical_value"}, "A binomial result")
        data = (
            f".oneSample {count(o['responses'], 'A count')} "
            f"{count(found['critical_value'], 'A critical value')} "
            f"⟨{probability(found['p_value'])}, {reject}⟩"
        )
    elif method == "two_stage":
        o = fields(
            subject, {"analysis", "stage1_responses"}, "Observed stage counts", {"stage2_responses"}
        )
        found = fields(reported, {"continued", "reject_null", "typeI_bound"}, "A stage result")
        data = (
            f".twoStage {count(o['stage1_responses'], 'A first-stage count')} "
            f"{natural_option(o.get('stage2_responses'))} {boolean(found['continued'])} "
            f"{reject} {probability(found['typeI_bound'])}"
        )
    else:
        raise Outside(f"Results for {method!r} are outside the semantics.")
    return f".checkedResult {string(name)} ({test_term}) ({data})"


def interval_data(name: str, subject: dict, reported: dict | None) -> str:
    if reported is None:
        raise Outside("The interval's reported endpoints are missing.")
    level_value = probability(subject["level"])
    tail = probability(reported["tail"])
    code = f"{level_value} {tail}"

    def endpoints(key: str | None = None) -> str:
        low, high = (reported["lower"], reported["upper"]) if key is None else reported[key]
        return f"⟨{probability(low)}, {probability(high)}⟩"

    if "table" in subject:
        item = fields(subject, {"table", "measure", "level"}, "An association interval")
        code = (
            f".association {table_data(item['table'])} {string(item['measure'])} {code} "
            f"{endpoints('control')} {endpoints('treatment')}"
        )
    elif "pairs" in subject:
        item = fields(subject, {"pairs", "level"}, "A matched interval")
        code = f".matched {pairs_data(item['pairs'])} {code} {endpoints('arm')}"
    elif "events" in subject:
        item = fields(subject, {"events", "level"}, "An incidence interval")
        code = f".rate {events_data(item['events'])} {code} {endpoints('arm')}"
    elif "responses" in subject:
        item = fields(subject, {"model", "responses", "level"}, "A binomial interval")
        arm = fields(item["model"], {"module", "n"}, "A one-arm model")
        if arm["module"] != "one_arm_binomial":
            raise Outside("A response interval needs a one-arm model.")
        code = (
            f".binomial {count(arm['n'], 'An arm size')} "
            f"{count(item['responses'], 'A count')} {code} {endpoints()}"
        )
    elif "cases" in subject:
        item = fields(
            subject, {"model", "cases", "measure", "level"}, "A proportion interval", {"group"}
        )
        group = f"(some {string(item['group'])})" if "group" in item else "none"
        code = (
            f".proportion {study(item['model'])} {string(item['measure'])} {group} "
            f"{count(item['cases'], 'A count')} {code} {endpoints()}"
        )
    else:
        item = fields(
            subject,
            {"model", "control_successes", "treatment_successes", "level"},
            "A difference interval",
        )
        control = count(item["control_successes"], "An observed count")
        treatment = count(item["treatment_successes"], "An observed count")
        code = (
            f".difference {model(item['model'])} ⟨{control}, {treatment}⟩ {code} "
            f"{endpoints('control')} {endpoints('treatment')}"
        )
    return f".interval {string(name)} ({code})"


def verify_claims(program: dict) -> list:
    """The claims of a canonical program's `verify` requests, in order: what Lean prints."""
    return [request["claim"] for request in program["requests"] if request["operation"] == "verify"]


def declarations(program: dict) -> list[dict]:
    """The tests and combinations the program declares, as Lean prints them back."""
    found = []
    for binding in program["bindings"]:
        kind = binding["type"]
        if kind in DECLARATIONS:
            found.append({"name": binding["name"], "type": kind, "value": binding["value"]})
    return found


def stage_rule(value: object) -> str:
    record = fields(
        value,
        {"kind"},
        "A stage rule",
        {
            "continue_above",
            "reject_above",
            "prior_a",
            "prior_b",
            "reference",
            "continue_at_least",
            "success_at_least",
        },
    )
    if record["kind"] == "threshold":
        rule = fields(value, {"kind", "continue_above", "reject_above"}, "A threshold rule")
        first = count(rule["continue_above"], "An interim threshold")
        final = count(rule["reject_above"], "A final threshold")
        return f"(.threshold {first} {final})"
    if record["kind"] == "posterior":
        rule = fields(
            value,
            {"kind", "prior_a", "prior_b", "reference", "continue_at_least", "success_at_least"},
            "A posterior rule",
        )
        a = count(rule["prior_a"], "A prior parameter")
        b = count(rule["prior_b"], "A prior parameter")
        points = " ".join(
            probability(rule[key]) for key in ("reference", "continue_at_least", "success_at_least")
        )
        return f"(.posterior {a} {b} {points})"
    raise Outside("The stopping rule is not a threshold or posterior rule.")


def planning_point(point: dict) -> str:
    if "p_control" in point:
        fields(point, {"p_control", "p_treatment"}, "A two-arm planning point")
        return f"(.arms ⟨{probability(point['p_control'])}, {probability(point['p_treatment'])}⟩)"
    if "response_rate" in point:
        fields(point, {"response_rate"}, "A response rate")
        return f"(.response {probability(point['response_rate'])})"
    if "discordant" in point:
        fields(point, {"discordant", "odds_ratio"}, "A matched planning point")
        odds = Fraction(point["odds_ratio"])
        return (
            f"(.matched {probability(point['discordant'])} {rational(odds)} "
            f"{probability(str(odds / (1 + odds)))})"
        )
    if "rate_ratio" in point:
        fields(
            point,
            {"rate_ratio", "exposed_time", "unexposed_time"},
            "An incidence point",
            {"events"},
        )
        ratio, exposed_time, unexposed_time = (
            Fraction(point[key]) for key in ("rate_ratio", "exposed_time", "unexposed_time")
        )
        null_share = exposed_time / (exposed_time + unexposed_time)
        alternative_share = ratio * exposed_time / (ratio * exposed_time + unexposed_time)
        return (
            f"(.rate {rational(ratio)} {rational(exposed_time)} {rational(unexposed_time)} "
            f"{natural_option(point.get('events'))} {probability(str(null_share))} "
            f"{probability(str(alternative_share))})"
        )
    for first, second in (
        ("risk_unexposed", "risk_exposed"),
        ("prevalence_unexposed", "prevalence_exposed"),
        ("exposure_controls", "exposure_cases"),
    ):
        if first in point:
            fields(point, {first, second}, "An association point", {"exposed_share"})
            share = (
                f"(some {probability(point['exposed_share'])})"
                if "exposed_share" in point
                else "none"
            )
            return (
                f"(.association {string(first)} {string(second)} "
                f"⟨{probability(point[first])}, {probability(point[second])}⟩ {share})"
            )
    raise Outside("The planning point has no exact Lean model.")


def plan_selection(reported: dict | None) -> str:
    if reported is None:
        return "none"
    if "n_stage1" in reported:
        r = fields(reported, {"n_stage1", "n_stage2", "rule"}, "A selected two-stage design")
        first, second = (count(r[key], "A stage size") for key in ("n_stage1", "n_stage2"))
        selection = f".stages ⟨{first}, {second}⟩ {stage_rule(r['rule'])}"
    elif "n_control" in reported:
        r = fields(reported, {"n_control", "n_treatment"}, "A selected two-arm design")
        first, second = (count(r[key], "An arm size") for key in ("n_control", "n_treatment"))
        selection = f".arms ⟨{first}, {second}, by decide, by decide⟩"
    elif "critical_value" in reported:
        r = fields(reported, {"n", "critical_value"}, "A selected one-arm design")
        selection = (
            f".oneSample {count(r['n'], 'A size')} {count(r['critical_value'], 'A threshold')}"
        )
    else:
        r = fields(reported, {"n"}, "A selected count")
        selection = f".count {count(r['n'], 'A size')}"
    return f"(some ({selection}))"


def supported_plan(subject: dict) -> bool:
    candidates = subject.get("candidates", {})
    analysis = subject.get("analysis", candidates.get("analysis", {}))
    return candidates.get("design") == "two_stage_threshold" or (
        analysis.get("test")
        in {
            "fisher",
            "fisher_exact",
            "mcnemar",
            "rate_test",
            "binomial_exact_one_sided",
            "two_stage",
        }
        and analysis.get("alternative") != "margin"
    )


def planning_query(name: str, kind: str, subject: dict) -> str:
    if kind == "meets":
        fields(subject, {"analysis", "target"}, "A feasibility request")
        return f".meets ({test(name, subject['analysis'])})"
    fields(subject, {"candidates", "target", "claim"}, "A sample-size request")
    candidates = subject["candidates"]
    minimal = subject["claim"] == "smallest_in_range"
    if candidates.get("design") == "two_stage_threshold":
        fields(candidates, {"design", "null_rate", "max_total", "criterion"}, "A two-stage search")
        if subject["claim"] != "sufficient":
            raise Outside("Two-stage searches certify sufficiency.")
        return (
            f".stageSearch {probability(candidates['null_rate'])} "
            f"{count(candidates['max_total'], 'A search limit')} {string(candidates['criterion'])}"
        )
    if subject["claim"] not in {"smallest_in_range", "sufficient"}:
        raise Outside("The search must ask for a smallest or a sufficient size.")
    analysis = candidates["analysis"]
    ratio = 1
    if "allocation" in candidates:
        fields(
            candidates, {"analysis", "allocation", "min_per_arm", "max_per_arm"}, "An arm search"
        )
        low, high = candidates["min_per_arm"], candidates["max_per_arm"]
        if candidates["allocation"] != "equal_arms":
            ratio = int(candidates["allocation"].removeprefix("1:"))
        search = "arms"
    elif "min_cases" in candidates or "min_exposed" in candidates:
        if "min_cases" in candidates:
            low_key, high_key, ratio_key = "min_cases", "max_cases", "controls_per_case"
        else:
            low_key, high_key, ratio_key = "min_exposed", "max_exposed", "unexposed_per_exposed"
        fields(candidates, {"analysis", low_key, high_key, ratio_key}, "A group search")
        low, high, ratio = (candidates[key] for key in (low_key, high_key, ratio_key))
        search = "groups"
    else:
        search = {
            "mcnemar": "pairs",
            "rate_test": "events",
            "fisher_exact": "total",
            "binomial_exact_one_sided": "oneSample",
        }[analysis["test"]]
        unit = "n" if search in {"oneSample", "total"} else search
        low_key, high_key = f"min_{unit}", f"max_{unit}"
        fields(candidates, {"analysis", low_key, high_key}, "A count search")
        low, high = candidates[low_key], candidates[high_key]
    bounds = (
        f"⟨{count(low, 'A lower bound')}, {count(high, 'An upper bound')}, "
        f"{count(ratio, 'An allocation ratio')}, by decide, {boolean(minimal)}⟩"
    )
    return f".search ({test(name, analysis)}) .{search} {bounds}"


def plan_data(name: str, kind: str, subject: dict, reported: dict | None) -> str:
    if not supported_plan(subject):
        raise Outside("The planning request has no exact Lean model.")
    query = planning_query(name, kind, subject)
    target = fields(subject["target"], {"at", "minimum_power", "maximum_typeI"}, "A target")
    goal = (
        f"⟨{planning_point(target['at'])}, {probability(target['minimum_power'])}, "
        f"{probability(target['maximum_typeI'])}⟩"
    )
    return f".planned {string(name)} ({query}) {goal} {plan_selection(reported)}"


def request_data(claim: dict, *, reported: dict | None) -> str:
    record = fields(claim, {"kind", "subject_name", "subject"}, "A claim")
    kind, name, subject = record["kind"], record["subject_name"], record["subject"]
    if kind in ("typeI", "familywise") and reported is None:
        return f".{kind} ({test(name, subject)})"
    if kind == "result":
        return result_data(name, subject, reported)
    if kind == "interval":
        return interval_data(name, subject, reported)
    if kind in {"meets", "sample_size"}:
        return plan_data(name, kind, subject, reported)
    raise Outside(f"Claims of kind {kind!r} are not in the semantics yet.")


def program_data(program: dict, reported: list[dict | None] | None = None) -> str:
    """The Lean definition of `program`, or `Outside` when the semantics does not cover it."""
    verified = verify_claims(program)
    outputs = [None] * len(verified) if reported is None else reported
    requests = [
        request_data(claim, reported=output)
        for claim, output in zip(verified, outputs, strict=True)
    ]
    declared = [test(entry["name"], entry["value"]) for entry in declarations(program)]
    listed = ",\n  ".join(requests)
    tests = ",\n  ".join(declared)
    return (
        f"def program : {SEMANTICS}.Program where\n"
        f"  requests := [\n  {listed}]\n"
        f"  declarations := [\n  {tests}]\n"
    )


def fixed(value: object) -> bool:
    """Whether every design in a claim's subject stops at fixed sizes. A claim about one
    that does not has no sampling law, and the semantics states it as `False`."""
    if isinstance(value, dict):
        if value.get("stopping") not in (None, "fixed"):
            return False
        return all(fixed(item) for item in value.values())
    if isinstance(value, list):
        return all(fixed(item) for item in value)
    return True


def allocated(value: dict) -> bool:
    """Whether the shares of every family and design with looks in a claim's subject add up
    to at most its level (`Test.allocated`). Python leaves a claim without this open."""
    if "analyses" not in value:
        return True
    members = [member["analysis"] for member in value["analyses"]]
    within = value["method"] not in ("bonferroni", "alpha_spending") or sum(
        Fraction(member["alpha"]) for member in members
    ) <= Fraction(value["alpha"])
    return within and all(allocated(member) for member in members)


def ready(claim: dict, outputs: list[dict | None] | None = None, index: int = 0) -> bool:
    """Whether the semantics proves a claim (`Program.readyAt`): its designs stop at fixed
    sizes and its levels are within budget."""
    if outputs is not None and claim["kind"] in {"meets", "sample_size"} and outputs[index] is None:
        return False
    return fixed(claim["subject"]) and allocated(claim["subject"])


def premise_keys(name: str, subject: dict) -> list[tuple[str, str]]:
    """The premises the semantics gives a test, in its order (`Test.premises`): the level
    of each assumed test, and the familywise bound of each graph after its members'."""
    if "analyses" in subject:
        keys = []
        for member in subject["analyses"]:
            if subject.get("composition") == "conditional" and exact_member(member["analysis"]):
                keys.append(("member", member["name"]))
            else:
                keys.extend(premise_keys(member["name"], member["analysis"]))
        cited = cited_rule(subject) is not None
        return keys + ([("procedure", name)] if cited else [])
    analysis = subject.get("candidates", subject).get("analysis", subject)
    if "test" not in analysis:
        return []
    return (
        []
        if analysis["test"]
        in {"fisher", "randomisation", "binomial_exact_one_sided", "two_stage", *EXACT_STUDY}
        else [("level", name)]
    )


def premise_label(key: tuple[str, str], subject: dict | None = None) -> str:
    """A premise's name in reports, as the translator names its premises."""
    kind, name = key
    if kind == "procedure":
        return f"cited_{name}_rule"
    if kind == "member":
        return f"member_{name}_level"
    declared = subject is not None and subject.get("test") == DECLARED
    return f"{'declared' if declared else 'cited'}_{name}_level"


def grade(claim: dict) -> str:
    """The grade `Program.grade` gives a claim: its own premise makes it cited, or declared
    when the author declared it; only its members' premises make it conditional; none
    makes it proved. The audit requires Lean's grade to be this one."""
    name, subject = claim["subject_name"], claim["subject"]
    keys = premise_keys(name, subject)
    own = ("procedure", name) if "analyses" in subject else ("level", name)
    if own in keys:
        return "declared" if subject.get("test") == DECLARED else "cited"
    return "conditional" if keys else "proved"


def claim_theorem(index: int, hint: str | None = None) -> str:
    text = (
        f"theorem claim_{index} : program.Claim {index} :=\n"
        f"  {SEMANTICS}.Program.sound program contracts {index} (by decide +kernel)\n"
    )
    if hint is None:
        return text.rstrip()
    return (
        "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 20000000 in\n"
        f"{text}    {hint} (by decide +kernel)"
    )


def level_hint(subject: dict) -> str | None:
    """Hints for fixed-sample Type I checks. A conditional family assumes its members."""
    if one_sided(subject):
        model = subject["design"]["model"]
        alpha = Fraction(subject["alpha"])
        return str(list(fisher_bounds(model["n_control"], model["n_treatment"], alpha)))
    if subject.get("alternative") == "margin":
        test = margin_test(subject)
        grid, shift = margin_grid(test.margin)
        assert test.cells is not None
        return f"⟨{grid}, {max(shift, 0)}, {max(-shift, 0)}, {list(test.cells)}⟩"
    return None


def claims(
    program: dict,
    hints: dict[int, str] | None = None,
    reported: list[dict | None] | None = None,
    omitted: frozenset[int] = frozenset(),
) -> str:
    """The theorems proving each claim that is ready, by the semantics' soundness theorem
    and the program's contracts."""
    lines = [CONTRACTS, CANONICAL, ""]
    for index, claim in enumerate(verify_claims(program)):
        if index not in omitted and ready(claim, reported, index):
            lines.append(claim_theorem(index, (hints or {}).get(index)))
    return "\n".join(lines) + "\n"


def report(label: str) -> str:
    """The command that prints the data's canonical form."""
    if "{" in label or "}" in label or "\n" in label:
        raise ValueError(f"{label!r} cannot label a printed program.")
    return (
        "open Lean Elab Command in\n"
        f'run_cmd logInfo m!"{MARKER} {label} {{({SEMANTICS}.Program.encode program).compress}}"\n'
        "open Lean Elab Command in\n"
        f'run_cmd logInfo m!"{GRADES} {label} {{(List.range program.requests.length).map '
        f'fun r => ({SEMANTICS}.Program.grade program r).name}}"\n'
    )


def printed(output: str, label: str) -> dict | None:
    """The canonical form Lean printed for a program, if it printed one."""
    prefix = f"{MARKER} {label} "
    for line in output.splitlines():
        start = line.find(prefix)
        if start != -1:
            return json.loads(line[start + len(prefix) :])
    return None


def printed_grades(output: str, label: str) -> list[str] | None:
    """Each claim's grade, as Lean computes it from the premises the claim assumes."""
    prefix = f"{GRADES} {label} "
    for line in output.splitlines():
        start = line.find(prefix)
        if start != -1:
            listed = line[start + len(prefix) :].strip().strip("[]")
            return [name.strip() for name in listed.split(",") if name.strip()]
    return None


def same_json(first: object, second: object) -> bool:
    """Whether two JSON values are equal as JSON: keys in any order, but `true` is not `1`."""
    return json.dumps(first, sort_keys=True) == json.dumps(second, sort_keys=True)


def binding_problem(
    output: str, label: str, program: dict, *, reported: list[dict | None] | None = None
) -> str | None:
    """Why the data Lean read differs from the canonical program or the run's outputs."""
    found = printed(output, label)
    if found is None:
        return f"Lean printed no canonical form for {label}."
    expected = {"claims": verify_claims(program), "declarations": declarations(program)}
    thresholds = written_thresholds(program)
    if thresholds:
        expected["rejection_thresholds"] = thresholds
    if reported is not None and any(output is not None for output in reported):
        if not same_json(found.get("reported"), reported):
            return f"The data Lean read for {label} differs from its reported outputs."
        expected["reported"] = reported
    if not same_json(found, expected):
        return f"The data Lean read for {label} is not its canonical program."
    return None


def written_thresholds(program: dict) -> list[dict]:
    def thresholds(name: str, subject: dict) -> list[dict]:
        if subject.get("alternative") == "margin":
            selected = margin_test(subject)
            assert selected.thresholds is not None
            return [{"name": name, "thresholds": list(selected.thresholds)}]
        return [
            value
            for member in subject.get("analyses", [])
            for value in thresholds(member["name"], member["analysis"])
        ]

    written = [
        value
        for entry in declarations(program)
        for value in thresholds(entry["name"], entry["value"])
    ]
    for claim in verify_claims(program):
        subject = claim["subject"]
        analysis = subject.get("candidates", subject).get("analysis", subject)
        written.extend(thresholds(claim["subject_name"], analysis))
    return written
