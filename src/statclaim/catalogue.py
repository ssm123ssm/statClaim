"""Classified public inventory; signatures and fields come from live registries."""

from statclaim.language import MODULES, OPERATIONS, ValueType
from statclaim.language_fields import SCHEMAS
from statclaim.methods import ASSUMPTIONS, METHOD_MODULES, METHODS, OUTCOMES
from statclaim.methods.core import ASSUMPTION_KINDS, CHECKS, GRADES, SCOPES, SOURCES
from statclaim.reference import (
    DIAGNOSTICS,
    ENUMERATIONS,
    GRAMMAR,
    LIMITS,
    PROGRAM_STATUSES,
    RESULT_STATUSES,
    VALUE_TYPES,
)

MODULE_CLASSES = {
    "models.two_arm_binomial": (
        "Models and hypotheses",
        "Two independent binomial arms; equality, difference and inequality nulls; "
        "observations and the Type I and result claims shared by two-arm analyses.",
    ),
    "sampling": (
        "Study designs",
        "Fixed sampling is supported. Adaptive sampling is descriptive; its current "
        "Type I error requirement remains unresolved.",
    ),
    "tests.fisher": (
        "Analyses and claims",
        "Two-sided Fisher analysis for the equality null and one-sided analysis for "
        '"treatment no better than control", with Lean-backed result and Type I claims '
        "under fixed sampling.",
    ),
    "tests.difference": (
        "Analyses and claims",
        "Exact test of p_treatment - p_control <= margin, for non-inferiority (negative "
        "margin) or superiority (zero). Its error bound covers the whole null. Up to 120 "
        "participants per arm.",
    ),
    "multiplicity.bonferroni": (
        "Multiplicity and composition",
        "Bonferroni for two to twenty endpoints; dependence between them is unrestricted. "
        "A family of two-sided Fisher analyses is proved outright. Any other family, "
        "with one-sided, margin or cited tests, is conditional: Lean checks the combination "
        "and the members are assumed.",
    ),
    "multiplicity.graphical": (
        "Multiplicity and composition",
        "A graphical procedure: each test starts with a share of the level and passes it on "
        "after a rejection. The contract checks the shares and transitions. The procedure's "
        "guarantee is cited, not checked by Lean.",
    ),
    "multiplicity.fixed_sequence": (
        "Multiplicity and composition",
        "Hierarchical testing in a fixed order, each test at the full level and only after "
        "every earlier test rejected. Lean checks the combination; the tests' own bounds "
        "are assumed.",
    ),
    "planning": (
        "Study planning",
        "Exact power at a planning point, target checks and a bounded sample-size search "
        "with equal or unequal allocation for the fixed Fisher analysis. "
        "Targets also apply to one-sample tests and two-stage designs. "
        "A size can be certified as sufficient or as the smallest in the declared range.",
    ),
    "estimation": (
        "Analyses and claims",
        "Confidence interval for a difference of two proportions, from an exact interval "
        "per arm. Valid for every pair of rates; conservative.",
    ),
    "tests.binomial": (
        "Analyses and claims",
        "One-sided exact binomial test for a single arm. Type I error is checked for every "
        "rate at or below the null rate; power and sample size use the planning module. "
        "Observed counts give a Lean-checked p-value and decision, and an exact "
        "confidence interval with checked coverage.",
    ),
    "designs.group_sequential": (
        "Adaptive designs",
        "One test repeated at several looks with the error level split across them, "
        "stopping at the first rejection. Lean checks that the split gives the overall "
        "bound; each look's own bound is assumed. Conservative: it ignores the correlation "
        "between looks.",
    ),
    "designs.two_stage": (
        "Adaptive designs",
        "Single-arm two-stage binomial policy with an interim stop, using count thresholds "
        "or Beta-posterior thresholds. Type I error and power are checked for the complete "
        "policy; the error bound covers every rate at or below the null rate. "
        "Designs can be proposed or found by an optimal or minimax search. "
        "Observed counts give a checked decision.",
    ),
}
# Cited method modules describe themselves; adding one needs no edit here.
MODULE_CLASSES.update({group.name: ("Cited analyses", group.summary) for group in METHOD_MODULES})
MODULE_CLASSES.update(
    {
        outcome.module: ("Models and hypotheses", f"{outcome.summary} Fixes no distribution.")
        for outcome in OUTCOMES.values()
    }
)
OBJECT_CLASSES = {
    "Guarantee": (
        "Claims and results",
        "An error-rate statement: quantity, relation, bound, null and scope.",
    ),
    "Model": ("Core statistical objects", "Sampling model and arm sizes."),
    "StudyDesign": ("Core statistical objects", "Model with a stopping rule."),
    "Hypothesis": ("Core statistical objects", "A null restriction, not an assertion of truth."),
    "Analysis": ("Core statistical objects", "Design, compatible null and exact alpha."),
    "OutcomeModel": (
        "Core statistical objects",
        "Two arms with a continuous, survival or other registered outcome.",
    ),
    "OutcomeNull": ("Core statistical objects", "A null restriction for such a model."),
    "CitedAnalysis": (
        "Core statistical objects",
        "Design, null and alpha for a test whose guarantee is cited, not proved.",
    ),
    "Observation": ("Core statistical objects", "Observed counts tied to an analysis."),
    "Family": ("Core statistical objects", "Analyses, family alpha and declared joint law."),
    "Sequential": (
        "Adaptive design objects",
        "Looks at cumulative sample sizes, each with the level spent there.",
    ),
    "ComposedFamily": (
        "Core statistical objects",
        "A family, sequence or graph of analyses and other combinations; the members are assumed.",
    ),
    "Rates": ("Planning objects", "Planning point for two arms; an input, not a fact."),
    "Rate": ("Planning objects", "Planning point for a single response rate."),
    "PowerTarget": ("Planning objects", "Required power at a point and a Type I bound."),
    "Feasibility": ("Planning objects", "One analysis assessed against one target."),
    "Candidates": ("Planning objects", "Finite equal-arm design space for a search."),
    "Sizing": ("Planning objects", "Candidates searched for a design meeting a target."),
    "OneArmModel": ("Core statistical objects", "One arm with a fixed sample size."),
    "OneSampleAnalysis": (
        "Core statistical objects",
        "One-sided exact binomial test with its null rate and alpha.",
    ),
    "OneSampleObservation": (
        "Core statistical objects",
        "Observed responses for a one-sample test.",
    ),
    "DifferenceInterval": (
        "Core statistical objects",
        "Observed two-arm counts and a confidence level.",
    ),
    "Interval": ("Core statistical objects", "Observed count and confidence level."),
    "OneArmCandidates": ("Planning objects", "Sample sizes searched for a one-sample test."),
    "TwoStageModel": ("Adaptive design objects", "Stage sizes of a single-arm design."),
    "TwoStageObservation": (
        "Adaptive design objects",
        "Observed counts, with stage two only if the study continued.",
    ),
    "TwoStageCandidates": (
        "Planning objects",
        "Two-stage designs searched by an optimal or minimax criterion.",
    ),
    "Prior": ("Adaptive design objects", "Beta prior with positive integer parameters."),
    "Rule": ("Adaptive design objects", "Interim continuation and final decision rule."),
    "TwoStageAnalysis": (
        "Adaptive design objects",
        "Complete policy: stages, rule and the null response rate.",
    ),
    "Claim": (
        "Claims and results",
        "Requested typeI, result, familywise or planning proposition.",
    ),
    "VerificationResult": (
        "Claims and results",
        "Explicit verification outcome; optional evidence.",
    ),
    "CalculationResult": ("Claims and results", "Calculation outcome; no proof evidence."),
    "Evidence": ("Evidence and inspection", "Checked properties, assumptions and certificate."),
    "CertificateReference": ("Evidence and inspection", "Certificate identity, path and hash."),
    "CalculationDetails": ("Evidence and inspection", "Exact p-value, alpha and test details."),
    "PlanningDetails": (
        "Evidence and inspection",
        "Calculated sizes, power and target components; not proof evidence.",
    ),
    "OneSampleDetails": (
        "Evidence and inspection",
        "Calculated critical value, error and power of a one-sample test.",
    ),
    "OneSampleResultDetails": (
        "Evidence and inspection",
        "Exact one-sided p-value, critical value and decision.",
    ),
    "DifferenceDetails": (
        "Evidence and inspection",
        "Estimate and interval for a difference of two proportions.",
    ),
    "MarginDetails": (
        "Evidence and inspection",
        "Thresholds, power and decision of an exact difference test.",
    ),
    "IntervalDetails": (
        "Evidence and inspection",
        "Estimate and exact confidence interval endpoints.",
    ),
    "StageResultDetails": (
        "Evidence and inspection",
        "Decision and error bound for observed two-stage counts.",
    ),
    "PolicyDetails": (
        "Evidence and inspection",
        "Calculated error, power and expected sample size of a two-stage policy.",
    ),
    "Diagnostic": ("Evidence and inspection", "A diagnostic code, severity and message."),
}
CLAIM_TYPES = {"TypeIClaim", "ResultClaim", "FamilywiseClaim", "PlanningClaim", "IntervalClaim"}


def catalogue() -> dict:
    """Fail on unclassified registry changes instead of silently omitting new APIs."""
    if set(MODULES) != set(MODULE_CLASSES):
        raise ValueError("Classify every module in catalogue.MODULE_CLASSES")
    schemas = {ValueType(kind).label: fields for kind, fields in SCHEMAS.items()}
    if set(schemas) != set(OBJECT_CLASSES):
        raise ValueError("Classify every public object in catalogue.OBJECT_CLASSES")
    constructors = [c for m in MODULES.values() for c in m.constructors] + list(OPERATIONS.values())
    if any(c.result not in schemas.keys() | CLAIM_TYPES for c in constructors):
        raise ValueError("Classify every constructor result in the catalogue")
    return {
        "objects": [
            {
                "name": name,
                "classification": group,
                "description": description,
                "fields": {
                    field: ValueType(spec.kind, spec.optional).label
                    for field, spec in schemas[name].items()
                },
            }
            for name, (group, description) in OBJECT_CLASSES.items()
        ],
        "modules": [
            {
                "name": name,
                "classification": MODULE_CLASSES[name][0],
                "support": MODULE_CLASSES[name][1],
                "constructors": [_constructor(c) for c in module.constructors],
            }
            for name, module in MODULES.items()
        ],
        "operations": [_constructor(c) for c in OPERATIONS.values()],
        "grammar": GRAMMAR,
        "value_types": VALUE_TYPES,
        "result_statuses": RESULT_STATUSES,
        "program_statuses": PROGRAM_STATUSES,
        "evidence_grades": {
            key: {
                "meaning": grade.label,
                "sources": list(grade.sources),
                "machine_checked": grade.machine_checked,
            }
            for key, grade in GRADES.items()
        },
        "evidence_sources": SOURCES,
        "machine_checks": CHECKS,
        "scopes": SCOPES,
        "assumption_kinds": ASSUMPTION_KINDS,
        "enumerations": ENUMERATIONS,
        "limits": LIMITS,
        "cited_methods": [
            {
                **method.to_dict(),
                "module": method.module,
                "outcome": method.outcome,
                "null": method.null,
                "relation": method.relation,
                "scope": method.scope,
                "assumptions": [item.id for item in method.assumptions],
                "references": list(method.references),
                "minimum_sizes": {"per_arm": method.min_per_arm, "total": method.min_total},
            }
            for method in METHODS.values()
        ],
        "assumptions": [item.to_dict() for item in ASSUMPTIONS.values()],
        "diagnostics": {
            code: {"severity": severity, "meaning": meaning}
            for code, (severity, meaning) in DIAGNOSTICS.items()
        },
    }


def _constructor(constructor) -> dict:
    return {
        "name": constructor.name,
        "signature": constructor.signature,
        "typed_signature": "{}({}) -> {}".format(
            constructor.name,
            ", ".join(
                f"{p.name}{'?' if p.optional else ''}: {ValueType(p.kind).label}"
                for p in constructor.parameters
            ),
            constructor.result,
        ),
        "parameters": {p.name: ValueType(p.kind).label for p in constructor.parameters},
        "optional": [p.name for p in constructor.parameters if p.optional],
        "result": constructor.result,
        "description": constructor.documentation,
        "contract": (
            constructor.hypothesis_contract.to_dict() if constructor.hypothesis_contract else None
        ),
    }


def _table(header: tuple[str, ...], rows) -> list[str]:
    lines = ["| " + " | ".join(header) + " |", "| " + " | ".join("---" for _ in header) + " |"]
    lines += ["| " + " | ".join(str(cell) for cell in row) + " |" for row in rows]
    return [*lines, ""]


def _meanings(title: str, values: dict, name: str = "Value") -> list[str]:
    return [
        f"### {title}",
        "",
        *_table((name, "Meaning"), ((f"`{k}`", v) for k, v in values.items())),
    ]


def render_catalogue() -> str:
    data = catalogue()
    lines = [
        "# Language reference and catalogue",
        "",
        "Generated from the language registries. Update with "
        "`uv run python scripts/update_catalogue.py`; CI checks for drift.",
        "",
        "All APIs are preview APIs. Object availability does not imply a proof adapter. "
        "See [scope](scope.md) for supported guarantees and the "
        "[language guide](stat-language.md) for a walkthrough.",
        "",
        "Contents: [grammar](#grammar), [value types](#value-types), [objects](#objects), "
        "[modules and constructors](#modules), [operations](#built-in-operations), "
        "[statuses and other fixed values](#statuses-and-other-fixed-values), "
        "[cited methods](#cited-methods), [assumptions](#assumptions), [limits](#limits), "
        "[diagnostic codes](#diagnostic-codes).",
        "",
        "## Grammar",
        "",
        "```ebnf",
        data["grammar"].rstrip(),
        "```",
        "",
        "Statements end at a newline; calls and lists may span lines. Names must be declared "
        "before use and cannot be redeclared. There is no arithmetic, no control flow and no "
        "way to run other code.",
        "",
        "## Value types",
        "",
        *_table(("Type", "Meaning"), ((f"`{k}`", v) for k, v in data["value_types"].items())),
        "## Objects",
        "",
        "A field is read with a dot: `analysis.alpha`. Only the fields listed here exist.",
        "",
    ]
    for group in dict.fromkeys(o["classification"] for o in data["objects"]):
        lines += [f"### {group}", "", "| Object | Meaning | Public fields |", "| --- | --- | --- |"]
        for obj in data["objects"]:
            if obj["classification"] == group:
                fields = ", ".join(f"`{n}: {t}`" for n, t in obj["fields"].items())
                lines.append(f"| {obj['name']} | {obj['description']} | {fields} |")
        lines.append("")
    lines += [
        "Claim constructors return `TypeIClaim`, `ResultClaim`, `FamilywiseClaim` or "
        "`PlanningClaim`, "
        "all represented by Claim. Exact numbers, strings, booleans and lists are value types. "
        "Optional evidence stays optional through field access.",
        "",
        "## Modules",
        "",
        "`use` imports built-in constructors; it does not load arbitrary files or plugins. "
        "Arguments may be given by position or by name. A `?` marks an argument that may be "
        "left out.",
        "",
    ]
    for module in data["modules"]:
        lines += [f"### `{module['name']}` — {module['classification']}", "", module["support"], ""]
        for c in module["constructors"]:
            lines.append(f"- `{c['typed_signature']}`")
            if c["description"]:
                lines.append(f"  {c['description']}")
            if c["contract"]:
                lines.append(
                    f"  Required null: {c['contract']['expected_null']}; same model required."
                )
        lines.append("")
    lines += ["## Built-in operations", ""]
    lines += [f"- `{c['typed_signature']}`" for c in data["operations"]]
    lines += [
        "",
        "Verification and calculation run only on explicit execution; the editor plans them. "
        "Compilation cannot create evidence.",
        "",
        "## Statuses and other fixed values",
        "",
        *_meanings("Result status (`result.status`)", data["result_statuses"], "Status"),
        *_meanings("File status (`Program status`)", data["program_statuses"], "Status"),
        "### Evidence grade (`evidence.grade`)",
        "",
        *_table(
            ("Grade", "Meaning", "`evidence.sources`", "`evidence.machine_checked`"),
            (
                (
                    f"`{k}`",
                    g["meaning"],
                    ", ".join(f"`{s}`" for s in g["sources"]),
                    f"`{g['machine_checked']}`",
                )
                for k, g in data["evidence_grades"].items()
            ),
        ),
        *_meanings("Evidence source", data["evidence_sources"]),
        *_meanings("What a machine checked", data["machine_checks"]),
        *_meanings("Guarantee scope (`claim.scope`)", data["scopes"]),
        *_meanings("Assumption kind", data["assumption_kinds"], "Kind"),
    ]
    for title, values in data["enumerations"].items():
        lines += _meanings(f"`{title}`", values)
    lines += [
        "## Cited methods",
        "",
        "Guarantees taken from the literature. See [cited methods](cited-methods.md).",
        "",
        *_table(
            ("Constructor", "Version", "Outcome", "Null", "Error rate", "Scope", "Minimum size"),
            (
                (
                    f"`{m['key']}`",
                    m["version"],
                    m["outcome"],
                    f"`{m['null']}`",
                    "equals alpha" if m["relation"] == "equals" else "at most alpha",
                    f"`{m['scope']}`",
                    f"{m['minimum_sizes']['per_arm']} per arm, {m['minimum_sizes']['total']} total",
                )
                for m in data["cited_methods"]
            ),
        ),
    ]
    for m in data["cited_methods"]:
        lines += [
            f"**`{m['key']}`** ({m['title']}) assumes "
            + ", ".join(f"`{a}`" for a in m["assumptions"])
            + ". References:",
            "",
            *[f"- {reference}" for reference in m["references"]],
            "",
        ]
    lines += [
        "## Assumptions",
        "",
        "Assumptions of the cited methods and of combinations, by id. The exact modules' "
        "assumptions are classified in `methods/identify.py`.",
        "",
        *_table(
            ("Id", "Kind", "Text"),
            ((f"`{a['id']}`", a["kind"], a["text"]) for a in data["assumptions"]),
        ),
        "## Limits",
        "",
        *_table(("Quantity", "Supported"), data["limits"].items()),
        "## Diagnostic codes",
        "",
        "An `error` makes the file invalid. An `obligation` leaves a claim unresolved; it "
        "is never a finding that the claim is false.",
        "",
        *_table(
            ("Code", "Severity", "Reported when"),
            ((f"`{k}`", d["severity"], d["meaning"]) for k, d in data["diagnostics"].items()),
        ),
        "## Lean library concepts",
        "",
        "The formal library also defines parameter domains, procedures, guarantees and "
        "composition rules. These are not all standalone `.stat` constructors yet. "
        "See [core object model](core-object-model.md) and [Lean objects](lean-objects.md).",
        "",
        "The same content is available in machine-readable form from "
        "`statclaim catalogue --json`. See [adding modules](adding-modules.md).",
        "",
    ]
    return "\n".join(lines)
