"""Classified public inventory; signatures and fields come from live registries."""

from statproof.language import MODULES, OPERATIONS, ValueType
from statproof.language_fields import SCHEMAS

MODULE_CLASSES = {
    "models.two_arm_binomial": (
        "Models and hypotheses",
        "Two independent binomial arms; equality, difference and inequality null descriptions. "
        "Only equality has a current Fisher proof adapter.",
    ),
    "sampling": (
        "Study designs",
        "Fixed sampling is supported. Adaptive sampling is descriptive; its current "
        "Type I error requirement remains unresolved.",
    ),
    "tests.fisher": (
        "Analyses and claims",
        "Two-sided Fisher calculation and Lean-backed result/Type I claims for the "
        "equality null with fixed sampling.",
    ),
    "multiplicity.bonferroni": (
        "Multiplicity and composition",
        "Bonferroni for two or more Fisher endpoints with an explicit joint-law contract. "
        "Dependence between endpoints is unrestricted.",
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
    "designs.two_stage": (
        "Adaptive designs",
        "Single-arm two-stage binomial policy with an interim stop, using count thresholds "
        "or Beta-posterior thresholds. Type I error and power are checked for the complete "
        "policy; the error bound covers every rate at or below the null rate. "
        "Designs can be proposed or found by an optimal or minimax search. "
        "Observed counts give a checked decision.",
    ),
}
OBJECT_CLASSES = {
    "Model": ("Core statistical objects", "Sampling model and arm sizes."),
    "StudyDesign": ("Core statistical objects", "Model with a stopping rule."),
    "Hypothesis": ("Core statistical objects", "A null restriction, not an assertion of truth."),
    "Analysis": ("Core statistical objects", "Design, compatible null and exact alpha."),
    "Observation": ("Core statistical objects", "Observed counts tied to an analysis."),
    "Family": ("Core statistical objects", "Analyses, family alpha and declared joint law."),
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
    }


def _constructor(constructor) -> dict:
    return {
        "name": constructor.name,
        "signature": constructor.signature,
        "parameters": {p.name: ValueType(p.kind).label for p in constructor.parameters},
        "result": constructor.result,
        "description": constructor.documentation,
        "contract": (
            constructor.hypothesis_contract.to_dict() if constructor.hypothesis_contract else None
        ),
    }


def render_catalogue() -> str:
    data = catalogue()
    lines = [
        "# Object and module catalogue",
        "",
        "Generated from the language registries. Update with "
        "`uv run python scripts/update_catalogue.py`; CI checks for drift.",
        "",
        "All APIs are preview APIs. Object availability does not imply a proof adapter. "
        "See [scope](scope.md) for supported guarantees.",
        "",
    ]
    for group in dict.fromkeys(o["classification"] for o in data["objects"]):
        lines += [f"## {group}", "", "| Object | Meaning | Public fields |", "| --- | --- | --- |"]
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
        "`use` imports built-in constructors; it does not load arbitrary files or plugins.",
        "",
    ]
    for module in data["modules"]:
        lines += [f"### `{module['name']}` — {module['classification']}", "", module["support"], ""]
        for c in module["constructors"]:
            lines.append(f"- `{c['signature']}`")
            if c["contract"]:
                lines.append(
                    f"  Required null: {c['contract']['expected_null']}; same model required."
                )
        lines.append("")
    lines += ["## Built-in operations", ""]
    lines += [f"- `{c['signature']}`" for c in data["operations"]]
    lines += [
        "",
        "Verification and calculation run only on explicit execution; the editor plans them. "
        "Compilation cannot create evidence.",
        "",
        "## Lean library concepts",
        "",
        "The formal library also defines parameter domains, procedures, guarantees and "
        "composition rules. These are not all standalone `.stat` constructors yet. "
        "See [core object model](core-object-model.md) and [Lean objects](lean-objects.md).",
        "",
        "For typed parameters and contracts in machine-readable form, run "
        "`statproof catalogue --json`. See [adding modules](adding-modules.md).",
        "",
    ]
    return "\n".join(lines)
