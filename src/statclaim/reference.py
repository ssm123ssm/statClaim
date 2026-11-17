"""Closed vocabularies of the language: statuses, diagnostic codes, limits, grammar.

Everything here is data for the generated reference (docs/catalogue.md). Tests
keep it in step with the code: every diagnostic code raised anywhere must be
listed, and the grammar's examples are run through the real parser.
"""

from statclaim.composition import MAX_MEMBERS
from statclaim.planning import (
    CRITERIA,
    MAX_CITED_ARM,
    MAX_MARGIN_ARM,
    MAX_ONE_ARM,
    MAX_PER_ARM,
    MAX_RATIO,
    MAX_SEARCH_TOTAL,
    MAX_STAGE,
)

GRAMMAR = """\
file        = { statement NEWLINE } ;
statement   = "use" module
            | "let" NAME "=" expression
            | operation ;                      (* only verify and calculate *)
operation   = ( "verify" | "calculate" ) "(" expression ")"
            | ( "verify" | "calculate" ) expression ;      (* older spelling *)
module      = NAME { "." NAME } ;
expression  = primary { "." NAME } ;           (* field access *)
primary     = NAME                             (* a name declared earlier *)
            | NAME "(" [ arguments ] ")"       (* constructor call *)
            | "[" [ expression { "," expression } [ "," ] ] "]"
            | NUMBER | STRING ;
arguments   = argument { "," argument } [ "," ] ;
argument    = [ NAME "=" ] expression ;        (* positional before named *)
NUMBER      = [ "-" ] DIGITS [ "." DIGITS ]    (* exact decimal *)
            | [ "-" ] DIGITS "/" DIGITS ;      (* exact fraction *)
STRING      = '"' { character } '"' ;          (* JSON escapes *)
NAME        = ( letter | "_" ) { letter | digit | "_" } ;   (* ASCII *)
comment     = "#" to the end of the line ;
"""
# Each line must parse; the test also checks that the rejected ones are rejected.
GRAMMAR_ACCEPTS = (
    "use models.two_arm_binomial",
    "let study = two_arm_binomial(n_control=100, n_treatment=100)",
    "let study = two_arm_binomial(100, n_treatment=100)",
    "let level = 0.025",
    "let level = 1/40",
    "let shift = mean_difference_at_most(model=study, value=-2)",
    'let family = bonferroni(analyses=[a, b,], alpha=1/20, joint_law="binomial_marginals",)',
    "let file = verify(claim).evidence.certificate.file",
    "verify(typeI(analysis))",
    "verify typeI(analysis)",
    "let x = f(  # a comment inside a call\n    1,\n)",
)
GRAMMAR_REJECTS = (
    "let x = 1 + 2",
    "let x = f(a=1, 2)",
    "x = 1",
    "let x = 1;",
    "let x = 1/0",
    "let 1x = 2",
    "typeI(analysis)",
)

VALUE_TYPES = {
    "integer": "A whole number, such as `100`.",
    "exact number": "An exact decimal or fraction: `0.025` and `1/40` are the same value. "
    "Never a floating-point approximation.",
    "level": "An exact number between 0 and 1, used for alpha and confidence levels. "
    "Some tests require it strictly inside.",
    "string": 'Text in double quotes, such as `"binomial_marginals"`.',
    "boolean": "`true` or `false`; appears in results only.",
    "list": "Items in square brackets. Family members and looks must be named analyses.",
    "Option[T]": "A value that may be absent, such as evidence after a failed check. "
    "Reading a field of an absent value gives an absent value.",
}

RESULT_STATUSES = {
    "verified": "Lean proved the guarantee. Evidence grade `proved`.",
    "conditional": "Lean proved how the parts combine; each part's own guarantee is assumed. "
    "Evidence grade `conditional`.",
    "cited": "The study fits a published method's contract; the guarantee is cited, not "
    "machine-checked. Evidence grade `cited`.",
    "declared": "The author named and vouched for the test or one of its parts. Nothing "
    "about that guarantee was checked or cited. Evidence grade `declared`.",
    "calculated": "A `calculate` request produced numbers. No evidence.",
    "unresolved_obligation": "A requirement is unmet or a target is missed. No evidence. "
    "Not a finding that the claim is false.",
    "backend_error": "Lean could not be run or failed for a technical reason. No evidence.",
    "not_executed": "The request was planned by `compile` and has not been run.",
}
PROGRAM_STATUSES = {
    "invalid": "The file has an error and nothing was run.",
    "elaborated": "The file compiles with no open requirement; nothing was run.",
    "unresolved_obligation": "At least one claim has an unmet requirement.",
    "declared": "Every claim went through; the weakest part anywhere is a declared test.",
    "cited": "Every claim went through; the weakest part anywhere is cited.",
    "conditional": "Every claim went through; the weakest part is a proved combination "
    "of tests that are themselves provable.",
    "verified": "Every verified claim was proved; calculations may also be present.",
    "calculated": "Only calculations were requested.",
    "stale_source": "The file changed while it was being checked. Run it again.",
}
ENUMERATIONS = {
    "Claim.kind": {
        "typeI": "Type I error of an analysis or a sequential design.",
        "familywise": "Familywise error of a family.",
        "result": "The p-value and decision for observed data.",
        "meets": "A design meets a power and Type I target.",
        "sample_size": "Some, or the smallest, size in a range meets a target.",
        "interval": "A confidence interval and its coverage.",
    },
    "StudyDesign.stopping": {
        "fixed": "From `fixed(...)`: sizes set in advance, one analysis.",
        "data_dependent": "From `adaptive(...)`: leaves error claims unresolved.",
    },
    "bonferroni joint_law": {
        "binomial_marginals": "The only value, and the default. Allowed only when every "
        "member is a two-sided Fisher analysis; leave it out otherwise.",
    },
    "two_stage_candidates criterion": dict.fromkeys(
        CRITERIA, "Ranking used by the two-stage design search."
    ),
    "Diagnostic.severity": {
        "error": "The file is invalid.",
        "obligation": "A requirement is open; the file is valid.",
    },
    "Assumption status": {
        "declared": "The file itself states it.",
        "assumed": "Nothing in the file can show it.",
        "condition": "Says which null or planning point the claim is about.",
    },
}
LIMITS = {
    "Analyses in a family, or looks in a sequential design": f"2 to {MAX_MEMBERS}",
    "Participants per arm, exact test with a margin": f"up to {MAX_MARGIN_ARM}",
    "Participants per arm, Fisher planning search": f"up to {MAX_PER_ARM}",
    "Participants per arm, cited-test planning search": f"up to {MAX_CITED_ARM}",
    "Allocation ratio in a planning search": f"1 to {MAX_RATIO}",
    "Participants, one-sample binomial test": f"up to {MAX_ONE_ARM}",
    "Participants per stage, two-stage design": f"up to {MAX_STAGE}",
    "Total participants, two-stage design search": f"up to {MAX_SEARCH_TOTAL}",
}

# code: (severity, when it is reported)
DIAGNOSTICS = {
    # Reading the file
    "syntax": ("error", "The text does not follow the grammar."),
    "number": ("error", "A number is malformed or has a zero denominator."),
    "string": ("error", "A string is unterminated or has a bad escape."),
    "name": ("error", "A name is not an ASCII identifier."),
    "depth": ("error", "An expression is nested too deeply."),
    # Names and modules
    "unknown_module": ("error", "`use` names a module that does not exist."),
    "module_conflict": ("error", "Two loaded modules define the same constructor."),
    "unknown_constructor": (
        "error",
        "A call names no loaded constructor; the hint names the module to `use`.",
    ),
    "unknown_name": ("error", "A name is used before it is declared."),
    "redefinition": ("error", "A name is declared twice; bindings are immutable."),
    "reserved_name": ("error", "A binding uses the name of a built-in operation."),
    "dependency": ("error", "A declaration depends on one that failed."),
    # Calls and values
    "arguments": ("error", "An argument is missing, unknown, repeated or surplus."),
    "type": ("error", "An argument has the wrong type, or belongs to another kind of outcome."),
    "domain": ("error", "A value is outside its allowed range."),
    "unknown_field": ("error", "An object has no public field of that name."),
    "absent_value": ("error", "A field is read from a value that is absent."),
    "runtime_dependency": (
        "error",
        "A constructor is given a value that exists only after execution.",
    ),
    "unsupported_claim": ("error", "The claim cannot be used with this operation."),
    # Statistical contracts
    "model_mismatch": ("error", "The design and the null are declared over different models."),
    "hypothesis_mismatch": (
        "error",
        "The test does not support the declared null. Not a finding that the null is false.",
    ),
    "alternative_in_null": ("error", "The planning point lies inside the null."),
    "no_power_formula": ("error", "A cited or declared test with no power formula is planned."),
    "planning_point": ("error", "The planning point does not fit the analysis."),
    "rule_mismatch": ("error", "A stopping rule does not fit the two-stage design."),
    "sampling_contract": ("error", "A joint law is given where none applies, or is not supported."),
    "family_size": ("error", "A family or sequential design has too few or too many entries."),
    "duplicate_analysis": ("error", "A family or sequential design lists an analysis twice."),
    "sequential_question": ("error", "The looks of a sequential design differ in test or null."),
    "sequence_level": (
        "error",
        "A test in a fixed sequence or a graph is not declared at the overall level.",
    ),
    "graph_definition": ("error", "The weights or transitions of a graph are not valid."),
    "sequential_order": ("error", "The looks are not in order of growing sample size."),
    # Open requirements
    "sampling_scope": (
        "obligation",
        "The design stops on the data, which the guarantee does "
        "not cover. Not evidence of inflated error.",
    ),
    "allocation": ("obligation", "The members' levels sum to more than the overall level."),
    "typeI_target_not_established": (
        "obligation",
        "The analysis's level exceeds the requested Type I bound.",
    ),
    "typeI_target_not_met": ("obligation", "The calculated Type I error exceeds the target."),
    "power_target_not_met": ("obligation", "The calculated power is below the target."),
    "no_feasible_candidate": ("obligation", "No design in the searched range meets the target."),
    "verification": ("obligation", "Lean could not establish the claim; the message says why."),
    "source_changed": ("obligation", "The file changed while it was being checked."),
    "snapshot_changed": ("obligation", "The retained copy of the file changed during the run."),
}
