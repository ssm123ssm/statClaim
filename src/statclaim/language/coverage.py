"""What gives each constructor its meaning in Lean, or why nothing does.

Every constructor states its entry where it is defined (`Constructor.lean`), and
lean_translation/table.py collects them.
"""

from dataclasses import dataclass

ROLES = {
    "model": "A study model or a part of one: arms, outcome, assignment, strata.",
    "design": "A sampling plan or a stopping rule.",
    "null": "A null hypothesis, as a predicate on the model's parameters.",
    "analysis": "A test whose guarantee a Lean module proves.",
    "premise": "A test whose guarantee enters as a named premise, cited or declared.",
    "composition": "A rule combining the members' guarantees, proved in Lean or cited.",
    "claim": "A proposition the program states.",
    "data": "Observed data, checked against the model's outcome domain.",
    "planning": "A planning input; it has a Lean meaning when its analysis is exact.",
    "operation": "A request for evidence.",
}

# Lean files the table may name before they exist.
PLANNED: tuple[str, ...] = ()


@dataclass(frozen=True)
class InLean:
    role: str
    lean: tuple[str, ...]  # the Lean files, from the repository root, that give it meaning


@dataclass(frozen=True)
class NotInLean:
    reason: str


def in_lean(role: str, *files: str) -> InLean:
    return InLean(role, tuple(f"StatClaim/{name}.lean" for name in files))


CORE = "Core/Objects"
POLICY = "Core/Policy"
OUTCOME_LAWS = "Interface/Outcomes"
PREMISES = "Interface/Premises"
PROGRAM = "Semantics/Meaning"
RESULTS = "Semantics/Results"
INTERVALS = "Semantics/Intervals"
PLANS = "Semantics/Plans"
METHODS = "Generated/Methods"
BINOMIAL = "Modules/TwoArmBinomial"
RANDOMISATION = "Modules/Randomisation"
ASSOCIATION = "Modules/Association"
INCIDENCE = "Modules/Incidence"
MATCHED = "Modules/Matched"
INTERVAL = "Modules/BinomialInterval"
ONE_SAMPLE = "Modules/OneSampleBinomial"
TWO_STAGE = "Modules/TwoStageBinomial"
COMPOSITION = "Modules/Composition"

# The guarantee of every cited test enters as a premise generated from the method registry.
CITED = in_lean("premise", METHODS, PREMISES)

APPROXIMATE = NotInLean(
    "A planning point for an approximate power formula or a simulation; its results are "
    "calculated or simulated, never proved."
)
PRECISION = NotInLean("Precision searches are calculations; Lean does not check them.")
