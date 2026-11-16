"""The vocabulary every method is written in: assumptions, guarantees and grades.

Nothing here depends on the language, the compiler or Lean, so a method file can
be read and reviewed on its own.
"""

from dataclasses import dataclass
from fractions import Fraction

# How a guarantee was established. A grade is shorthand for two separate facts:
# where the guarantee's statement comes from, and how far a machine checked it.
SOURCES = {
    "lean_proof": "a proof in Lean",
    "literature": "a published result",
    "member_guarantees": "the members' own guarantees, each proved or cited separately",
    "simulation": "a simulation",
}
CHECKS = {
    "guarantee": "Lean checked the guarantee itself",
    "composition": "Lean checked how the parts combine, not the parts",
    "contract": "only the fit between the study and the method's contract was checked",
}


@dataclass(frozen=True)
class Grade:
    label: str
    sources: tuple[str, ...]
    machine_checked: str


GRADES = {
    "proved": Grade("proved in Lean", ("lean_proof",), "guarantee"),
    "conditional": Grade(
        "combination proved in Lean; the members' own guarantees are assumed",
        ("lean_proof", "member_guarantees"),
        "composition",
    ),
    "cited": Grade("cited from the literature; not machine-checked", ("literature",), "contract"),
    "simulated": Grade("estimated by simulation; not a proof", ("simulation",), "contract"),
}
# What kind of statement a guarantee is. An approximation is never shown as a bound.
SCOPES = {
    "finite_sample": "finite-sample bound",
    "asymptotic": "large-sample approximation",
}
ASSUMPTION_KINDS = {
    "design": "About the study plan. Compared with the declared design where possible.",
    "sampling": "About how observations arise. Not checkable from a declaration.",
    "distribution": "About the outcome's distribution. Not checkable from a declaration.",
    "member": "A member test's own error bound, relied on when tests are combined.",
}


@dataclass(frozen=True)
class Assumption:
    """One condition a guarantee rests on. The id is stable; the text may be reworded."""

    id: str
    kind: str
    text: str

    def __post_init__(self):
        if self.kind not in ASSUMPTION_KINDS:
            raise ValueError(f"Unknown assumption kind {self.kind!r}.")

    def to_dict(self) -> dict:
        return {"id": self.id, "kind": self.kind, "text": self.text}


@dataclass(frozen=True)
class Guarantee:
    """A statement about an error rate: which rate, how it is bounded, and where."""

    quantity: str  # "type_I_error" or "familywise_error"
    relation: str  # "equals" or "at_most"
    bound: Fraction
    null: str
    scope: str  # a key of SCOPES
    # For a large-sample guarantee: what has to grow for it to become exact.
    limit: str = "the sample sizes grow"

    def __post_init__(self):
        if self.relation not in ("equals", "at_most") or self.scope not in SCOPES:
            raise ValueError("Unknown guarantee relation or scope.")

    @property
    def sentence(self) -> str:
        """Exact and approximate guarantees are always worded differently."""
        name = {
            "type_I_error": "Null rejection probability",
            "familywise_error": "Probability of rejecting any true member null",
        }[self.quantity]
        if self.scope == "finite_sample":
            relation = "equals" if self.relation == "equals" else "is at most"
            return f"{name} {relation} {self.bound} whenever {self.null}."
        relation = "approaches" if self.relation == "equals" else "is at most"
        return (
            f"{name} {relation} {self.bound} in the limit as {self.limit}, "
            f"whenever {self.null}. No bound is claimed at the declared sample sizes."
        )

    def to_dict(self) -> dict:
        return {
            "quantity": self.quantity,
            "relation": self.relation,
            "bound": str(self.bound),
            "null": self.null,
            "scope": self.scope,
            **({"limit": self.limit} if self.scope == "asymptotic" else {}),
        }


@dataclass(frozen=True)
class NullForm:
    """One form a null hypothesis can take for an outcome, such as equal means."""

    key: str  # the constructor's name in .stat files
    statement: str  # may contain {value} when the null takes a number
    documentation: str
    takes_value: bool = False

    def state(self, value: Fraction) -> str:
        return self.statement.format(value=value)


@dataclass(frozen=True)
class Outcome:
    """A kind of two-arm outcome, with the nulls that can be stated about it.

    The model fixes no distribution; each method states the one it assumes.
    """

    key: str  # "continuous", "survival"
    module: str  # the module a file loads with `use`
    constructor: str  # the model's constructor name
    summary: str  # one line for the catalogue
    documentation: str
    nulls: tuple[NullForm, ...]


@dataclass(frozen=True)
class CitedMethod:
    """A test whose guarantee is taken from the literature, not proved in Lean.

    Bump `version` whenever the guarantee, assumptions, references or limits
    change; `tests/fixtures/method_versions.json` enforces this.
    """

    key: str  # the constructor's name in .stat files
    module: str  # the module a file loads with `use`
    title: str
    version: int
    outcome: str  # the Outcome this test applies to
    null: str  # the one null form of that outcome the test supports
    relation: str  # how the error rate relates to alpha: "equals" or "at_most"
    scope: str
    assumptions: tuple[Assumption, ...]
    references: tuple[str, ...]
    min_per_arm: int
    min_total: int
    # For a large-sample guarantee: what has to grow for it to become exact.
    limit: str = "the sample sizes grow"

    def guarantee(self, alpha: Fraction, null: str) -> Guarantee:
        return Guarantee("type_I_error", self.relation, alpha, null, self.scope, self.limit)

    def to_dict(self) -> dict:
        return {"key": self.key, "version": self.version, "title": self.title}


@dataclass(frozen=True)
class MethodModule:
    """What a method file exports: a module name, its summary and its methods."""

    name: str
    summary: str
    methods: tuple[CitedMethod, ...]
