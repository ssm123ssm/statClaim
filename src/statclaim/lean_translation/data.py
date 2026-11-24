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

from statclaim.lean_translation.emit import rational
from statclaim.methods import METHODS, NULL_FORMS, OUTCOMES

SEMANTICS = "StatClaim.Semantics"
MARKER = "STATCLAIM_PROGRAM"
GRADES = "STATCLAIM_GRADES"
# The model constructor each outcome kind's module names, as the canonical program writes it.
MODULES = {outcome.constructor: key for key, outcome in OUTCOMES.items()}
STOPPING = ("fixed", "data_dependent")
COMBINATIONS = {"bonferroni": "bonferroni", "graphical": "graphical", "fixed_sequence": "sequence"}
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


class Outside(Exception):
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


def test(name: object, value: object) -> str:
    """A test or combination, named as its declaration is."""
    label = string(name)
    if isinstance(value, dict) and "analyses" in value:
        method = value["method"]
        if method not in COMBINATIONS:
            raise Outside(f"The combination {method!r} is not in the semantics yet.")
        extra = {"weights", "transitions"} if method == "graphical" else set()
        record = fields(
            value, {"method", "composition", "alpha", "analyses", *extra}, "A combination"
        )
        if record["composition"] != "conditional" or not isinstance(record["analyses"], list):
            raise Outside("A combination is not a conditional combination of analyses.")
        members = []
        for entry in record["analyses"]:
            member = fields(entry, {"name", "analysis"}, "A member")
            members.append(test(member["name"], member["analysis"]))
        listed = "[" + ",\n    ".join(members) + "]"
        if method == "graphical":
            weights = [exact(w, "A weight") for w in record["weights"]]
            rows = [[exact(t, "A transition") for t in row] for row in record["transitions"]]
            shares = (
                "["
                + ", ".join(weights)
                + "] ["
                + ", ".join("[" + ", ".join(row) + "]" for row in rows)
                + "]"
            )
            return f".graphical {label}\n    {listed}\n    {shares} {level(record['alpha'])}"
        return f".{COMBINATIONS[method]} {label}\n    {listed}\n    {level(record['alpha'])}"
    declared = isinstance(value, dict) and value.get("test") == DECLARED
    record = fields(value, ANALYSIS | (DECLARED_FIELDS if declared else set()), "An analysis")
    parts = (
        f"{design(record['design'])}\n      {null(record['null'])}\n      {level(record['alpha'])}"
    )
    if record["test"] == "fisher":
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
    cited = METHODS.get(record["test"])
    if cited is None or cited.grade != "cited":
        raise Outside(f"The test {record['test']!r} is not in the semantics yet.")
    return f".assumed {label} (.cited StatClaim.Generated.Methods.{cited.key})\n      {parts}"


def verify_claims(program: dict) -> list:
    """The claims of a canonical program's `verify` requests, in order: what Lean prints."""
    return [request["claim"] for request in program["requests"] if request["operation"] == "verify"]


def program_data(program: dict) -> str:
    """The Lean definition of `program`, or `Outside` when the semantics does not cover it."""
    requests = []
    for claim in verify_claims(program):
        record = fields(claim, {"kind", "subject_name", "subject"}, "A claim")
        if record["kind"] not in ("typeI", "familywise"):
            raise Outside(f"Claims of kind {record['kind']!r} are not in the semantics yet.")
        requests.append(f".{record['kind']} ({test(record['subject_name'], record['subject'])})")
    if not requests:
        raise Outside("The program asks Lean for no claim.")
    body = ",\n  ".join(requests)
    return f"def program : {SEMANTICS}.Program := ⟨[\n  {body}]⟩\n"


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


def claims(program: dict) -> str:
    """The theorems proving each claim that has a sampling law, by the semantics'
    soundness theorem and the program's contracts."""
    lines = ["theorem contracts : program.Contracts := by decide +kernel", ""]
    for index, claim in enumerate(verify_claims(program)):
        if fixed(claim["subject"]):
            lines.append(
                f"theorem claim_{index} : program.Claim {index} :=\n"
                f"  {SEMANTICS}.Program.sound program contracts {index} (by decide +kernel)"
            )
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


def printed(output: str, label: str) -> list | None:
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


def binding_problem(output: str, label: str, program: dict) -> str | None:
    """Why the data Lean read is not the canonical program, or None when it is."""
    found = printed(output, label)
    if found is None:
        return f"Lean printed no canonical form for {label}."
    expected = verify_claims(program)
    if found != expected:
        return f"The data Lean read for {label} is not its canonical program."
    return None
