"""The compatibility certificate of a whole program: milestone 6 of
docs/proposals/lean-translation.md, stated through the semantics of compiled programs
where it covers the program (docs/proposals/lean-semantics.md).

Its inputs are the source and the canonical program it compiles to. Its proof ends with
the audit `verify` certificates end with: every contract fact and claim is a theorem
that uses no axiom beyond Lean's three, and the completion marker is bound to these
inputs. `verification.py` builds and replays it like every other certificate.

A program the semantics covers is written as Lean data (`data.py`). Its contracts are
decided by `decide +kernel`, each claim is `program.Claim r`, proved by the soundness
theorem, and Lean prints the data's canonical form and each claim's grade: the canonical
form must be the certificate's program, and each grade the one `data.grade` reports,
when the certificate is issued and whenever it is checked again. Any other program is
stated by the translation, and Lean lists the premises each claim's proof uses; the
grades they give must be the ones the translation states.

Result binding (trusted): `claims` maps each claim to the request and source line it
comes from.
"""

import re

from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source
from statclaim.lean_translation import data
from statclaim.lean_translation.denote import Denotation, denote
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.grades import grade
from statclaim.lean_translation.program import render
from statclaim.planning import AUDIT

KIND = "statclaim_program_certificate"
# Bump when the meaning of a translation changes, so older certificates are not replayed
# against a different translator. 2: programs the semantics covers are stated through it.
TRANSLATION_VERSION = 2
NAMESPACE = "StatClaimProgram"
# The collector's name for the program; one certificate holds one program.
LABEL = "program"
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


class Unchecked(ValueError):
    """A program that has no compatibility certificate: it does not compile, or its
    inputs no longer match."""


def payload(source: Source) -> dict:
    """The certificate's inputs: the source, and the canonical program it compiles to."""
    compilation = compile_source(source)
    if compilation.status == "invalid":
        raise Unchecked("The program does not compile, so Lean is not asked about it.")
    return {
        "translation_version": TRANSLATION_VERSION,
        "source": {"path": source.path, "text": source.text},
        "program": compilation.program.to_dict(),
    }


def checked(inputs: dict):
    """The compiled program, after checking that the inputs come from this translator and
    that their source still compiles to the canonical program they record."""
    if inputs.get("translation_version") != TRANSLATION_VERSION:
        raise Unchecked("The certificate was made by another version of the translator.")
    source = Source(inputs["source"]["text"], inputs["source"]["path"])
    compilation = compile_source(source)
    if compilation.status == "invalid" or compilation.program.to_dict() != inputs["program"]:
        raise Unchecked("The source no longer compiles to the program the inputs record.")
    return compilation.program


def semantic(inputs: dict) -> str | None:
    """The program as Lean data, when the semantics covers it; otherwise None."""
    checked(inputs)
    if inputs.get("omitted"):
        return None  # only a translation leaves claims out
    try:
        return data.program_data(inputs["program"])
    except data.Outside:
        return None


def denotation(inputs: dict) -> Denotation:
    """What the program states in Lean, after checking that its source still compiles to
    the canonical program the inputs record."""
    stated = denote(checked(inputs))
    # Claims Lean did not prove when the certificate was first built are left out of it,
    # and the inputs say which: the rest of the program is still certified.
    omitted = set(inputs.get("omitted", []))
    if not omitted <= {claim.name for claim in stated.claims}:
        raise Unchecked("The inputs omit a claim the program does not state.")
    stated.claims = [claim for claim in stated.claims if claim.name not in omitted]
    return stated


def failing_claims(proof_text: str, output: str, stated: Denotation) -> set[str] | None:
    """The claims whose proofs Lean rejected, from its errors in Proof.lean, or None when
    an error lies outside every claim: then the declarations themselves failed. Under the
    semantics a claim with a sampling law cannot fail alone, so any error is the
    program's."""
    from statclaim.lean_translation.rejection import owners

    if f"{data.SEMANTICS}.Program.sound" in proof_text:
        return None
    lines = proof_text.splitlines()
    end = lines.index(f"end {NAMESPACE}") + 1 if f"end {NAMESPACE}" in lines else len(lines)
    found = owners(proof_text)
    names = {lean(claim.name): claim.name for claim in stated.claims}
    failing: set[str] = set()
    for line in output.splitlines():
        match = re.search(r"Proof\.lean:(\d+):\d+: error", line)
        if not match or int(match.group(1)) > end:
            continue  # the audit after the program fails whenever a claim does
        space, declaration = found[int(match.group(1)) - 1]
        inner = space.removeprefix(NAMESPACE).removeprefix(".")
        claim = next(
            (name for lean_name, name in names.items() if declaration == lean_name),
            next(
                (name for lean_name, name in names.items() if inner.startswith(f"{lean_name}_")),
                None,
            ),
        )
        if claim is None:
            return None
        failing.add(claim)
    return failing


def theorems(stated: Denotation) -> list[str]:
    """Every theorem the audit checks: contract facts, claims and the program theorem."""
    names = [lean(fact.name) for fact in stated.contracts if fact.check != "comment"]
    names += [lean(claim.name) for claim in stated.claims]
    return [*names, "program"]


def semantic_theorems(inputs: dict) -> list[str]:
    """Under the semantics: the contracts, and each claim that has a sampling law."""
    return ["contracts", *(claim["theorem"].rsplit(".", 1)[1] for claim in claims(inputs))]


def proof(inputs: dict, input_sha256: str) -> str:
    """Proof.lean: the translation, then the audit bound to these inputs."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    program = semantic(inputs)
    if program is not None:
        body = "\n".join([program, data.claims(inputs["program"]), data.report(LABEL)])
        audited = semantic_theorems(inputs)
    else:
        stated = denotation(inputs)
        body, audited = render(stated, LABEL), theorems(stated)
    names = ",\n    ".join(f"``{NAMESPACE}.{name}" for name in audited)
    return "\n".join(
        [
            "import StatClaim",
            "import Lean.Util.CollectAxioms",
            "",
            f"-- Canonical program SHA-256: {input_sha256}",
            f"namespace {NAMESPACE}",
            "",
            body.rstrip(),
            "",
            f"end {NAMESPACE}",
            AUDIT.format(names=names, input_sha256=input_sha256),
        ]
    )


def used_premises(output: str) -> dict[str, list[str]]:
    """The premises Lean lists for each claim's proof."""
    used = {}
    for line in output.splitlines():
        found = re.search(rf"STATCLAIM_PREMISES {LABEL} (\S+): (.*)$", line)
        if found:
            used[found.group(1)] = [name for name in found.group(2).strip().split(",") if name]
    return used


def check_grades(inputs: dict, output: str) -> None:
    """Fail unless each claim's grade, from the premises Lean lists for its proof, is the
    grade the translation states. Under the semantics: fail unless the data Lean read is
    the certificate's program, and each claim's grade in Lean is the one reported."""
    if semantic(inputs) is not None:
        problem = data.binding_problem(output, LABEL, inputs["program"])
        if problem is not None:
            raise Unchecked(problem)
        grades = data.printed_grades(output, LABEL)
        if grades is None:
            raise Unchecked("Lean printed no grades for the program.")
        for listed in claims(inputs):
            index = int(listed["theorem"].rsplit("_", 1)[1])
            if index >= len(grades) or grades[index] != listed["grade"]:
                raise Unchecked(f"{listed['claim']}: Lean's grade differs from {listed['grade']}.")
        return
    used = used_premises(output)
    for claim in denotation(inputs).claims:
        if claim.name not in used:
            raise Unchecked(f"Lean listed no premises for {claim.name}.")
        found = grade(claim.own, used[claim.name])
        if found != claim.grade:
            raise Unchecked(
                f"{claim.name}: Lean's premises give {found}, the translation states {claim.grade}."
            )


def semantic_claims(inputs: dict) -> list[dict]:
    """Each claim the semantics states and the certificate proves: those that are ready,
    numbered by their place among the `verify` requests."""
    found = []
    requests = [r for r in inputs["program"]["requests"] if r["operation"] == "verify"]
    for index, request in enumerate(requests):
        claim = request["claim"]
        if not data.ready(claim):
            continue
        own = data.premise_keys(claim["subject_name"], claim["subject"])
        mine = [key for key in own if key[1] == claim["subject_name"]]
        found.append(
            {
                "claim": f"{claim['kind']}({claim['subject_name']})",
                "theorem": f"{NAMESPACE}.claim_{index}",
                "request_id": request["request_id"],
                "grade": data.grade(claim),
                "premise": data.premise_label(mine[0], claim["subject"]) if mine else None,
                "source": request["source"],
                "parts": [],
            }
        )
    return found


def semantic_premises(inputs: dict) -> list[str]:
    """The premises of the tests the program's claims involve, by name, once each."""
    names: list[str] = []
    for request in inputs["program"]["requests"]:
        if request["operation"] != "verify":
            continue
        claim = request["claim"]
        subjects = {claim["subject_name"]: claim["subject"]}
        stack = [claim["subject"]]
        while stack:
            subject = stack.pop()
            for member in subject.get("analyses", []):
                subjects[member["name"]] = member["analysis"]
                stack.append(member["analysis"])
        for key in data.premise_keys(claim["subject_name"], claim["subject"]):
            label = data.premise_label(key, subjects.get(key[1]))
            if label not in names:
                names.append(label)
    return names


def claims(inputs: dict) -> list[dict]:
    """Each claim the certificate establishes, with its grade and where it comes from."""
    if semantic(inputs) is not None:
        return semantic_claims(inputs)
    requests = inputs["program"]["requests"]
    found = []
    for claim in denotation(inputs).claims:
        request = requests[claim.request_id - 1]
        found.append(
            {
                "claim": f"{request['claim']['kind']}({request['claim']['subject_name']})",
                "theorem": f"{NAMESPACE}.{lean(claim.name)}",
                "request_id": claim.request_id,
                "grade": claim.grade,
                "premise": claim.own,
                "source": request["source"],
                # A result, interval or plan is proved in parts, named as its theorems are.
                "parts": [name for name, _ in claim.result.parts] if claim.result else [],
            }
        )
    return found


def semantic_profile(inputs: dict) -> dict:
    listed = [
        f"{claim['claim']}, line {claim['source']['line']}: {claim['grade']}"
        for claim in claims(inputs)
    ]
    count = len(data.declarations(inputs["program"]))
    return {
        "claims": [
            f"The contracts of its {count} declared tests and combinations, and the shape of "
            "each claim, hold, decided by Lean.",
            *listed,
        ],
        "assumptions": semantic_premises(inputs),
        "scope": (
            "The program as the StatClaim semantics defines it, for the canonical program "
            "these inputs bind, and each listed claim under the premises of the tests it "
            "involves."
        ),
        "theorems": [f"{NAMESPACE}.{name}" for name in semantic_theorems(inputs)],
        "general_theorem": f"{data.SEMANTICS}.Program.sound",
    }


def trusted_statement(inputs: dict) -> str:
    """What decides the certificate's statements."""
    if semantic(inputs) is not None:
        return (
            "The semantics of compiled programs (StatClaim/Semantics: Syntax, Meaning, "
            "Contracts, Grades, Encode) and the check that the data Lean read is the "
            "canonical program (lean_translation/data.py, binding_problem)."
        )
    return (
        "The translator's statement of each declaration and claim "
        "(lean_translation/denote.py, exact.py, statements.py) and the grade rule."
    )


def profile(inputs: dict) -> dict:
    """What the certificate says, for `verification._profile`."""
    if semantic(inputs) is not None:
        return semantic_profile(inputs)
    stated = denotation(inputs)
    listed = [
        f"{claim['claim']}, line {claim['source']['line']}: {claim['grade']}"
        for claim in claims(inputs)
    ]
    facts = sum(fact.check != "comment" for fact in stated.contracts)
    unproved = [f"Not proved in Lean, so left out: {name}." for name in inputs.get("omitted", [])]
    met = [f"The program's declarations meet {facts} contract facts, each decided by Lean."]
    return {
        "claims": [*(met if facts else []), *listed, *unproved],
        "assumptions": [premise.name for premise in stated.premises],
        "scope": (
            "The declarations of this program as Lean states them, and each listed claim "
            "under the listed premises. Parts the translation leaves out are not covered."
        ),
        "theorems": [f"{NAMESPACE}.{name}" for name in theorems(stated)],
        "general_theorem": f"{NAMESPACE}.program",
    }


def summary(inputs: dict) -> dict:
    """What a report shows: the claims, what is left out, and what Lean refutes."""
    if semantic(inputs) is not None:
        requests = [r for r in inputs["program"]["requests"] if r["operation"] == "verify"]
        return {
            "semantics": True,
            "claims": claims(inputs),
            "contract_facts": [entry["name"] for entry in data.declarations(inputs["program"])],
            "premises": semantic_premises(inputs),
            "not_translated": {},
            # Claims whose design stops by a rule depending on the data: the semantics
            # states them as False, so no certificate proves them.
            "refuted": {
                f"{r['claim']['kind']}({r['claim']['subject_name']})": "no sampling law"
                for r in requests
                if not data.fixed(r["claim"]["subject"])
            },
            # Claims whose levels add up to more than their own: Python leaves them open,
            # and the certificate does not prove them.
            "unproved": [
                f"{r['claim']['kind']}({r['claim']['subject_name']})"
                for r in requests
                if data.fixed(r["claim"]["subject"]) and not data.allocated(r["claim"]["subject"])
            ],
        }
    stated = denotation(inputs)
    return {
        "claims": claims(inputs),
        "contract_facts": [lean(f.name) for f in stated.contracts if f.check != "comment"],
        "premises": [premise.name for premise in stated.premises],
        "not_translated": dict(stated.skipped),
        "refuted": dict(stated.refuted),
    }
