"""The compatibility certificate of a whole program: milestone 6 of
docs/proposals/lean-translation.md.

Its inputs are the source and the canonical program it compiles to. Its proof is the
program's translation, followed by the audit `verify` certificates end with: every
contract fact and claim is a theorem that uses no axiom beyond Lean's three, and the
completion marker is bound to these inputs. Lean also lists the premises each claim's
proof uses, and the grades they give must be the ones the translation states, when the
certificate is issued and whenever it is checked again. `verification.py` builds and
replays it like every other certificate.

Result binding (trusted): `claims` maps each claim to the request and source line it
comes from.
"""

import re

from statclaim.language_compiler import compile_source
from statclaim.language_syntax import Source
from statclaim.lean_translation.denote import Denotation, denote
from statclaim.lean_translation.emit import name as lean
from statclaim.lean_translation.grades import grade
from statclaim.lean_translation.program import render
from statclaim.planning import AUDIT

KIND = "statclaim_program_certificate"
# Bump when the meaning of a translation changes, so older certificates are not replayed
# against a different translator.
TRANSLATION_VERSION = 1
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


def denotation(inputs: dict) -> Denotation:
    """What the program states in Lean, after checking that its source still compiles to
    the canonical program the inputs record."""
    if inputs.get("translation_version") != TRANSLATION_VERSION:
        raise Unchecked("The certificate was made by another version of the translator.")
    source = Source(inputs["source"]["text"], inputs["source"]["path"])
    compilation = compile_source(source)
    if compilation.status == "invalid" or compilation.program.to_dict() != inputs["program"]:
        raise Unchecked("The source no longer compiles to the program the inputs record.")
    return denote(compilation.program)


def theorems(stated: Denotation) -> list[str]:
    """Every theorem the audit checks: contract facts, claims and the program theorem."""
    names = [lean(fact.name) for fact in stated.contracts if fact.check != "comment"]
    names += [lean(claim.name) for claim in stated.claims]
    return [*names, "program"]


def proof(inputs: dict, input_sha256: str) -> str:
    """Proof.lean: the translation, then the audit bound to these inputs."""
    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    stated = denotation(inputs)
    names = ",\n    ".join(f"``{NAMESPACE}.{name}" for name in theorems(stated))
    return "\n".join(
        [
            "import StatClaim",
            "import Lean.Util.CollectAxioms",
            "",
            f"-- Canonical program SHA-256: {input_sha256}",
            f"namespace {NAMESPACE}",
            "",
            render(stated, LABEL).rstrip(),
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
    grade the translation states."""
    used = used_premises(output)
    for claim in denotation(inputs).claims:
        if claim.name not in used:
            raise Unchecked(f"Lean listed no premises for {claim.name}.")
        found = grade(claim.own, used[claim.name])
        if found != claim.grade:
            raise Unchecked(
                f"{claim.name}: Lean's premises give {found}, the translation states {claim.grade}."
            )


def claims(inputs: dict) -> list[dict]:
    """Each claim the certificate establishes, with its grade and where it comes from."""
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
            }
        )
    return found


def profile(inputs: dict) -> dict:
    """What the certificate says, for `verification._profile`."""
    stated = denotation(inputs)
    listed = [
        f"{claim['claim']}, line {claim['source']['line']}: {claim['grade']}"
        for claim in claims(inputs)
    ]
    facts = sum(fact.check != "comment" for fact in stated.contracts)
    return {
        "claims": [
            f"The program's declarations meet {facts} contract facts, each decided by Lean.",
            *listed,
        ],
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
    stated = denotation(inputs)
    return {
        "claims": claims(inputs),
        "contract_facts": [lean(f.name) for f in stated.contracts if f.check != "comment"],
        "premises": [premise.name for premise in stated.premises],
        "not_translated": dict(stated.skipped),
        "refuted": dict(stated.refuted),
    }
