"""Build a whole-program certificate from the compiled program and reported values."""

import re
from fractions import Fraction
from pathlib import Path

from statclaim.asymptotic import (
    fm_regions,
    fm_witness,
    mcnemar_witness,
    one_sample_score_probability,
)
from statclaim.language_compiler import compile_source
from statclaim.language_printer import program_source
from statclaim.language_syntax import Source
from statclaim.lean_translation import data
from statclaim.lean_translation.table import TABLE, NotInLean
from statclaim.wald import PROPORTION_Z_TESTS, find_certificate, find_counterexample

KIND = "statclaim_program_certificate"
TRANSLATION_VERSION = 3
NAMESPACE = "StatClaimProgram"
LABEL = "program"
COUNTEREXAMPLE_KEYS = {
    test: f"{test.removesuffix('_test')}_counterexamples"
    for test in (
        *PROPORTION_Z_TESTS,
        "mcnemar_asymptotic",
        "farrington_manning",
        "binomial_score_test",
    )
}

AUDIT = """
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[{names}] do
    match ← getConstInfo theoremName with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {{theoremName}}"
    for dependency in ← collectAxioms theoremName do
      unless allowed.contains dependency do
        throwError "Unexpected assumption {{dependency}} in {{theoremName}}"
  logInfo "STATCLAIM_CHECKED {input_sha256}"
"""


class Unchecked(ValueError):
    """The compiler or the semantic binding check could not accept the inputs."""


def payload(source: Source, project: Path | None = None) -> dict:
    """Bind the source, its canonical program and the reported values for verification."""
    from statclaim.lean_translation.material import material

    compilation = compile_source(source)
    if compilation.status == "invalid":
        raise Unchecked("The program does not compile, so Lean is not asked about it.")
    program = compilation.program
    reported, _ = material(program, project or Path.cwd())
    canonical = program.to_dict()
    witnesses: dict[str, dict[str, dict[str, str]]] = {}
    for index, claim in enumerate(data.verify_claims(canonical)):
        subject = claim["subject"]
        test = subject.get("test")
        if test not in COUNTEREXAMPLE_KEYS or not is_fixed_typeI(claim, test):
            continue
        if test == "mcnemar_asymptotic":
            witness = mcnemar_witness(*data.mcnemar_parameters(subject))
        elif test == "farrington_manning":
            witness = fm_witness(*data.fm_parameters(subject))
        elif test == "binomial_score_test":
            reference = Fraction(subject["null_rate"])
            risk = one_sample_score_probability(
                subject["model"]["n"], reference, Fraction(subject["squared_cutoff"])
            )
            witness = (reference, risk) if risk > Fraction(subject["alpha"]) else None
        else:
            n = subject["design"]["model"]["n_control"]
            cutoff, alpha = Fraction(subject["squared_cutoff"]), Fraction(subject["alpha"])
            pooled = test == "score_test"
            witness = (
                find_counterexample(n, cutoff, alpha, pooled=pooled)
                if find_certificate(n, cutoff, alpha, pooled=pooled) is None
                else None
            )
        if witness is not None:
            rate, risk = witness
            witnesses.setdefault(COUNTEREXAMPLE_KEYS[test], {})[str(index)] = {
                "p": str(rate),
                "typeI_error": str(risk),
            }
    return {
        "translation_version": TRANSLATION_VERSION,
        "source": {"path": source.path, "text": source.text},
        "program": canonical,
        "reported": reported,
        **witnesses,
    }


def is_fixed_typeI(claim: dict, test: str) -> bool:
    return (
        claim["kind"] == "typeI"
        and claim["subject"].get("test") == test
        and data.fixed(claim["subject"])
    )


def checked(inputs: dict):
    """Recompile the source and check the canonical input envelope."""
    if inputs.get("translation_version") != TRANSLATION_VERSION:
        raise Unchecked(
            "Replay this program certificate with the StatClaim version that issued it."
        )
    source = Source(inputs["source"]["text"], inputs["source"]["path"])
    compilation = compile_source(source)
    if compilation.status == "invalid" or compilation.program.to_dict() != inputs["program"]:
        raise Unchecked("The source no longer compiles to the program the inputs record.")
    claims = data.verify_claims(inputs["program"])
    count = len(claims)
    reported = inputs.get("reported")
    if not isinstance(reported, list) or len(reported) != count:
        raise Unchecked("Reported values must align with the program's verification requests.")
    if any(type(r) is not int or not 0 <= r < count for r in inputs.get("omitted", [])):
        raise Unchecked("The inputs omit an unknown verification request.")
    for test, key in COUNTEREXAMPLE_KEYS.items():
        check_counterexample_inputs(inputs.get(key, {}), claims, test)
    return compilation.program


def check_counterexample_inputs(witnesses: object, claims: list, test: str) -> None:
    if not isinstance(witnesses, dict):
        raise Unchecked("Counterexamples must be indexed by verification request.")
    count = len(claims)
    for index, witness in witnesses.items():
        if (
            not isinstance(index, str)
            or not index.isascii()
            or not index.isdecimal()
            or len(index) > len(str(count))
            or index != str(int(index))
            or int(index) >= count
            or not is_fixed_typeI(claims[int(index)], test)
        ):
            raise Unchecked(
                f"A {test} counterexample must refer to a matching fixed Type I request."
            )
        if not isinstance(witness, dict) or set(witness) != {"p", "typeI_error"}:
            raise Unchecked(
                "A counterexample needs a null rate and a rational rejection probability."
            )
        try:
            for value in witness.values():
                if not isinstance(value, str) or str(Fraction(value)) != value:
                    raise ValueError
        except (ValueError, ZeroDivisionError) as error:
            raise Unchecked("Counterexample values must be exact fractions.") from error


def counterexample_inputs(inputs: dict) -> dict:
    return {
        index: witness
        for key in COUNTEREXAMPLE_KEYS.values()
        for index, witness in inputs.get(key, {}).items()
    }


def semantic(inputs: dict) -> str:
    checked(inputs)
    try:
        return data.program_data(inputs["program"], reported=inputs["reported"])
    except data.Outside as error:
        raise Unchecked(str(error)) from error


def failing_claims(proof_text: str, output: str) -> set[int] | None:
    """Map proof errors to verification indices, or return None for a program error."""
    owner = None
    by_line = []
    for line in proof_text.splitlines():
        if re.match(r"^(?:theorem |def |end )", line):
            match = re.match(
                r"^theorem (?:claim|[a-z_]+_refuted)_(\d+)\b",
                line,
            )
            owner = int(match.group(1)) if match else None
        by_line.append(owner)
    end = proof_text.splitlines().index(f"end {NAMESPACE}") + 1
    failing = set()
    for match in re.finditer(r"Proof\.lean:(\d+):\d+: error", output):
        line_number = int(match.group(1))
        if line_number > end:
            continue
        owner = by_line[line_number - 1]
        if owner is None:
            return None
        failing.add(owner)
    return failing


def proof(inputs: dict, input_sha256: str) -> str:
    """Proof.lean instantiates the soundness theorem and audits the proof dependencies."""
    from statclaim.lean_translation.material import material

    if not re.fullmatch(r"[0-9a-f]{64}", input_sha256):
        raise ValueError("Expected a SHA-256 input identifier.")
    written = semantic(inputs)
    _, hints = material(checked(inputs), Path.cwd())
    refutations = counterexamples(inputs)
    subjects = [request["claim"]["subject"] for request in requests(inputs)]
    theorems = [
        "contracts",
        "canonical",
        *(f"claim_{index}" for index, _ in listed_requests(inputs)),
        *(refutation["theorem"].removeprefix(NAMESPACE + ".") for refutation in refutations),
    ]
    names = ",\n    ".join(f"``{NAMESPACE}.{name}" for name in theorems)
    return "\n".join(
        [
            "import StatClaim",
            "import Lean.Util.CollectAxioms",
            "",
            f"-- Canonical program SHA-256: {input_sha256}",
            *printed(inputs["program"]),
            f"namespace {NAMESPACE}",
            "",
            "set_option maxRecDepth 100000",
            "set_option maxHeartbeats 20000000",
            written,
            data.claims(
                inputs["program"],
                hints,
                inputs["reported"],
                frozenset(inputs.get("omitted", []))
                | frozenset(map(int, counterexample_inputs(inputs))),
            ),
            *(
                refutation_theorem(refutation, subjects[refutation["index"]])
                for refutation in refutations
            ),
            data.report(LABEL),
            f"end {NAMESPACE}",
            AUDIT.format(names=names, input_sha256=input_sha256),
        ]
    )


def printed(program: dict) -> list[str]:
    """The canonical program as StatClaim source, in comments: what a reviewer compares with
    the file. Lean reads its declarations and verify(...) requests as `program` below."""
    return [
        "--",
        "-- The canonical program, printed back as StatClaim source. Compiling it gives the",
        "-- same program; Lean reads its declarations and verify(...) requests below.",
        "--",
        *(f"--   {line}".rstrip() for line in program_source(program).splitlines()),
        "",
    ]


def requests(inputs: dict) -> list[dict]:
    return [r for r in inputs["program"]["requests"] if r["operation"] == "verify"]


def listed_requests(inputs: dict):
    omitted = set(inputs.get("omitted", []))
    witnesses = counterexample_inputs(inputs)
    for index, request in enumerate(requests(inputs)):
        if (
            index not in omitted
            and str(index) not in witnesses
            and data.ready(request["claim"], inputs["reported"], index)
        ):
            yield index, request


def check_grades(inputs: dict, output: str) -> None:
    """Compare the program, values and grades that Lean read with the bundle inputs."""
    problem = data.binding_problem(output, LABEL, inputs["program"], reported=inputs["reported"])
    if problem:
        raise Unchecked(problem)
    grades = data.printed_grades(output, LABEL)
    if grades is None or len(grades) != len(requests(inputs)):
        raise Unchecked("Lean did not print the expected number of grades.")
    for index, request in listed_requests(inputs):
        expected = data.grade(request["claim"])
        if grades[index] != expected:
            raise Unchecked(
                f"Request {request['request_id']}: Lean's grade differs from {expected}."
            )


def claim_name(claim: dict) -> str:
    return f"{claim['kind']}({claim['subject_name']})"


def counterexamples(inputs: dict) -> list[dict]:
    witnesses = counterexample_inputs(inputs)
    omitted = set(inputs.get("omitted", []))
    found = []
    for index, request in enumerate(requests(inputs)):
        witness = witnesses.get(str(index))
        if index in omitted or witness is None:
            continue
        claim = request["claim"]
        subject = claim["subject"]
        test = subject["test"].removesuffix("_test")
        alpha = subject["alpha"]
        location = f"common p = {witness['p']}"
        lower_bound = test == "farrington_manning"
        if test == "mcnemar_asymptotic":
            location = f"discordance probability q = {witness['p']}"
        elif test == "binomial_score":
            location = f"null response rate p = {witness['p']}"
        elif lower_bound:
            treatment = Fraction(witness["p"]) + Fraction(subject["null"]["value"])
            location = f"p_control = {witness['p']} and p_treatment = {treatment}"
        amount = "a lower bound on Type I error is" if lower_bound else "the exact Type I error is"
        found.append(
            {
                **witness,
                "alpha": alpha,
                "index": index,
                "request_id": request["request_id"],
                "claim": claim_name(claim),
                "theorem": f"{NAMESPACE}.{test}_refuted_{index}",
                "message": f"At {location}, {amount} {witness['typeI_error']}, exceeding {alpha}.",
            }
        )
    return found


def refutation_theorem(refutation: dict, subject: dict | None = None) -> str:
    index = refutation["index"]
    name = refutation["theorem"].removeprefix(f"{NAMESPACE}.")
    theorem = "wald_refuted" if name.startswith("wald_") else "proportionZ_refuted"
    hint = ""
    if name.startswith("mcnemar_asymptotic_"):
        theorem = "mcnemarAsymptotic_refuted"
    elif name.startswith("binomial_score_"):
        theorem = "oneSampleScore_refuted"
    elif name.startswith("farrington_manning_"):
        assert subject is not None
        theorem = "farringtonManning_refuted"
        _, inner = fm_regions(*data.fm_parameters(subject)[:-1])
        hint = f" {data.fm_region(inner)}"
    rate = data.rational(Fraction(refutation["p"]))
    risk = data.rational(Fraction(refutation["typeI_error"]))
    return (
        f"theorem {name} : ¬ program.Claim {index} :=\n"
        f"  {data.SEMANTICS}.Program.{theorem} program {index} {rate} {risk}{hint}"
        " (by decide +kernel)"
    )


def result_parts(claim: dict, output: dict | None) -> list[str]:
    kind = claim["kind"]
    if kind == "interval":
        return ["coverage", "interval"]
    if kind in ("meets", "sample_size"):
        parts = ["sizes", "power"]
        if claim["subject"].get("claim") == "smallest_in_range":
            parts.append("smaller")
        return parts
    if kind == "result" and output is not None:
        parts = ["decision"]
        for key, part in (
            ("p_value", "p_value"),
            ("observed_table_probability", "table_probability"),
            ("support_min", "support"),
            ("critical_value", "critical"),
            ("continued", "interim"),
        ):
            if key in output:
                parts.append(part)
        return parts
    return []


def claims(inputs: dict) -> list[dict]:
    found = []
    for index, request in listed_requests(inputs):
        claim = request["claim"]
        keys = data.premise_keys(claim["subject_name"], claim["subject"])
        own = next((key for key in keys if key[1] == claim["subject_name"]), None)
        found.append(
            {
                "claim": claim_name(claim),
                "theorem": f"{NAMESPACE}.claim_{index}",
                "request_id": request["request_id"],
                "grade": data.grade(claim),
                "premise": data.premise_label(own, claim["subject"]) if own else None,
                "source": request["source"],
                "parts": result_parts(claim, inputs["reported"][index]),
            }
        )
    return found


def semantic_premises(inputs: dict) -> list[str]:
    names: dict[str, None] = {}
    for request in requests(inputs):
        claim = request["claim"]
        subjects = {claim["subject_name"]: claim["subject"]}
        stack = [claim["subject"]]
        while stack:
            for member in stack.pop().get("analyses", []):
                subjects[member["name"]] = member["analysis"]
                stack.append(member["analysis"])
        for key in data.premise_keys(claim["subject_name"], claim["subject"]):
            names[data.premise_label(key, subjects.get(key[1]))] = None
    return list(names)


def trusted_statement(inputs: dict) -> str:
    return (
        "The reviewed StatClaim/Semantics definitions, Lean's JSON printer, and the check "
        "that the printed program and reported values match these inputs; "
        f"{data.SEMANTICS}.Program.form_injective proves that the printed form determines "
        "the program."
    )


def profile(inputs: dict) -> dict:
    checked(inputs)
    listed = claims(inputs)
    refuted = counterexamples(inputs)
    count = len(data.declarations(inputs["program"]))
    return {
        "claims": [
            f"Lean checks the contract facts of {count} test and combination declarations.",
            *(
                f"{claim['claim']}, line {claim['source']['line']}: {claim['grade']}"
                for claim in listed
            ),
            *(f"{entry['claim']} refuted. {entry['message']}" for entry in refuted),
        ],
        "assumptions": semantic_premises(inputs),
        "scope": "The bound program and reported values, under the listed mathematical premises.",
        "theorems": [
            f"{NAMESPACE}.contracts",
            f"{NAMESPACE}.canonical",
            *(claim["theorem"] for claim in listed),
            *(entry["theorem"] for entry in refuted),
        ],
        **({"counterexamples": refuted} if refuted else {}),
        "general_theorem": f"{data.SEMANTICS}.Program.sound",
        "binding_theorem": f"{data.SEMANTICS}.Program.form_injective",
    }


def summary(inputs: dict) -> dict:
    declared = data.declarations(inputs["program"])
    outside = TABLE["blinded_reestimation"]
    assert isinstance(outside, NotInLean)
    unproved = {}
    for index, request in enumerate(requests(inputs)):
        claim = request["claim"]
        if not data.fixed(claim["subject"]):
            continue
        if index in inputs.get("omitted", []):
            unproved[claim_name(claim)] = "Lean did not prove the claim."
        elif not data.allocated(claim["subject"]):
            unproved[claim_name(claim)] = "The members' levels exceed the allocated level."
        elif not data.ready(claim, inputs["reported"], index):
            unproved[claim_name(claim)] = (
                "The calculation did not find a design meeting the targets."
            )
    return {
        "semantics": True,
        "claims": claims(inputs),
        "contract_facts": [e["name"] for e in declared],
        "premises": semantic_premises(inputs),
        "outside_lean": {
            entry["name"]: outside.reason
            for entry in inputs["program"]["bindings"]
            if entry["type"] == "ReestimationIR"
        },
        "refuted": {
            **{
                claim_name(r["claim"]): "no sampling law"
                for r in requests(inputs)
                if not data.fixed(r["claim"]["subject"])
            },
            **{entry["claim"]: entry["message"] for entry in counterexamples(inputs)},
        },
        "unproved": list(unproved),
        "unproved_reasons": unproved,
    }
