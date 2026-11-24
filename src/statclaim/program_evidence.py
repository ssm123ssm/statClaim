"""The program certificate a run builds once, and the evidence each verified claim takes
from it. See docs/proposals/lean-translation.md.

`statclaim check` translates every program it runs and builds it in Lean once
(`lean_translation/certificate.py`), even one that only calculates: Lean decides the
declarations' contract facts and proves each claim the translation states. Each `verify`
request then runs as before, computing what it reports, and where it would have built a
certificate of its own it takes the program certificate's evidence for its claim instead
(`attach`): its status follows the grade Lean's proof gives it. A claim Lean does not
prove is left out of the certificate and stays unresolved, with Lean's message; the rest
is still certified. Calculated and simulated values are not proved.

Result binding (trusted): a request takes only the evidence of the claim the translation
states for that request.
"""

import dataclasses
from contextvars import ContextVar
from pathlib import Path

from statclaim.language_syntax import Source
from statclaim.lean_translation import certificate
from statclaim.verification import VerificationError, certify_program, digest

STATUS = {
    "proved": "verified",
    "conditional": "conditional",
    "cited": "cited",
    "declared": "declared",
}
WORDS = {
    "proved": "Proved in Lean",
    "conditional": "Combination proved in Lean; members assumed",
    "cited": "Cited; its contract facts checked in Lean",
    "declared": "Declared by the author; its contract facts checked in Lean",
}

# The parts of a result, interval or plan, as `statements.py` names its theorems.
PARTS = {
    "counts": "the observed counts lie in the declared sample",
    "support": "the possible tables given the margins",
    "table_probability": "the observed table's probability",
    "p_value": "the p-value reported",
    "decision": "the decision reported",
    "critical": "the critical value",
    "interim": "the interim decision under the declared rule",
    "stages": "the stage sizes",
    "interval": "the interval reported",
    "coverage": "the interval's coverage",
    "law": "the law of the counts",
    "tails": "the tail probabilities",
    "size": "the sample size",
    "sizes": "the arm sizes",
    "power": "the power at the planning point",
    "smaller": "that no smaller design meets the targets",
}


@dataclasses.dataclass(frozen=True)
class ProgramRun:
    """One build of a program in Lean, and the request being run."""

    issued: dict | None  # the certificate, or None when Lean checked nothing
    bundle: Path | None
    claims: dict  # request id → the claim the certificate proves for it
    failures: dict  # request id → why Lean did not prove its claim
    request: int = 0
    contract_facts: int = 0  # how many contract facts of the declarations Lean decided
    failure: dict | None = None  # why Lean checked nothing: its stage, message and error


# The program run of the request `check_source` is running; unset outside a run.
CURRENT: ContextVar[ProgramRun | None] = ContextVar("statclaim_program_run", default=None)


def build(source: Source, *, project: Path, output: Path, timeout: float) -> ProgramRun:
    """Translate the program and build it in Lean once, with or without claims. A claim
    whose proof Lean rejects is left out and the rest built again; an error in the
    declarations leaves the program unchecked and every claim unresolved, with Lean's
    message naming the disagreement."""
    inputs = certificate.payload(source)
    stated = certificate.denotation(inputs)
    requests = {claim.request_id: claim for claim in stated.claims}
    facts = sum(fact.check != "comment" for fact in stated.contracts)
    failures: dict = {}
    for attempt in (1, 2):
        try:
            # A second build leaves out the claims Lean did not prove in the first.
            directory = output if attempt == 1 else output.with_name(output.name + "-proved")
            issued, bundle = certify_program(
                inputs, project=project, output=directory, timeout=timeout
            )
            break
        except VerificationError as error:
            proof = (error.bundle / "Proof.lean").read_text() if error.bundle else ""
            log = (error.bundle / "transcript.log").read_text() if error.bundle else ""
            failing = (
                certificate.failing_claims(proof, log, certificate.denotation(inputs))
                if error.stage == "proof"
                else None
            )
            if attempt == 2 or not failing:
                message = (
                    "Python accepts this program, but Lean did not check it. This "
                    f"disagreement is a defect; please report it. Lean ({error.stage}): {error}"
                )
                if error.stage == "project":
                    message = str(error)
                failure = {"stage": error.stage, "message": message, "error": str(error)}
                return ProgramRun(
                    None, None, {}, {rid: message for rid in requests}, failure=failure
                )
            for claim in stated.claims:
                if claim.name in failing:
                    failures[claim.request_id] = f"Lean did not prove this claim: {error}"
            inputs = {**inputs, "omitted": sorted(failing)}
    listed = {claim["request_id"]: claim for claim in certificate.claims(inputs)}
    return ProgramRun(issued, bundle, listed, failures, contract_facts=facts)


def attach(report: dict) -> dict | None:
    """The report with the program certificate's evidence for the request being run, or
    None when the program certificate does not cover it (no run, or not translated)."""
    run = CURRENT.get()
    if run is None:
        return None
    request = run.request
    if request in run.failures:
        report["backend_invoked"] = True
        report["verification"] = {"stage": "proof", "message": run.failures[request]}
        report["evidence_source"] = "program"
        return report
    claim = run.claims.get(request)
    if claim is None or run.issued is None or run.bundle is None:
        return None
    issued, bundle, grade = run.issued, run.bundle, claim["grade"]
    certificate = {
        "certificate_id": issued["certificate_id"],
        "directory": str(bundle),
        "file": str(bundle / "certificate.json"),
        "sha256": digest((bundle / "certificate.json").read_bytes()),
    }
    program_claim = {"kind": issued["kind"], "theorem": claim["theorem"], "grade": grade}
    if grade in ("cited", "declared"):
        # Python's account of the cited guarantee stands; Lean checked the declarations'
        # contract facts and that the claim rests on its own premise.
        report.update(
            status=STATUS[grade],
            evidence_grade=grade,
            evidence_source="program",
            backend_invoked=True,
            lean_check={**program_claim, "certificate": certificate},
        )
        return report
    target = report.get("target_property") or claim["claim"]
    # How a combination of assumed members combines, in its own words, when it has them.
    words = report.pop("combination_words", None) if grade == "conditional" else None
    # The claim, the parts it is proved in, and the declarations' contract facts.
    established = [f"{WORDS[grade]}.", *words] if words else [f"{WORDS[grade]}: {target}"]
    parts = [PARTS[part] for part in claim.get("parts", []) if part in PARTS]
    if parts:
        established.append("Also proved in Lean: " + "; ".join(parts) + ".")
    established += [line for line in issued["claims"][:1] if "contract facts" in line]
    report.update(
        status=STATUS[grade],
        evidence_grade=grade,
        evidence_source="program",
        certificate_issued=True,
        backend_invoked=True,
        established_properties=established,
        outstanding_obligations=[],
        trusted_components=issued["trusted_components"],
        certificate=certificate,
        program_claim=program_claim,
    )
    report.setdefault("evidence", []).append(
        {
            "kind": "formal_proof",
            "scope": established,
            "theorems": [claim["theorem"]],
            "backend": issued["environment"]["lean_version"],
            "input_sha256": issued["input_sha256"],
            "certificate_id": issued["certificate_id"],
        }
    )
    if isinstance(report.get("formal_reference"), dict):
        report["formal_reference"].update(
            theorem=claim["theorem"],
            checked_in_this_run=True,
            application_to_this_run="verified_in_program",
        )
    return report
