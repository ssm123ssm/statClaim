"""Issue one whole-program certificate and bind its evidence to each verified request."""

import dataclasses
from contextvars import ContextVar
from pathlib import Path

from statclaim.language_syntax import Source
from statclaim.lean_translation import certificate, data
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

# The parts of a result, interval or plan, as named in a semantic certificate.
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
    """Build the program in Lean, with or without claims. A claim
    whose proof Lean rejects is left out and the rest built again; an error in the
    declarations leaves the program unchecked and every claim unresolved, with Lean's
    message naming the disagreement."""
    inputs = certificate.payload(source, project)
    requests = {
        index: request["request_id"] for index, request in certificate.listed_requests(inputs)
    }
    facts = len(data.declarations(inputs["program"]))
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
                certificate.failing_claims(proof, log) if error.stage == "proof" and proof else None
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
                    None, None, {}, {rid: message for rid in requests.values()}, failure=failure
                )
            for index in failing:
                if index in requests:
                    failures[requests[index]] = f"Lean did not prove this claim: {error}"
            inputs = {**inputs, "omitted": sorted(failing)}
    listed = {claim["request_id"]: claim for claim in certificate.claims(inputs)}
    listed.update(
        (entry["request_id"], {**entry, "grade": "refuted"})
        for entry in certificate.counterexamples(inputs)
    )
    return ProgramRun(issued, bundle, listed, failures, contract_facts=facts)


def bind_report(run: ProgramRun, index: int, request, report: dict) -> dict:
    """Require the rendered values to match the values in this request's theorem."""
    from statclaim.lean_translation.material import interval_output, plan_output, result_output

    if run.issued is None or not report.get("certificate_issued"):
        return report
    inputs = run.issued["inputs"]
    found = next(
        (
            (entry, expected)
            for entry, expected in zip(
                certificate.requests(inputs), inputs["reported"], strict=True
            )
            if entry["request_id"] == index
        ),
        None,
    )
    if found is None:
        return report
    entry, expected = found
    if expected is None:
        return report
    kind = entry["claim"]["kind"]
    subject = entry["claim"]["subject"]
    got = report.get("calculation")
    actual: dict | None = None
    if isinstance(got, dict):
        try:
            if kind == "result":
                actual = result_output(request, got)
                if actual["reject_null"] != (report.get("decision") == "reject_null"):
                    actual = None
                analysis = subject["analysis"]
                if analysis.get("alternative") == "margin":
                    thresholds = data.margin_test(analysis).thresholds
                    assert thresholds is not None
                    if got.get("thresholds") != list(thresholds):
                        actual = None
            elif kind == "interval":
                actual = interval_output(request, got)
            else:
                actual = plan_output(subject, got)
        except (KeyError, TypeError, ValueError, data.Outside):
            actual = None
    if actual == expected:
        return report
    message = "The run's reported values differ from the values Lean checked."
    for key in ("certificate", "program_claim", "evidence_grade", "trusted_components"):
        report.pop(key, None)
    report.update(
        status="unresolved_obligation",
        certificate_issued=False,
        established_properties=[],
        outstanding_obligations=[message],
        verification={"stage": "binding", "message": message},
    )
    report["evidence"] = [e for e in report.get("evidence", []) if e["kind"] != "formal_proof"]
    return report


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
    if grade == "refuted":
        witness = {key: claim[key] for key in ("p", "typeI_error", "alpha", "theorem")}
        report.update(
            status="refuted",
            backend_invoked=True,
            certificate_issued=True,
            outstanding_obligations=[],
            verification={"stage": "counterexample", "message": claim["message"]},
            counterexample=witness,
            certificate=certificate,
            program_claim=program_claim,
        )
        return report
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
