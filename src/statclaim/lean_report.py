"""The Lean section of a study report: `statclaim report --lean`.

Python accepts the program first; then its translation is built and audited as a
compatibility certificate (`lean_translation/certificate.py`). Lean is the authority
here: a program Python accepts and Lean does not is reported as a failure naming both,
never as a weaker status.
"""

from pathlib import Path

from statclaim.language_compiler import compile_source
from statclaim.language_inspection import best_status
from statclaim.language_syntax import Source
from statclaim.language_values import STATUS_GRADES
from statclaim.lean_translation import certificate
from statclaim.verification import VerificationError, certify_program, lean_available

UNAVAILABLE = (
    "Lean is not available here. It lives in a StatClaim checkout with lake installed: "
    "run 'make setup' there, then pass --project. See docs/quickstart.md."
)


def lean_check(
    source: Source, *, project: Path, output: Path | None = None, timeout: float = 600
) -> dict:
    """Build and audit the program's compatibility certificate, and say what it shows."""
    compilation = compile_source(source)
    if compilation.status == "invalid":
        return {
            "status": "not_compiled",
            "message": "The program does not compile, so Lean is not asked about it.",
        }
    if not lean_available(project.resolve()):
        return {"status": "unavailable", "message": UNAVAILABLE}
    inputs = certificate.payload(source)
    try:
        issued, bundle = certify_program(inputs, project=project, output=output, timeout=timeout)
    except VerificationError as error:
        return {
            "status": "failed",
            "stage": error.stage,
            "message": (
                "Python accepts this program, but Lean did not check it. This disagreement "
                f"is a defect; please report it. Lean ({error.stage}): {error}"
            ),
            "certificate_directory": None if error.bundle is None else str(error.bundle),
        }
    summary = certificate.summary(inputs)
    requests = compilation.program.requests
    for claim in summary["claims"]:
        status = best_status(requests[claim["request_id"] - 1].claim)
        claim["python"] = STATUS_GRADES.get(status, status)
    return {
        "status": "checked",
        "certificate_id": issued["certificate_id"],
        "certificate_directory": str(bundle),
        **summary,
    }
