"""Build, audit and replay Lean certificates of whole programs.

A certificate binds its inputs (the source and the canonical program it compiles to,
lean_translation/certificate.py) to the Lean file generated from them, the pinned
toolchain and library, and the transcript of the build. Lean must print the completion
marker bound to these inputs, after an audit that every audited theorem uses no axiom
beyond Lean's three. Replay recompiles the source, reconstructs the Lean data and reruns Lean;
a matching digest alone never counts.
"""

import hashlib
import json
import math
import os
import platform
import re
import shutil
import signal
import subprocess
import tempfile
from datetime import UTC, datetime
from pathlib import Path

from statclaim import __version__

TRUSTED_COMPONENTS = [
    "Lean's kernel and its checked integer reduction.",
    "The statistical meaning of the reviewed Lean definitions.",
    "Authenticity of the local toolchain and imported compiled dependencies.",
    "The parser, elaborator, canonical serialization, and certificate/report binding code.",
]

PROGRAM_KIND = "statclaim_program_certificate"


def _program_profile(payload: dict) -> dict:
    """A whole program's compatibility certificate (lean_translation/certificate.py)."""
    from statclaim.lean_translation import certificate

    try:
        stated = certificate.profile(payload)
    except certificate.Unchecked as error:
        raise VerificationError("binding", str(error)) from error
    return {
        "schema_version": 1,
        "kind": PROGRAM_KIND,
        # Each claim keeps its own grade: a cited claim in a checked program stays cited.
        "status": "program_checked_under_premises",
        **stated,
        "trusted_components": [*TRUSTED_COMPONENTS, certificate.trusted_statement(payload)],
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    }


def _profile(kind: str, payload: dict) -> dict:
    """What a certificate of this kind says; only the program certificate is issued."""
    if kind != PROGRAM_KIND:
        raise VerificationError(
            "integrity",
            "Unsupported certificate kind. Certificates of earlier kinds replay with the "
            "StatClaim version that issued them.",
        )
    return _program_profile(payload)


def _proof_for_payload(kind: str, payload: dict) -> str:
    if kind != PROGRAM_KIND:
        raise VerificationError("integrity", "Unsupported certificate kind.")
    from statclaim.lean_translation import certificate

    try:
        return certificate.proof(payload, digest(canonical_bytes(payload)))
    except certificate.Unchecked as error:
        raise VerificationError("binding", str(error)) from error


class VerificationError(RuntimeError):
    def __init__(self, stage: str, message: str, bundle: Path | None = None):
        super().__init__(message)
        self.stage = stage
        self.bundle = bundle


def canonical_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def _run(args: list[str], project: Path, timeout: float, logs: list[str], stage: str) -> str:
    logs.append(f"[{stage}] {json.dumps(args)}\n")
    try:
        process = subprocess.Popen(
            args,
            cwd=project,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
    except OSError as error:
        raise VerificationError(stage, str(error)) from error
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        try:
            if os.name == "posix":
                os.killpg(process.pid, signal.SIGKILL)
            else:
                process.kill()
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        logs.extend([stdout, stderr])
        raise VerificationError(stage, f"{stage} timed out after {timeout:g} seconds.") from error
    logs.extend([stdout, stderr])
    if process.returncode:
        detail = (stderr + stdout).strip()[-6000:]
        raise VerificationError(stage, f"{stage} exited with code {process.returncode}: {detail}")
    return stdout + stderr


NEEDS_LEAN = (
    "This claim needs the Lean backend, which lives in a StatClaim checkout. Run the command "
    "there or pass --project. Cited claims, compile, explain and report need no Lean."
)
# The files that make a folder a StatClaim checkout that can build Lean proofs.
LEAN_PROJECT_FILES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "StatClaim.lean")


def lean_available(project: Path) -> bool:
    """Whether verify(...) can build proofs here: a StatClaim checkout, with lake installed."""
    return (
        all((project / name).is_file() for name in LEAN_PROJECT_FILES)
        and (project / "StatClaim").is_dir()
        and shutil.which("lake") is not None
    )


def _source_hashes(project: Path) -> dict[str, str]:
    paths = [project / name for name in LEAN_PROJECT_FILES]
    if not all(path.is_file() for path in paths) or not (project / "StatClaim").is_dir():
        raise VerificationError("project", NEEDS_LEAN)
    paths += sorted((project / "StatClaim").rglob("*.lean"))
    hashes = {str(path.relative_to(project)): digest(path.read_bytes()) for path in paths}
    application = Path(__file__).parent
    for path in sorted(application.rglob("*.py")):
        relative = path.relative_to(application).as_posix()
        hashes[f"application/statclaim/{relative}"] = digest(path.read_bytes())
    return hashes


def _artifact_hashes(project: Path) -> dict[str, str]:
    directory = project / ".lake/build/lib/lean"
    paths = sorted(directory.glob("StatClaim.olean*"))
    paths += sorted((directory / "StatClaim").rglob("*.olean*"))
    paths = [path for path in paths if not path.name.endswith(".hash")]
    if not paths:
        raise VerificationError("artifacts", "The StatClaim compiled library is missing.")
    return {str(path.relative_to(project)): digest(path.read_bytes()) for path in paths}


def _dependencies(project: Path, timeout: float, logs: list[str]) -> list[dict]:
    manifest = json.loads((project / "lake-manifest.json").read_text())
    packages = project / ".lake/packages"
    versions = []
    for package in manifest["packages"]:
        if package["type"] != "git" or not re.fullmatch(r"[\w.-]+", package["name"]):
            raise VerificationError(
                "dependencies", "Only pinned Git Lake dependencies are supported."
            )
        path = (packages / package["name"]).resolve()
        if not path.is_relative_to(packages.resolve()):
            raise VerificationError(
                "dependencies", "Dependency checkout escapes the package directory."
            )
        revision = _run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            project,
            timeout,
            logs,
            "dependency-revision",
        ).strip()
        dirty = _run(
            ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=all"],
            project,
            timeout,
            logs,
            "dependency-status",
        ).strip()
        if revision != package["rev"] or dirty:
            raise VerificationError(
                "dependencies", f"Dependency {package['name']} differs from its pin."
            )
        versions.append({"name": package["name"], "revision": revision, "url": package["url"]})
    return versions


def _validate_timeout(timeout: float) -> None:
    if not math.isfinite(timeout) or timeout <= 0:
        raise ValueError("Timeout must be a positive, finite number of seconds.")


def _prepare(project: Path, timeout: float, logs: list[str]) -> tuple[dict, dict, dict]:
    source_hashes = _source_hashes(project)
    _run(["lake", "build"], project, timeout, logs, "build")
    toolchain = (project / "lean-toolchain").read_text().strip()
    lean_version = _run(
        ["lake", "env", "lean", "--version"], project, timeout, logs, "version"
    ).strip()
    match = re.search(r"\bversion ([^,\s]+)", lean_version)
    if not match or toolchain != f"leanprover/lean4:v{match[1]}":
        raise VerificationError("version", "The running Lean version differs from lean-toolchain.")
    environment = {
        "lean_version": lean_version,
        "lean_toolchain": toolchain,
        "dependencies": _dependencies(project, timeout, logs),
        "python_version": platform.python_version(),
        "statclaim_version": __version__,
    }
    if _source_hashes(project) != source_hashes:
        raise VerificationError("binding", "Project sources changed during the build.")
    return source_hashes, _artifact_hashes(project), environment


def _check_proof(
    bundle: Path,
    input_id: str,
    project: Path,
    timeout: float,
    logs: list[str],
    *,
    compile_output: bool,
) -> str:
    args = ["lake", "env", "lean", f"--root={bundle}"]
    if compile_output:
        args += ["-o", str(bundle / "Proof.olean")]
    args.append(str(bundle / "Proof.lean"))
    output = _run(args, project, timeout, logs, "proof")
    if f"STATCLAIM_CHECKED {input_id}" not in output.splitlines():
        raise VerificationError("proof", "Lean did not emit the expected audited-proof marker.")
    return output


def _check_grades(kind: str, payload: dict, output: str) -> None:
    """A program certificate's claims must have the grades their proofs' premises give."""
    if kind != PROGRAM_KIND:
        return
    from statclaim.lean_translation import certificate

    try:
        certificate.check_grades(payload, output)
    except certificate.Unchecked as error:
        raise VerificationError("grades", str(error)) from error


def _check_stable(
    project: Path,
    sources: dict,
    artifacts: dict,
    environment: dict,
    timeout: float,
    logs: list[str],
) -> None:
    if _source_hashes(project) != sources or _artifact_hashes(project) != artifacts:
        raise VerificationError("binding", "Sources or compiled artifacts changed during checking.")
    if _dependencies(project, timeout, logs) != environment["dependencies"]:
        raise VerificationError("binding", "Dependency revisions changed during checking.")


def certify_program(
    payload: dict, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify a whole program: its declarations are compatible as Lean states them, and
    each translated claim follows from its premises with the grade Lean's proof gives it.
    `payload` comes from `lean_translation.certificate.payload`."""
    return _certify_payload(payload, PROGRAM_KIND, project=project, output=output, timeout=timeout)


def _certify_payload(
    payload: dict,
    kind: str,
    *,
    project: Path,
    output: Path | None,
    timeout: float,
) -> tuple[dict, Path]:
    _validate_timeout(timeout)
    project = project.resolve()
    _source_hashes(project)
    input_id = digest(canonical_bytes(payload))
    proof_source = _proof_for_payload(kind, payload)
    if output is None:
        parent = project / ".statclaim/certificates"
        parent.mkdir(parents=True, exist_ok=True)
        bundle = Path(tempfile.mkdtemp(prefix=f"{input_id[:12]}-", dir=parent))
    else:
        bundle = output.resolve()
        bundle.mkdir(parents=True, exist_ok=False)
    logs: list[str] = []
    _write_json(bundle / "inputs.json", payload)
    (bundle / "Proof.lean").write_text(proof_source)
    try:
        sources, artifacts, environment = _prepare(project, timeout, logs)
        output = _check_proof(bundle, input_id, project, timeout, logs, compile_output=True)
        _check_grades(kind, payload, output)
        _check_stable(project, sources, artifacts, environment, timeout, logs)
        if (bundle / "Proof.lean").read_text() != proof_source or canonical_bytes(
            json.loads((bundle / "inputs.json").read_text())
        ) != canonical_bytes(payload):
            raise VerificationError("binding", "The proof or bound inputs changed during checking.")
        # Hash and retain the actual statements, checked artifact, inputs, and log.
        (bundle / "transcript.log").write_text("".join(logs))
        files = {
            name: digest((bundle / name).read_bytes())
            for name in ("inputs.json", "Proof.lean", "Proof.olean", "transcript.log")
        }
        certificate = {
            **_profile(kind, payload),
            "created_at": datetime.now(UTC).isoformat(),
            "input_sha256": input_id,
            "inputs": payload,
            "environment": environment,
            "source_sha256": sources,
            "compiled_library_sha256": artifacts,
            "files_sha256": files,
        }
        certificate["certificate_id"] = digest(canonical_bytes(certificate))
        pending = bundle / "certificate.pending.json"
        _write_json(pending, certificate)
        pending.replace(bundle / "certificate.json")
        return certificate, bundle
    except (VerificationError, OSError, ValueError, KeyError) as error:
        (bundle / "transcript.log").write_text("".join(logs))
        stage = error.stage if isinstance(error, VerificationError) else "backend"
        _write_json(bundle / "failure.json", {"stage": stage, "message": str(error)})
        raise VerificationError(stage, str(error), bundle) from error


def recheck_certificate(bundle: Path, *, project: Path, timeout: float = 120) -> dict:
    """Check integrity and regenerate the expected statements, then rerun Lean.

    A matching digest alone never constitutes verification. The original bundle
    is read-only during replay; proof source is checked again against the pins.
    """
    _validate_timeout(timeout)
    try:
        return _recheck_certificate(bundle, project=project, timeout=timeout)
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        raise VerificationError(
            "integrity", f"Malformed or incomplete certificate bundle: {error}"
        ) from error


def _recheck_certificate(bundle: Path, *, project: Path, timeout: float) -> dict:
    bundle, project = bundle.resolve(), project.resolve()
    certificate = json.loads((bundle / "certificate.json").read_text())
    if not isinstance(certificate, dict):
        raise VerificationError("integrity", "Certificate must be a JSON object.")
    identity = certificate.pop("certificate_id", None)
    if identity != digest(canonical_bytes(certificate)):
        raise VerificationError("integrity", "Certificate content digest does not match.")
    profile = _profile(certificate.get("kind"), certificate["inputs"])
    for key, value in profile.items():
        if canonical_bytes(certificate.get(key)) != canonical_bytes(value):
            raise VerificationError("integrity", f"Unsupported certificate field: {key}.")
    files = certificate["files_sha256"]
    if set(files) != {"inputs.json", "Proof.lean", "Proof.olean", "transcript.log"}:
        raise VerificationError("integrity", "Unexpected certificate file manifest.")
    for name, expected in files.items():
        if digest((bundle / name).read_bytes()) != expected:
            raise VerificationError("integrity", f"Certificate file {name} was changed.")
    payload = json.loads((bundle / "inputs.json").read_text())
    input_id = digest(canonical_bytes(payload))
    if input_id != certificate["input_sha256"] or payload != certificate["inputs"]:
        raise VerificationError("binding", "Certificate inputs do not match their binding.")
    if (bundle / "Proof.lean").read_text() != _proof_for_payload(certificate["kind"], payload):
        raise VerificationError(
            "binding", "Proof statements differ from the bound inputs and requested claims."
        )
    if _source_hashes(project) != certificate["source_sha256"]:
        raise VerificationError("binding", "The source snapshot differs from the certificate.")
    logs: list[str] = []
    sources, artifacts, environment = _prepare(project, timeout, logs)
    if sources != certificate["source_sha256"]:
        raise VerificationError("binding", "The source snapshot differs from the certificate.")
    for name in ("lean_toolchain", "dependencies", "statclaim_version"):
        if environment[name] != certificate["environment"][name]:
            raise VerificationError(
                "binding", "The pinned environment differs from the certificate."
            )
    output = _check_proof(bundle, input_id, project, timeout, logs, compile_output=False)
    _check_grades(certificate["kind"], payload, output)
    _check_stable(project, sources, artifacts, environment, timeout, logs)
    for name, expected in files.items():
        if digest((bundle / name).read_bytes()) != expected:
            raise VerificationError("binding", "The bundle changed during replay.")
    return {
        "status": "verified",
        "certificate_id": identity,
        "backend_invoked": True,
        "kind": certificate["kind"],
        # What the replayed certificate establishes; a composition leaves members assumed.
        "certificate_status": profile["status"],
        "claims": profile["claims"],
        **({"counterexamples": profile["counterexamples"]} if "counterexamples" in profile else {}),
        "certificate_directory": str(bundle),
    }
