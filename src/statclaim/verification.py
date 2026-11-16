"""Issue and recheck design-level and per-result Lean certificate bundles."""

import hashlib
import json
import math
import os
import platform
import re
import signal
import subprocess
import tempfile
from datetime import UTC, datetime
from fractions import Fraction
from pathlib import Path

from statclaim import __version__
from statclaim.design import Design
from statclaim.family import FAMILY_ASSUMPTIONS, Endpoint, FisherFamily
from statclaim.fisher import TEST_VERSION, FisherResult, parse_alpha, test_id
from statclaim.planning import (
    DIFFERENCE_ASSUMPTIONS,
    DIFFERENCE_CHECKED_THEOREMS,
    DIFFERENCE_KIND,
    INTERVAL_ASSUMPTIONS,
    INTERVAL_CHECKED_THEOREMS,
    INTERVAL_KIND,
    MARGIN_KIND,
    NULL_NAMES,
    PLANNING_KIND,
    POLICY_KIND,
    RESULT_ASSUMPTIONS,
    RESULT_CHECKED_THEOREMS,
    RESULT_KIND,
    STAGE_RESULT_KIND,
    BinomialInterval,
    DifferenceInterval,
    MarginTest,
    OneSampleResult,
    PowerPlan,
    TwoStagePlan,
    TwoStageResult,
    alternative_of,
    difference_claims,
    difference_payload,
    interval_claims,
    interval_payload,
    margin_assumptions,
    margin_claims,
    margin_payload,
    margin_theorems,
    parse_difference_payload,
    parse_interval_payload,
    parse_margin_payload,
    parse_planning_payload,
    parse_policy_payload,
    parse_result_payload,
    parse_stage_result_payload,
    planning_assumptions,
    planning_claims,
    planning_payload,
    planning_theorems,
    policy_assumptions,
    policy_claims,
    policy_payload,
    policy_theorems,
    render_difference_proof,
    render_interval_proof,
    render_margin_proof,
    render_planning_proof,
    render_policy_proof,
    render_result_proof,
    render_stage_result_proof,
    result_claims,
    stage_result_assumptions,
    stage_result_claims,
    stage_result_payload,
    stage_result_theorems,
)
from statclaim.planning import result_payload as binomial_result_payload
from statclaim.proof import (
    CHECKED_THEOREMS,
    DESIGN_CHECKED_THEOREMS,
    FAMILY_CHECKED_THEOREMS,
    ONE_SIDED_DESIGN_THEOREMS,
    ONE_SIDED_RESULT_THEOREMS,
    render_design_proof,
    render_family_proof,
    render_proof,
    validate_result,
)

CLAIMS = [
    "Exact p-value equals the Lean Fisher definition for these counts.",
    "Observed table probability and support equal the Lean definitions.",
    "Reported decision equals membership in the formal rejection event.",
    "The specified fixed-sample rule has Type I error at most 1/20 under the null model.",
]
ASSUMPTIONS = [
    "The samples follow two independent binomial distributions.",
    "Positive arm sizes were fixed before outcomes were observed.",
    "The error bound is under the null of equal success probabilities, for every p in [0, 1].",
    "The supplied counts describe the declared sampling procedure.",
]
TRUSTED_COMPONENTS = [
    "Lean's kernel and its checked integer reduction.",
    "The statistical meaning of the reviewed Lean definitions.",
    "Authenticity of the local toolchain and imported compiled dependencies.",
    "The input parser, proof generator, and certificate/report binding code.",
]
DESIGN_CLAIMS = [
    "The declared positive sample sizes and fixed sampling-law contract are Lean checked.",
    "The specified two-sided Fisher analysis has Type I error at most 1/20 "
    "under the null, for every common success probability in [0, 1].",
]
DESIGN_ASSUMPTIONS = ASSUMPTIONS[:3]
ONE_SIDED_NULL = "the treatment success probability is at most the control's"
ONE_SIDED_ASSUMPTIONS = [
    *ASSUMPTIONS[:2],
    f"The error bound is under the null that {ONE_SIDED_NULL}.",
    ASSUMPTIONS[3],
]
ONE_SIDED_DESIGN_CLAIMS = [
    "The declared positive sample sizes are Lean checked, and the rejection bounds are "
    "validated against the formal one-sided p-value.",
    f"The one-sided Fisher analysis has Type I error at most 1/20 whenever {ONE_SIDED_NULL}.",
]
ONE_SIDED_CLAIMS = [
    "Exact one-sided p-value equals the Lean definition for these counts.",
    "Reported decision follows from comparing that p-value with the level.",
    ONE_SIDED_DESIGN_CLAIMS[1],
]


def _profile(kind: str, payload: dict) -> dict:
    """Only these built-in scopes may select claims and generated proof obligations."""
    one_sided = kind in (
        "statclaim_per_result_certificate",
        "statclaim_design_certificate",
    ) and "greater" == alternative_of(
        (payload.get("analysis") or payload.get("result") or {}).get("test", "")
    )
    if kind == "statclaim_per_result_certificate":
        claims, assumptions, theorems = CLAIMS, ASSUMPTIONS, CHECKED_THEOREMS
        scope = "This result and the specified mathematical model; not all Python executions."
        general_theorem = "StatClaim.fisher_typeI_error_le_alpha"
        if one_sided:
            claims, assumptions = ONE_SIDED_CLAIMS, ONE_SIDED_ASSUMPTIONS
            theorems = ONE_SIDED_RESULT_THEOREMS
            general_theorem = "StatClaim.Modules.FisherOneSided.typeI_of_hints"
    elif kind == "statclaim_design_certificate":
        claims, assumptions, theorems = DESIGN_CLAIMS, DESIGN_ASSUMPTIONS, DESIGN_CHECKED_THEOREMS
        scope = "The declared analysis and mathematical model; no observed results are certified."
        general_theorem = "StatClaim.Modules.Fisher.typeI_statement"
        if one_sided:
            claims, assumptions = ONE_SIDED_DESIGN_CLAIMS, ONE_SIDED_ASSUMPTIONS[:3]
            theorems = ONE_SIDED_DESIGN_THEOREMS
            general_theorem = "StatClaim.Modules.FisherOneSided.typeI_of_hints"
    elif kind == "statclaim_family_certificate":
        family = _parse_family_payload(payload)
        claims = [
            "Each declared Fisher analysis has its marginal Type I bound under its endpoint null.",
            f"Strong familywise error is at most {family.alpha} under the declared marginal-law "
            "contracts, for every configuration of true and false endpoint nulls.",
            "The sum of the allocated endpoint levels does not exceed the familywise bound.",
        ]
        assumptions, theorems = FAMILY_ASSUMPTIONS, FAMILY_CHECKED_THEOREMS
        scope = (
            "The declared analyses, conditional on their marginal sampling laws; "
            "no observed results are certified."
        )
        general_theorem = "StatClaim.Modules.FisherFamilyN.strong_control"
    elif kind == PLANNING_KIND:
        plan = parse_planning_payload(payload)
        claims = planning_claims(plan)
        assumptions = planning_assumptions(plan.design.alternative)
        theorems = planning_theorems(plan)
        scope = (
            "The declared fixed design, its Type I bound and its power at one planning point; "
            "no observed results, other alternatives or minimality are certified."
        )
        general_theorem = "StatClaim.Modules.FisherPower.power_of_check"
    elif kind == POLICY_KIND:
        plan = parse_policy_payload(payload)
        claims, assumptions = policy_claims(plan), policy_assumptions(plan)
        theorems = policy_theorems(plan)
        scope = (
            "The complete declared single-arm design, its error bound and its power at one "
            "planning point; no observed results or minimality are certified."
        )
        general_theorem = "StatClaim.Modules.TwoStageBinomial.rejection_probability"
    elif kind == RESULT_KIND:
        claims = result_claims(parse_result_payload(payload))
        assumptions, theorems = RESULT_ASSUMPTIONS, RESULT_CHECKED_THEOREMS
        scope = "This observed count and the declared test; not other data or analyses."
        general_theorem = "StatClaim.Modules.OneSampleBinomial.typeI_of_check"
    elif kind == STAGE_RESULT_KIND:
        staged = parse_stage_result_payload(payload)
        claims, assumptions = stage_result_claims(staged), stage_result_assumptions(staged)
        theorems = stage_result_theorems(staged)
        scope = "These observed counts and the declared two-stage design; not other data."
        general_theorem = "StatClaim.Modules.TwoStageBinomial.typeI_atMost_of_check"
    elif kind == MARGIN_KIND:
        margin = parse_margin_payload(payload)
        claims, assumptions = margin_claims(margin), margin_assumptions(margin)
        theorems = margin_theorems(margin)
        scope = (
            "The declared exact difference test and its error bound over the whole null; "
            "power at one planning point and one observed decision where stated."
        )
        general_theorem = "StatClaim.Modules.DifferenceTest.typeI_of_cells"
    elif kind == DIFFERENCE_KIND:
        claims = difference_claims(parse_difference_payload(payload))
        assumptions, theorems = DIFFERENCE_ASSUMPTIONS, DIFFERENCE_CHECKED_THEOREMS
        scope = (
            "Joint coverage of the two arms' exact confidence sets, and the reported "
            "interval for the difference at these observed counts."
        )
        general_theorem = "StatClaim.Modules.BinomialInterval.joint_coverage"
    elif kind == INTERVAL_KIND:
        claims = interval_claims(parse_interval_payload(payload))
        assumptions, theorems = INTERVAL_ASSUMPTIONS, INTERVAL_CHECKED_THEOREMS
        scope = (
            "Coverage of the exact confidence set for this sample size, and the reported "
            "interval for this observed count."
        )
        general_theorem = "StatClaim.Modules.BinomialInterval.coverage"
    else:
        raise VerificationError("integrity", "Unsupported certificate kind.")
    if kind in ("statclaim_per_result_certificate", "statclaim_design_certificate"):
        alpha = (
            _parse_payload(payload)[0].alpha
            if kind == "statclaim_per_result_certificate"
            else parse_alpha(payload["analysis"]["alpha"])
        )
        claims = [claim.replace("1/20", str(alpha)) for claim in claims]
    return {
        "schema_version": 1,
        "kind": kind,
        "status": "verified_under_assumptions",
        "claims": list(claims),
        "assumptions": list(assumptions),
        "trusted_components": list(TRUSTED_COMPONENTS),
        "scope": scope,
        "theorems": [f"StatClaimCertificate.{name}" for name in theorems],
        "general_theorem": general_theorem,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    }


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


def result_payload(design: Design, result: FisherResult) -> dict:
    validate_result(design, result)
    return {
        "schema_version": 1,
        "design": {
            "module": "two_arm_binomial",
            "n_control": design.n_control,
            "n_treatment": design.n_treatment,
            "stopping": design.stopping,
        },
        "result": result.to_dict(),
    }


def design_payload(design: Design) -> dict:
    if design.stopping != "fixed":
        raise ValueError("A fixed-sample design certificate requires stopping='fixed'.")
    return {
        "schema_version": 1,
        "scope": "design",
        "design": {
            "module": "two_arm_binomial",
            "n_control": design.n_control,
            "n_treatment": design.n_treatment,
            "stopping": design.stopping,
        },
        "analysis": {
            "test": test_id(design.alternative),
            "test_version": TEST_VERSION,
            "null": NULL_NAMES[design.alternative],
            "alpha": str(design.alpha),
        },
    }


def family_payload(family: FisherFamily) -> dict:
    if not family.supported:
        raise ValueError("A Fisher family certificate requires fixed sampling for every analysis.")
    if family.allocated_alpha > family.alpha:
        raise ValueError("The allocated alpha exceeds the requested familywise bound.")
    return {
        "schema_version": 1,
        "scope": "family",
        "method": "bonferroni",
        "module_version": "0.1.0",
        "alpha": str(family.alpha),
        "joint_law": "binomial_marginals",
        "analyses": [{"name": e.name, **design_payload(e.design)} for e in family.endpoints],
    }


def _parse_family_payload(payload: dict) -> FisherFamily:
    endpoints = []
    for endpoint in payload["analyses"]:
        design = endpoint["design"]
        endpoints.append(
            Endpoint(
                endpoint["name"],
                Design(
                    design["n_control"],
                    design["n_treatment"],
                    design["stopping"],
                    parse_alpha(endpoint["analysis"]["alpha"]),
                ),
            )
        )
    family = FisherFamily(parse_alpha(payload["alpha"]), tuple(endpoints))
    if canonical_bytes(payload) != canonical_bytes(family_payload(family)):
        raise ValueError("Bound family, analysis, or requested guarantee is inconsistent.")
    return family


def _fraction_from_record(record: dict) -> Fraction:
    numerator, denominator = record["numerator"], record["denominator"]
    if type(numerator) is not int or type(denominator) is not int or denominator <= 0:
        raise ValueError("Invalid rational value in bound inputs.")
    return Fraction(numerator, denominator)


def _proof_for_payload(kind: str, payload: dict) -> str:
    input_id = digest(canonical_bytes(payload))
    if kind == "statclaim_per_result_certificate":
        design, result = _parse_payload(payload)
        return render_proof(design, result, input_id)
    if kind == "statclaim_design_certificate":
        declaration = payload["design"]
        design = Design(
            declaration["n_control"],
            declaration["n_treatment"],
            declaration["stopping"],
            parse_alpha(payload["analysis"]["alpha"]),
            alternative_of(payload["analysis"]["test"]),
        )
        if canonical_bytes(payload) != canonical_bytes(design_payload(design)):
            raise ValueError("Bound design, analysis, or requested guarantee is inconsistent.")
        return render_design_proof(design, input_id)
    if kind == "statclaim_family_certificate":
        return render_family_proof(_parse_family_payload(payload), input_id)
    if kind == PLANNING_KIND:
        return render_planning_proof(parse_planning_payload(payload), input_id)
    if kind == POLICY_KIND:
        return render_policy_proof(parse_policy_payload(payload), input_id)
    if kind == STAGE_RESULT_KIND:
        return render_stage_result_proof(parse_stage_result_payload(payload), input_id)
    if kind == MARGIN_KIND:
        return render_margin_proof(parse_margin_payload(payload), input_id)
    if kind == DIFFERENCE_KIND:
        return render_difference_proof(parse_difference_payload(payload), input_id)
    if kind == INTERVAL_KIND:
        return render_interval_proof(parse_interval_payload(payload), input_id)
    if kind == RESULT_KIND:
        return render_result_proof(parse_result_payload(payload), input_id)
    raise VerificationError("integrity", "Unsupported certificate kind.")


def _parse_payload(payload: dict) -> tuple[Design, FisherResult]:
    try:
        declaration, calculation = payload["design"], payload["result"]
        design = Design(
            declaration["n_control"],
            declaration["n_treatment"],
            declaration["stopping"],
            _fraction_from_record(calculation["alpha"]),
            alternative_of(calculation["test"]),
        )
        probabilities = []
        for name in ("p_value", "observed_table_probability"):
            record = calculation[name]
            numerator, denominator = record["numerator"], record["denominator"]
            if type(numerator) is not int or type(denominator) is not int or denominator <= 0:
                raise ValueError("Invalid rational value in bound inputs.")
            probabilities.append(Fraction(numerator, denominator))
        result = FisherResult(
            n_control=design.n_control,
            n_treatment=design.n_treatment,
            control_successes=calculation["table"]["control"][0],
            treatment_successes=calculation["table"]["treatment"][0],
            p_value=probabilities[0],
            observed_table_probability=probabilities[1],
            support_min=calculation["control_success_support"]["min"],
            support_max=calculation["control_success_support"]["max"],
            alpha=design.alpha,
            alternative=design.alternative,
        )
        # Reconstruct all derived fields; reject changed decisions, table labels,
        # sizes, thresholds, approximations, versions, or additional fields.
        if canonical_bytes(payload) != canonical_bytes(result_payload(design, result)):
            raise ValueError("Bound inputs or derived result fields are inconsistent.")
        return design, result
    except (KeyError, TypeError, IndexError, ZeroDivisionError) as error:
        raise ValueError("Malformed bound inputs.") from error


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


def _source_hashes(project: Path) -> dict[str, str]:
    required = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "StatClaim.lean"]
    paths = [project / name for name in required]
    if not all(path.is_file() for path in paths) or not (project / "StatClaim").is_dir():
        raise VerificationError("project", "Select the StatClaim project root with --project.")
    paths += sorted((project / "StatClaim").rglob("*.lean"))
    hashes = {str(path.relative_to(project)): digest(path.read_bytes()) for path in paths}
    for path in sorted(Path(__file__).parent.glob("*.py")):
        hashes[f"application/statclaim/{path.name}"] = digest(path.read_bytes())
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
) -> None:
    args = ["lake", "env", "lean", f"--root={bundle}"]
    if compile_output:
        args += ["-o", str(bundle / "Proof.olean")]
    args.append(str(bundle / "Proof.lean"))
    output = _run(args, project, timeout, logs, "proof")
    if f"STATCLAIM_CHECKED {input_id}" not in output.splitlines():
        raise VerificationError("proof", "Lean did not emit the expected audited-proof marker.")


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


def certify_result(
    design: Design,
    result: FisherResult,
    *,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> tuple[dict, Path]:
    """Certify this proposed result; correctness of all Python executions is not claimed."""
    return _certify_payload(
        result_payload(design, result),
        "statclaim_per_result_certificate",
        project=project,
        output=output,
        timeout=timeout,
    )


def certify_design(
    design: Design,
    *,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> tuple[dict, Path]:
    """Certify the declared analysis before any observed data are supplied."""
    return _certify_payload(
        design_payload(design),
        "statclaim_design_certificate",
        project=project,
        output=output,
        timeout=timeout,
    )


def certify_family(
    family: FisherFamily, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    return _certify_payload(
        family_payload(family),
        "statclaim_family_certificate",
        project=project,
        output=output,
        timeout=timeout,
    )


def certify_planning(
    plan: PowerPlan, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify a fixed design's Type I bound and its power at one planning point."""
    return _certify_payload(
        planning_payload(plan), PLANNING_KIND, project=project, output=output, timeout=timeout
    )


def certify_policy(
    plan: TwoStagePlan, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify a complete two-stage policy's error and power at its declared rates."""
    return _certify_payload(
        policy_payload(plan), POLICY_KIND, project=project, output=output, timeout=timeout
    )


def certify_binomial_result(
    result: OneSampleResult, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify an observed one-sample result; Lean confirms the proposed p-value."""
    return _certify_payload(
        binomial_result_payload(result),
        RESULT_KIND,
        project=project,
        output=output,
        timeout=timeout,
    )


def certify_stage_result(
    result: TwoStageResult, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify the decision a two-stage design reaches for observed counts."""
    return _certify_payload(
        stage_result_payload(result),
        STAGE_RESULT_KIND,
        project=project,
        output=output,
        timeout=timeout,
    )


def certify_difference(
    interval: DifferenceInterval,
    *,
    project: Path,
    output: Path | None = None,
    timeout: float = 120,
) -> tuple[dict, Path]:
    """Certify an interval for a difference of two proportions."""
    return _certify_payload(
        difference_payload(interval),
        DIFFERENCE_KIND,
        project=project,
        output=output,
        timeout=timeout,
    )


def certify_margin(
    test: MarginTest, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify an exact difference test with a margin, and its target or decision if any."""
    return _certify_payload(
        margin_payload(test), MARGIN_KIND, project=project, output=output, timeout=timeout
    )


def certify_interval(
    interval: BinomialInterval, *, project: Path, output: Path | None = None, timeout: float = 120
) -> tuple[dict, Path]:
    """Certify an exact confidence interval and the coverage of its procedure."""
    return _certify_payload(
        interval_payload(interval), INTERVAL_KIND, project=project, output=output, timeout=timeout
    )


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
        _check_proof(bundle, input_id, project, timeout, logs, compile_output=True)
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
    _check_proof(bundle, input_id, project, timeout, logs, compile_output=False)
    _check_stable(project, sources, artifacts, environment, timeout, logs)
    for name, expected in files.items():
        if digest((bundle / name).read_bytes()) != expected:
            raise VerificationError("binding", "The bundle changed during replay.")
    return {
        "status": "verified",
        "certificate_id": identity,
        "backend_invoked": True,
        "kind": certificate["kind"],
        "claims": profile["claims"],
        "certificate_directory": str(bundle),
    }
