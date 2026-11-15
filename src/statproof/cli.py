"""Run an exact Fisher test, inspect design obligations, or check development tooling."""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

from statproof import __version__
from statproof.design import inspect_design, load_design
from statproof.family import inspect_family, load_family
from statproof.report import test_design, verify_design, verify_design_only, verify_family
from statproof.verification import VerificationError, recheck_certificate


def doctor() -> int:
    print(f"StatProof {__version__}; Python {sys.version.split()[0]}")
    healthy = True
    for executable, arguments in (("uv", ["--version"]), ("lake", ["env", "lean", "--version"])):
        if not shutil.which(executable):
            print(f"MISSING: {executable}")
            healthy = False
            continue
        try:
            result = subprocess.run(
                [executable, *arguments], capture_output=True, text=True, timeout=60, check=False
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            print(f"ERROR: {executable}: {error}")
            healthy = False
            continue
        print((result.stdout + result.stderr).strip())
        healthy = healthy and result.returncode == 0
    print("Environment check only; no statistical theorem was checked in this command.")
    return 0 if healthy else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", action="version", version=__version__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("doctor", help="Check Python, uv, and the local Lean toolchain")
    inspect = commands.add_parser("inspect", help="Read a design and list unresolved obligations")
    inspect.add_argument("design", type=Path)
    test = commands.add_parser("test", help="Compute Fisher's test at the declared exact alpha")
    test.add_argument("design", type=Path)
    test.add_argument("--control-successes", type=int, required=True)
    test.add_argument("--treatment-successes", type=int, required=True)
    design_check = commands.add_parser(
        "verify-design", help="Certify the design's Type I error guarantee before supplying data"
    )
    design_check.add_argument("design", type=Path)
    design_check.add_argument("--project", type=Path, default=Path.cwd())
    design_check.add_argument(
        "--output", type=Path, help="New certificate directory (must not exist)"
    )
    design_check.add_argument("--timeout", type=float, default=120)
    verify = commands.add_parser(
        "verify", aliases=["verify-result"], help="Certify a computed result for observed counts"
    )
    verify.add_argument("design", type=Path)
    verify.add_argument("--control-successes", type=int, required=True)
    verify.add_argument("--treatment-successes", type=int, required=True)
    verify.add_argument(
        "--project", type=Path, default=Path.cwd(), help="StatProof source project root"
    )
    verify.add_argument(
        "--output", type=Path, help="New certificate bundle directory (must not exist)"
    )
    verify.add_argument("--timeout", type=float, default=120, help="Seconds per backend command")
    recheck = commands.add_parser("check-certificate", help="Check bundle integrity and rerun Lean")
    recheck.add_argument("bundle", type=Path)
    recheck.add_argument("--project", type=Path, default=Path.cwd())
    recheck.add_argument("--timeout", type=float, default=120)
    family_inspect = commands.add_parser("inspect-family", help="Inspect a two-analysis family")
    family_inspect.add_argument("family", type=Path)
    family_check = commands.add_parser(
        "verify-family", help="Certify strong familywise error control"
    )
    family_check.add_argument("family", type=Path)
    family_check.add_argument("--project", type=Path, default=Path.cwd())
    family_check.add_argument(
        "--output", type=Path, help="New certificate directory (must not exist)"
    )
    family_check.add_argument("--timeout", type=float, default=120)
    options = parser.parse_args(argv)
    if options.command == "doctor":
        return doctor()
    try:
        if options.command == "check-certificate":
            try:
                checked = recheck_certificate(
                    options.bundle,
                    project=options.project,
                    timeout=options.timeout,
                )
            except VerificationError as error:
                checked = {
                    "status": "unresolved_obligation",
                    "stage": error.stage,
                    "message": str(error),
                }
            print(json.dumps(checked, indent=2))
            return 0 if checked["status"] == "verified" else 1
        if options.command in ("inspect-family", "verify-family"):
            family = load_family(options.family)
            report = (
                inspect_family(family)
                if options.command == "inspect-family"
                else verify_family(
                    family, project=options.project, output=options.output, timeout=options.timeout
                )
            )
            print(json.dumps(report, indent=2))
            return 0 if report["status"] == "verified" else 1
        design = load_design(options.design)
        if options.command == "verify-design":
            report = verify_design_only(
                design,
                project=options.project,
                output=options.output,
                timeout=options.timeout,
            )
        elif options.command in ("verify", "verify-result"):
            report = verify_design(
                design,
                control_successes=options.control_successes,
                treatment_successes=options.treatment_successes,
                project=options.project,
                output=options.output,
                timeout=options.timeout,
            )
        elif options.command == "test":
            report = test_design(
                design,
                control_successes=options.control_successes,
                treatment_successes=options.treatment_successes,
            )
        else:
            report = inspect_design(design)
    except (OSError, ValueError) as error:
        parser.exit(2, f"statproof: {error}\n")
    print(json.dumps(report, indent=2))
    if options.command in ("verify-design", "verify", "verify-result"):
        return 0 if report["status"] == "verified" else 1
    if options.command == "test":
        # Zero signals a completed fixed-sample calculation, regardless of its
        # decision. Formal verification is a separate, explicit report field.
        return 0 if design.stopping == "fixed" else 1
    # Unresolved reports must not look like successful verification in scripts.
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
