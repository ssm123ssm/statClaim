"""Run an exact Fisher test, inspect design obligations, or check development tooling."""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

from statclaim import __version__
from statclaim.design import inspect_design, load_design
from statclaim.family import inspect_family, load_family
from statclaim.language import module_catalog
from statclaim.language_runner import check_source, render_report
from statclaim.language_syntax import Source
from statclaim.report import test_design, verify_design, verify_design_only, verify_family
from statclaim.verification import VerificationError, recheck_certificate

# The files that mark a StatClaim checkout, where the Lean backend lives.
CHECKOUT_FILES = ("lean-toolchain", "lakefile.toml", "StatClaim.lean")
SETUP = (
    "Proved and conditional claims need Lean, which lives in a StatClaim checkout: "
    "'git clone https://github.com/ssm123ssm/statClaim', run 'make setup' in it, then run "
    "statclaim there or pass --project. See docs/quickstart.md."
)


def doctor(project: Path) -> int:
    """Report what this installation can do. Lean is needed only for proofs.

    Lean is checked only inside a checkout: elsewhere, running lake could start a
    toolchain download.
    """
    print(f"StatClaim {__version__}; Python {sys.version.split()[0]}")
    print("Ready without Lean: compile, explain, report, impact, and cited claims.")
    uv = shutil.which("uv")
    if uv:
        result = subprocess.run([uv, "--version"], capture_output=True, text=True, check=False)
        print((result.stdout + result.stderr).strip())
    else:
        print("uv: not found. It is needed only to work in a checkout.")
    project = project.resolve()
    if not all((project / name).is_file() for name in CHECKOUT_FILES):
        print(f"Lean: not checked. {project} is not a StatClaim checkout.")
        healthy = False
    elif not shutil.which("lake"):
        print("Lean: MISSING. 'lake' is not on PATH; install elan, then run 'make setup'.")
        healthy = False
    else:
        try:
            result = subprocess.run(
                ["lake", "env", "lean", "--version"],
                cwd=project,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                timeout=60,
                check=False,
            )
            print((result.stdout + result.stderr).strip())
            healthy = result.returncode == 0
        except (OSError, subprocess.TimeoutExpired):
            print(
                "Lean: 'lake env lean --version' did not finish in 60 seconds. Run "
                f"'make setup' in {project} first; it downloads the pinned Lean and Mathlib."
            )
            healthy = False
    if not healthy:
        print(SETUP)
    print("Environment check only; no statistical theorem was checked in this command.")
    return 0 if healthy else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Check, explain and verify statistical study files (.stat).",
        epilog="Commands for the older TOML design files remain available and are not "
        "listed: inspect, test, verify-design, verify, inspect-family, verify-family. "
        "See docs/certificates.md.",
    )
    parser.add_argument("--version", action="version", version=__version__)
    # Legacy TOML commands are registered without help text, which keeps them
    # working while leaving them out of the command list.
    commands = parser.add_subparsers(dest="command", required=True, metavar="COMMAND")
    doctor_command = commands.add_parser(
        "doctor", help="Check Python, uv, and the Lean toolchain of a checkout"
    )
    doctor_command.add_argument(
        "--project", type=Path, default=Path.cwd(), help="StatClaim checkout to check for Lean"
    )
    commands.add_parser("lsp", help="Start the stdio language server (no proof execution)")
    inspect = commands.add_parser("inspect")
    inspect.add_argument("design", type=Path)
    test = commands.add_parser("test")
    test.add_argument("design", type=Path)
    test.add_argument("--control-successes", type=int, required=True)
    test.add_argument("--treatment-successes", type=int, required=True)
    design_check = commands.add_parser("verify-design")
    design_check.add_argument("design", type=Path)
    design_check.add_argument("--project", type=Path, default=Path.cwd())
    design_check.add_argument(
        "--output", type=Path, help="New certificate directory (must not exist)"
    )
    design_check.add_argument("--timeout", type=float, default=120)
    verify = commands.add_parser("verify", aliases=["verify-result"])
    verify.add_argument("design", type=Path)
    verify.add_argument("--control-successes", type=int, required=True)
    verify.add_argument("--treatment-successes", type=int, required=True)
    verify.add_argument(
        "--project", type=Path, default=Path.cwd(), help="StatClaim source project root"
    )
    verify.add_argument(
        "--output", type=Path, help="New certificate bundle directory (must not exist)"
    )
    verify.add_argument("--timeout", type=float, default=120, help="Seconds per backend command")
    recheck = commands.add_parser("check-certificate", help="Check bundle integrity and rerun Lean")
    recheck.add_argument("bundle", type=Path)
    recheck.add_argument("--project", type=Path, default=Path.cwd())
    recheck.add_argument("--timeout", type=float, default=120)
    family_inspect = commands.add_parser("inspect-family")
    family_inspect.add_argument("family", type=Path)
    family_check = commands.add_parser("verify-family")
    family_check.add_argument("family", type=Path)
    family_check.add_argument("--project", type=Path, default=Path.cwd())
    family_check.add_argument(
        "--output", type=Path, help="New certificate directory (must not exist)"
    )
    family_check.add_argument("--timeout", type=float, default=120)
    check = commands.add_parser("check", help="Check and execute a statistical .stat file")
    check.add_argument("source", type=Path)
    check.add_argument("--project", type=Path, default=Path.cwd())
    check.add_argument(
        "--output", type=Path, help="New directory for source, report, and certificates"
    )
    check.add_argument("--timeout", type=float, default=120)
    check.add_argument(
        "--elaborate-only",
        action="store_true",
        help="Compile and inspect requirements without calculations, Lean, or artifact writes",
    )
    check.add_argument("--json", action="store_true", help="Emit the structured report")
    compile_command = commands.add_parser(
        "compile", help="Compile a .stat plan and inspect requirements without executing it"
    )
    compile_command.add_argument("source", type=Path)
    compile_command.add_argument(
        "--json", action="store_true", help="Emit the typed plan and report"
    )
    explain_command = commands.add_parser(
        "explain", help="Explain why the contracts in a .stat file passed"
    )
    explain_command.add_argument("source", type=Path)
    explain_command.add_argument("--name", help="Only the contract of this declaration")
    explain_command.add_argument("--json", action="store_true")
    report_command = commands.add_parser(
        "report", help="Write a study-level report of contracts, assumptions and obligations"
    )
    report_command.add_argument("source", type=Path)
    report_command.add_argument("--output", type=Path, help="Write the report to this file")
    report_command.add_argument("--json", action="store_true")
    report_command.add_argument(
        "--lean",
        action="store_true",
        help="Also build and audit the program's compatibility certificate in Lean",
    )
    report_command.add_argument(
        "--project", type=Path, default=Path.cwd(), help="StatClaim checkout for --lean"
    )
    report_command.add_argument(
        "--certificate", type=Path, help="New directory for the --lean certificate"
    )
    report_command.add_argument("--timeout", type=float, default=600)
    impact_command = commands.add_parser(
        "impact", help="List the contracts and claims affected by a change between two files"
    )
    impact_command.add_argument("before", type=Path)
    impact_command.add_argument("after", type=Path)
    impact_command.add_argument("--json", action="store_true")
    modules = commands.add_parser(
        "modules", help="List file-language modules and typed constructors"
    )
    modules.add_argument("--json", action="store_true")
    inventory = commands.add_parser(
        "catalogue", aliases=["catalog"], help="List classified public objects, modules and fields"
    )
    inventory.add_argument("--json", action="store_true")
    options = parser.parse_args(argv)
    if options.command == "lsp":
        from statclaim.lsp import run_stdio

        return run_stdio()
    if options.command == "doctor":
        return doctor(options.project)
    try:
        if options.command in ("catalogue", "catalog"):
            from statclaim.catalogue import catalogue, render_catalogue

            print(json.dumps(catalogue(), indent=2) if options.json else render_catalogue())
            return 0
        if options.command == "modules":
            catalog = module_catalog()
            print(
                json.dumps(catalog, indent=2)
                if options.json
                else "\n".join(
                    f"use {module['module']}\n  " + "\n  ".join(module["constructors"])
                    for module in catalog
                )
            )
            return 0
        if options.command in ("explain", "report", "impact"):
            from statclaim.contract_reports import (
                explain,
                explanation_markdown,
                impact,
                impact_markdown,
                report_markdown,
                study_report,
            )
            from statclaim.language_compiler import compile_source

            def compiled(path: Path):
                return compile_source(Source(path.read_bytes().decode("utf-8"), str(path)))

            if options.command == "impact":
                result = impact(compiled(options.before), compiled(options.after))
                print(json.dumps(result, indent=2) if options.json else impact_markdown(result))
                return 0
            compilation = compiled(options.source)
            if options.command == "explain":
                entries = explain(compilation, options.name)
                if options.json:
                    print(json.dumps(entries, indent=2))
                elif entries:
                    print("\n\n".join(explanation_markdown(entry) for entry in entries))
                else:
                    print("No validated contract to explain.")
                return 0 if entries and all(entry["checked"] for entry in entries) else 1
            report = study_report(compilation, str(options.source))
            if options.lean:
                from statclaim.lean_report import lean_check

                source = Source(options.source.read_bytes().decode("utf-8"), str(options.source))
                report["lean"] = lean_check(
                    source,
                    project=options.project,
                    output=options.certificate,
                    timeout=options.timeout,
                )
            text = json.dumps(report, indent=2) if options.json else report_markdown(report)
            if options.output:
                options.output.write_text(text if text.endswith("\n") else text + "\n")
                print(f"Report written to {options.output}")
            else:
                print(text)
            if report["status"] == "invalid":
                return 2
            return 1 if report.get("lean", {}).get("status") in ("failed", "unavailable") else 0
        if options.command in ("check", "compile"):
            source = Source(
                options.source.read_bytes().decode("utf-8"), str(options.source.resolve())
            )
            report = check_source(
                source,
                project=getattr(options, "project", Path.cwd()),
                output=getattr(options, "output", None),
                timeout=getattr(options, "timeout", 120),
                elaborate_only=options.command == "compile" or options.elaborate_only,
            )
            print(json.dumps(report, indent=2) if options.json else render_report(report, source))
            return (
                2
                if report["status"] == "invalid"
                else 1
                if report["status"] in ("unresolved_obligation", "stale_source")
                else 0
            )
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
        parser.exit(2, f"statclaim: {error}\n")
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
