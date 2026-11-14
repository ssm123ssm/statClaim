"""Small development CLI for inspecting declarations and checking tooling."""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

from statproof import __version__
from statproof.design import inspect_design, load_design


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
    print("Environment check only; no statistical theorem has been verified.")
    return 0 if healthy else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", action="version", version=__version__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("doctor", help="Check Python, uv, and the local Lean toolchain")
    inspect = commands.add_parser("inspect", help="Read a design and list unresolved obligations")
    inspect.add_argument("design", type=Path)
    options = parser.parse_args(argv)
    if options.command == "doctor":
        return doctor()
    try:
        report = inspect_design(load_design(options.design))
    except (OSError, ValueError) as error:
        parser.exit(2, f"statproof: {error}\n")
    print(json.dumps(report, indent=2))
    # Unresolved reports must not look like successful verification in scripts.
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
