"""Install a built wheel into a fresh virtual environment and use it without Lean.

uv run python scripts/check_install.py dist/statclaim-*.whl [--python 3.13]

Everything happens in a temporary folder outside the repository: the wheel is
installed with uv, a few examples are copied out, and the installed command is
run on them as a new user would. Needs uv; does not need Lean.
"""

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
# Each example and the file status it reaches without Lean.
EXAMPLES = {
    "t_test": "cited",
    "log_rank": "cited",
    "cited_power": "calculated",
    # These verify a combination in Lean, so without a checkout the claim stays open.
    "trial_models": "unresolved_obligation",
    "declared_test": "unresolved_obligation",
}


def run(command: list, cwd: Path, **options) -> subprocess.CompletedProcess:
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True, **options)


def frame(message: dict) -> bytes:
    body = json.dumps(message).encode()
    return b"Content-Length: %d\r\n\r\n" % len(body) + body


def language_server(statclaim: Path, cwd: Path) -> list[str]:
    messages = [
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}},
        {"jsonrpc": "2.0", "method": "initialized", "params": {}},
        {"jsonrpc": "2.0", "id": 2, "method": "shutdown", "params": None},
        {"jsonrpc": "2.0", "method": "exit", "params": None},
    ]
    process = subprocess.run(
        [str(statclaim), "lsp"],
        input=b"".join(frame(m) for m in messages),
        capture_output=True,
        cwd=cwd,
        timeout=60,
    )
    replies, out = {}, process.stdout
    while out:
        header, _, rest = out.partition(b"\r\n\r\n")
        length = int(header.split(b":")[1])
        reply = json.loads(rest[:length])
        replies[reply.get("id")] = reply
        out = rest[length:]
    problems = []
    if process.returncode != 0:
        problems.append(f"lsp exited with {process.returncode}")
    capabilities = replies.get(1, {}).get("result", {}).get("capabilities", {})
    if "hoverProvider" not in capabilities or replies.get(2, {}).get("result", 0) is not None:
        problems.append("lsp did not answer initialize and shutdown")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("wheel", type=Path)
    parser.add_argument("--python", default=f"{sys.version_info.major}.{sys.version_info.minor}")
    options = parser.parse_args()
    wheel = options.wheel.resolve()
    problems = []
    with tempfile.TemporaryDirectory() as directory:
        base = Path(directory)
        venv, work = base / "venv", base / "work"
        work.mkdir()
        for command in (
            ["uv", "venv", "--quiet", "--python", options.python, str(venv)],
            ["uv", "pip", "install", "--quiet", "--python", str(venv), str(wheel)],
        ):
            result = run(command, base)
            if result.returncode:
                print(result.stdout + result.stderr)
                return 1
        binary = "Scripts" if sys.platform == "win32" else "bin"
        statclaim = venv / binary / "statclaim"
        version = run([str(statclaim), "--version"], work)
        print(f"statclaim --version: {version.stdout.strip()} (Python {options.python})")
        doctor = run([str(statclaim), "doctor"], work, timeout=120)
        print(doctor.stdout.strip())
        if doctor.returncode != 1 or "not a StatClaim checkout" not in doctor.stdout:
            problems.append("doctor did not report a missing Lean checkout with exit code 1")
        for name, expected in EXAMPLES.items():
            shutil.copy(ROOT / "examples" / f"{name}.stat", work)
            check = run([str(statclaim), "check", f"{name}.stat"], work, timeout=300)
            status = next(
                (
                    line.split(": ", 1)[1]
                    for line in check.stdout.splitlines()
                    if line.startswith("Program status: ")
                ),
                None,
            )
            report = run([str(statclaim), "report", f"{name}.stat"], work, timeout=300)
            ok = status == expected and report.stdout.startswith("# Study contract report")
            label = "ok" if ok else "FAILED"
            print(f"{label}: {name}.stat: check {status}; report {report.returncode}")
            if not ok:
                problems.append(f"{name}.stat: {check.stdout[-400:]}{check.stderr[-400:]}")
                problems.append(report.stderr[-400:])
        server = language_server(statclaim, work)
        print("ok: statclaim lsp answers initialize" if not server else "FAILED: statclaim lsp")
        problems += server
    if problems:
        print("\n".join(["Problems:", *problems]))
        return 1
    print("The wheel works without Lean.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
