"""Build the web studio: the studio's page, StatClaim from this commit, and Pyodide.

uv run python scripts/build_studio_site.py [--out dist/studio-site] [--reference FILE]

Needs `npm ci --prefix studio`, which installs the pinned Pyodide. The page files are the ones
studio/server.py serves (api.ASSETS); the answers that never change, such as the block
manifest and the lessons, are written by api.handle, as the server would give them; the rest
is answered in the browser by the same api.py. --reference also writes what CPython answers
for every example, which studio/tests/site.check.mjs compares with what Pyodide answers.
"""

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STUDIO = ROOT / "studio"
sys.path.insert(0, str(STUDIO))

import api  # noqa: E402

PYODIDE = STUDIO / "node_modules/pyodide"
PYODIDE_FILES = (
    "pyodide.mjs",
    "pyodide.asm.js",
    "pyodide.asm.wasm",
    "python_stdlib.zip",
    "pyodide-lock.json",
)
BROWSER_META = '<meta name="statclaim-backend" content="browser">'


def build(out: Path) -> None:
    if not all((PYODIDE / name).is_file() for name in PYODIDE_FILES):
        raise SystemExit("Pyodide is missing; run npm ci --prefix studio first.")
    shutil.rmtree(out, ignore_errors=True)
    out.mkdir(parents=True)
    for asset in sorted(api.ASSETS):
        shutil.copyfile(STUDIO / asset, out / asset)
    page = (out / "index.html").read_text(encoding="utf-8")
    marker = '<meta charset="utf-8">'
    if marker not in page:
        raise SystemExit("index.html has no charset meta to place the backend after.")
    (out / "index.html").write_text(page.replace(marker, marker + "\n  " + BROWSER_META, 1))

    python = out / "python"
    python.mkdir()
    with tempfile.TemporaryDirectory() as scratch:
        subprocess.run(
            ["uv", "build", "--wheel", "--out-dir", scratch, str(ROOT)],
            check=True,
            capture_output=True,
        )
        (wheel,) = Path(scratch).glob("statclaim-*.whl")
        shutil.copyfile(wheel, python / wheel.name)
    shutil.copyfile(STUDIO / "api.py", python / "api.py")
    (python / "manifest.json").write_text(json.dumps({"wheel": wheel.name}))

    (out / "pyodide").mkdir()
    for name in PYODIDE_FILES:
        shutil.copyfile(PYODIDE / name, out / "pyodide" / name)
    version = json.loads((PYODIDE / "package.json").read_text())["version"]
    (out / "pyodide" / "NOTICE.txt").write_text(
        f"Pyodide {version}, https://pyodide.org, under the Mozilla Public License 2.0.\n"
        "It includes CPython, under the Python Software Foundation License.\n"
    )

    answers = out / "api"
    answers.mkdir()
    for name in api.GETS:
        status, body = api.handle("GET", name, None, api.BROWSER)
        if status != 200:
            raise SystemExit(f"GET {name} answered {status}.")
        (answers / f"{name}.json").write_text(json.dumps(body))


def reference(path: Path) -> None:
    """What CPython answers in the web studio's place, for every example, lesson and case."""
    found = {}
    studies = [*(ROOT / "examples").rglob("*.stat"), *(ROOT / "replication").glob("*/*.stat")]
    for study in sorted(studies):
        payload = {"source": study.read_text(encoding="utf-8"), "name": study.name}
        found[str(study.relative_to(ROOT))] = {
            **payload,
            **{name: api.handle("POST", name, payload, api.BROWSER) for name in ("compile", "run")},
        }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(found))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--out", type=Path, default=ROOT / "dist/studio-site")
    parser.add_argument("--reference", type=Path)
    args = parser.parse_args()
    build(args.out)
    if args.reference:
        reference(args.reference)
    print(f"Built the web studio in {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
