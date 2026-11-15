"""Collect bundled runtime dependency licenses for the VSIX."""

import json
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1] / "extensions/vscode"
production = subprocess.check_output(
    ["npm", "ls", "--omit=dev", "--all", "--parseable"], cwd=root, text=True
).splitlines()
sections = []
for location in sorted(production[1:]):
    directory = Path(location)
    metadata = json.loads((directory / "package.json").read_text())
    licenses = [
        p
        for p in directory.iterdir()
        if p.name.lower().startswith(("license", "licence", "copying")) and p.is_file()
    ]
    if not licenses:
        raise SystemExit(f"Missing dependency license: {directory.name}")
    sections.append(
        metadata["name"]
        + " "
        + metadata["version"]
        + "\n"
        + "\n".join(p.read_text() for p in licenses)
    )
(root / "ThirdPartyNotices.txt").write_text("\n\n".join(sections).rstrip() + "\n")
