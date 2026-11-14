"""Reject proof placeholders in project Lean sources (not a complete axiom audit)."""

import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
paths = [
    root / "StatProof.lean",
    *sorted((root / "StatProof").rglob("*.lean")),
    *sorted((root / "tests/lean").rglob("*.lean")),
    *sorted((root / "examples").rglob("*.lean")),
]
bad = [
    str(path.relative_to(root))
    for path in paths
    if re.search(r"\b(sorry|admit|axiom)\b", path.read_text())
]
if bad:
    raise SystemExit(f"Proof placeholders or extra axioms found: {', '.join(bad)}")
print("Project Lean sources contain no sorry/admit/axiom tokens.")
