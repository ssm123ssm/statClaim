"""Record each cited method's version and content hash after a reviewed change."""

import json
from pathlib import Path

from statclaim.methods import METHODS
from statclaim.verification import digest

PATH = Path(__file__).resolve().parents[1] / "tests/fixtures/method_versions.json"
PATH.write_text(
    json.dumps(
        {
            key: {"version": method.version, "sha256": digest(repr(method).encode())}
            for key, method in METHODS.items()
        },
        indent=2,
    )
    + "\n"
)
print(f"Recorded {len(METHODS)} methods in {PATH.name}.")
