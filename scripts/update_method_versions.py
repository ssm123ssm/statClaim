"""Record each cited method's and power formula's version and hash after a reviewed change."""

import json
from pathlib import Path

from statclaim.methods import versions

PATH = Path(__file__).resolve().parents[1] / "tests/fixtures/method_versions.json"
recorded = versions()
PATH.write_text(json.dumps(recorded, indent=2) + "\n")
print(f"Recorded {len(recorded)} methods and power formulas in {PATH.name}.")
