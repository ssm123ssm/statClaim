"""Generate or validate the public catalogue."""

import argparse
from pathlib import Path

from statclaim.catalogue import render_catalogue

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--check", action="store_true")
args = parser.parse_args()
path = Path(__file__).resolve().parents[1] / "docs/catalogue.md"
expected = render_catalogue()
if args.check:
    if not path.exists() or path.read_text() != expected:
        parser.exit(1, "Catalogue is stale: run uv run python scripts/update_catalogue.py\n")
else:
    path.write_text(expected)
