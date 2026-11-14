.PHONY: setup check python-check lean-check demo

setup:
	uv sync --locked
	MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
	lake exe cache get Mathlib.Tactic.NormNum
	lake build

check: python-check lean-check

python-check:
	uv run --locked ruff check .
	uv run --locked ruff format --check .
	uv run --locked pytest

lean-check:
	lake build
	uv run --locked python scripts/check_lean_sources.py

demo:
	uv run --locked statproof inspect examples/fixed_sample.toml
