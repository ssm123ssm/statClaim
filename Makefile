.PHONY: setup check python-check lean-check reference-check demo

setup:
	uv sync --locked
	MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
	lake exe cache get Mathlib.Tactic.NormNum Mathlib.Data.Finset.Max Mathlib.Algebra.Order.BigOperators.Group.Finset
	lake build

check: python-check lean-check

python-check:
	uv run --locked ruff check .
	uv run --locked ruff format --check .
	uv run --locked pytest

lean-check:
	lake build
	uv run --locked python scripts/check_lean_sources.py
	lake env lean scripts/audit_axioms.lean

reference-check:
	uv run --locked python scripts/compare_with_r.py

demo:
	uv run --locked statproof test examples/fixed_sample.toml --control-successes 10 --treatment-successes 25
