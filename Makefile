.PHONY: setup check python-check lean-check integration-check reference-check demo verify-demo

setup:
	uv sync --locked
	MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
	lake exe cache get \
		Mathlib.Tactic.NormNum \
		Mathlib.Data.Finset.Max \
		Mathlib.Algebra.Order.BigOperators.Group.Finset \
		Mathlib.Algebra.BigOperators.Field \
		Mathlib.Data.Nat.Choose.Vandermonde \
		Mathlib.Basic.Real.Basic \
		Mathlib.Data.Nat.Choose.Sum \
		Mathlib.Tactic.FieldSimp \
		Mathlib.Tactic.Ring \
		Mathlib.Probability.Distributions.Binomial \
		Mathlib.MeasureTheory.Measure.Prod
	lake build

check: python-check lean-check integration-check

python-check:
	uv run --locked ruff check .
	uv run --locked ruff format --check .
	uv run --locked pytest -m 'not lean'

lean-check:
	lake build
	uv run --locked python scripts/check_lean_sources.py
	lake env lean scripts/audit_axioms.lean
	lake env lean tests/lean/FisherExamples.lean

integration-check:
	uv run --locked pytest -m lean

reference-check:
	uv run --locked python scripts/compare_with_r.py

demo:
	uv run --locked statproof test examples/fixed_sample.toml --control-successes 10 --treatment-successes 25

verify-demo:
	uv run --locked statproof verify examples/fixed_sample.toml --control-successes 10 --treatment-successes 25
