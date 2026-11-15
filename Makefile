.PHONY: setup check python-check lean-check integration-check reference-check demo verify-demo objects-demo design-demo design-objects-demo alpha-demo family-demo composition-demo language-demo language-family-demo language-result-demo

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
	lake env lean tests/lean/CoreObjects.lean
	lake env lean tests/lean/Composition.lean
	lake env lean examples/FisherObjects.lean
	lake env lean examples/DesignGuarantee.lean
	lake env lean examples/ConfigurableAlpha.lean
	lake env lean examples/MultipleTesting.lean

objects-demo:
	lake build
	lake env lean examples/FisherObjects.lean

design-objects-demo:
	lake build
	lake env lean examples/DesignGuarantee.lean

integration-check:
	uv run --locked pytest -m lean

reference-check:
	uv run --locked python scripts/compare_with_r.py

demo:
	uv run --locked statproof test examples/fixed_sample.toml --control-successes 10 --treatment-successes 25

verify-demo:
	uv run --locked statproof verify examples/fixed_sample.toml --control-successes 10 --treatment-successes 25

design-demo:
	uv run --locked statproof verify-design examples/fixed_sample.toml

alpha-demo:
	uv run --locked statproof verify-design examples/fixed_sample_alpha.toml

family-demo:
	uv run --locked statproof verify-family examples/two_outcomes.toml

composition-demo:
	lake build
	lake env lean examples/MultipleTesting.lean

language-demo:
	uv run --locked statproof check examples/fisher.stat

language-family-demo:
	uv run --locked statproof check examples/two_outcomes.stat

language-result-demo:
	uv run --locked statproof check examples/fisher_result.stat
