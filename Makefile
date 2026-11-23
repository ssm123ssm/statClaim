.PHONY: setup check python-check lean-check integration-check reference-check demo verify-demo objects-demo design-demo design-objects-demo alpha-demo family-demo composition-demo language-demo language-family-demo language-result-demo editor-check

setup:
	uv sync --locked
	MATHLIB_NO_CACHE_ON_UPDATE=1 lake env lean --version
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
		Mathlib.MeasureTheory.Measure.Prod \
		Mathlib.Probability.Distributions.Uniform
	lake build

check: python-check lean-check integration-check

# Lint the files git tracks, so local scratch folders never fail the check.
PYTHON_FILES = $$(git ls-files '*.py')

python-check: type-check
	uv run --locked ruff check $(PYTHON_FILES)
	uv run --locked ruff format --check $(PYTHON_FILES)
	uv run --locked python scripts/tutorial.py check
	uv run --locked pytest -m 'not lean'

# The web studio, built from this commit into dist/studio-site. site-check also runs every
# example in its Pyodide and compares the answers with CPython's.
.PHONY: site site-check
site:
	npm --prefix studio ci
	uv run --locked python scripts/build_studio_site.py

site-check:
	npm --prefix studio ci
	uv run --locked python scripts/build_studio_site.py --reference dist/studio-reference.json
	node studio/tests/site.check.mjs dist/studio-site dist/studio-reference.json

# The studio's page tests; its server tests run with the other Python tests.
.PHONY: studio-check
studio-check:
	npm --prefix studio ci
	npm --prefix studio test

# Gradual: pyproject.toml lists the modules mypy does not check yet.
.PHONY: type-check
type-check:
	uv run --locked mypy

lean-check:
	lake build
	uv run --locked python scripts/check_lean_sources.py
	lake env lean scripts/audit_axioms.lean
	lake env lean tests/lean/FisherExamples.lean
	lake env lean tests/lean/CoreObjects.lean
	lake env lean tests/lean/Composition.lean
	lake env lean tests/lean/Policies.lean
	lake env lean tests/lean/Interface.lean
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

# CI runs the Lean integration tests in three shards at once. The last shard takes every
# file the first two do not name, so a new integration file is never left out.
SHARD_A = tests/test_association_integration.py
SHARD_B = tests/test_verification_integration.py tests/test_randomisation_integration.py \
	tests/test_design_verification_integration.py
.PHONY: integration-shard
integration-shard:
ifeq ($(SHARD),a)
	uv run --locked pytest -m lean $(SHARD_A)
else ifeq ($(SHARD),b)
	uv run --locked pytest -m lean $(SHARD_B)
else
	uv run --locked pytest -m lean $(foreach file,$(SHARD_A) $(SHARD_B),--ignore=$(file))
endif

# Rerun the lessons that need no Lean and check the outputs the tutorial shows.
.PHONY: tutorial-check
tutorial-check:
	uv run --locked python scripts/tutorial.py outputs

reference-check:
	uv run --locked python scripts/compare_with_r.py

demo:
	uv run --locked statclaim test examples/fixed_sample.toml --control-successes 10 --treatment-successes 25

verify-demo:
	uv run --locked statclaim verify examples/fixed_sample.toml --control-successes 10 --treatment-successes 25

design-demo:
	uv run --locked statclaim verify-design examples/fixed_sample.toml

alpha-demo:
	uv run --locked statclaim verify-design examples/fixed_sample_alpha.toml

family-demo:
	uv run --locked statclaim verify-family examples/two_outcomes.toml

composition-demo:
	lake build
	lake env lean examples/MultipleTesting.lean

language-demo:
	uv run --locked statclaim check examples/fisher.stat

language-family-demo:
	uv run --locked statclaim check examples/two_outcomes.stat

language-result-demo:
	uv run --locked statclaim check examples/fisher_result.stat

editor-check:
	npm --prefix extensions/vscode run check
	npm --prefix extensions/vscode run test:unit
	npm --prefix extensions/vscode test

.PHONY: replicate replicate-lean replicate-update
replicate:
	uv run --locked python replication/run.py

replicate-lean:
	uv run --locked python replication/run.py --lean

replicate-update:
	uv run --locked python replication/run.py --update

.PHONY: install-check
install-check:
	rm -rf dist/install-check
	uv build --wheel --out-dir dist/install-check
	uv run --locked python scripts/check_install.py dist/install-check/statclaim-*.whl

.PHONY: catalogue-check repository-check editor-package
catalogue-check:
	uv run --locked python scripts/update_catalogue.py --check

repository-check:
	uv run --locked python scripts/check_repository.py

editor-package:
	npm --prefix extensions/vscode ci --ignore-scripts
	uv run --locked python scripts/extension_notices.py
	mkdir -p extensions/vscode/dist
	npm --prefix extensions/vscode run package
