# Cited methods

Some guarantees are not proved in Lean. For these methods StatClaim checks that
your study fits the method's contract, then restates the published guarantee with
its assumptions and references. The result has status `cited`, never `verified`.

```stat
use models.two_arm_continuous
use sampling
use tests.t

let study = two_arm_continuous(n_control=60, n_treatment=60)
let plan = fixed(model=study)
let null = equal_means(model=study)
let analysis = t_test(design=plan, null=null, alpha=1/20)
let checked = verify(typeI(analysis))
```

No Lean installation is needed to check this file. See `examples/t_test.stat`.

## What is checked

- The null fits the test: `equal_means` for a two-sided test,
  `mean_difference_at_most` for a one-sided or non-inferiority test.
- The null and the design are declared over the same model.
- The design is `fixed`. With `adaptive`, the claim stays unresolved.
- There are enough participants to estimate the variance.

## What is not checked

The guarantee itself, and most of its assumptions. The report names each
assumption and marks it:

- `declared`: your file states it. `fixed` says the sizes are set in advance.
- `assumed`: nothing in the file can show it, such as normal outcomes.

Read them with `checked.evidence.required_assumptions` and
`checked.evidence.references`. The JSON report also gives each assumption's id
and kind, and the method's version.

The claim's guarantee is a structured value, not only a sentence:

```stat
let bound = checked.claim.guarantee.bound        # 1/20
let relation = checked.claim.guarantee.relation  # equals or at_most
let scope = checked.claim.scope                  # finite_sample or asymptotic
```

## Supported tests

| Test | Null | Guarantee | Assumes |
| --- | --- | --- | --- |
| `t_test` | `equal_means` | Exact level | Normal outcomes, equal variances |
| `t_test_one_sided` | `mean_difference_at_most` | Level at most alpha | Normal outcomes, equal variances |
| `welch_test` | `equal_means` | Large-sample approximation | Finite variances |
| `welch_test_one_sided` | `mean_difference_at_most` | Large-sample approximation | Finite variances |

All assume independent observations, fixed arm sizes and one analysis.
`claim.guarantee` is `finite_sample` for the pooled tests and `asymptotic` for
Welch. A file with any cited claim has overall status `cited`.

Cited tests cannot yet join a Bonferroni family or a planning search.

## Adding a cited method

You need to read three short files, all in `src/statclaim/methods/`:

- `core.py`: what an assumption, a guarantee and a method are.
- `assumptions.py`: the shared assumptions. Reuse one before adding one.
- `t_tests.py`: a complete example to copy.

To add a test over an existing model and null:

1. Write a method file that exports `MODULE`, or add a `CitedMethod` to an
   existing file. State the null it supports, whether the error rate `equals`
   alpha or is `at_most` alpha, the scope, the assumptions and the references.
2. List a new file in `methods/__init__.py`.
3. Run `uv run python scripts/update_method_versions.py` and
   `uv run python scripts/update_catalogue.py`.
4. Add an example, and a test for a null the method must reject.

The constructor, editor support, catalogue entry and report follow from the
entry. A method over a new kind of outcome also needs a model and nulls in
`language.py`; open an issue first.

Each entry is trusted, not proved, so it needs a published source and statistical
review. After a reviewed change to an entry, raise its `version`. A test fails
until you do, because evidence records the version it relied on.
